import Lean
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

example : ¬ ∃ (x y : ℤ), x^2 + y^2 = 3 := by
  -- 1. Assume for contradiction a solution ⟨x, y⟩ exists.
  --    `h` is the proof `x^2 + y^2 = 3`.
  rintro ⟨x, y, h⟩

  -- 2. We choose n = 4.
  --    Apply the function `(Int.cast : ℤ → ZMod 4)` to both sides of the equality `h`.
  have h_mod_4 := congr_arg (Int.cast : ℤ → ZMod 4) h

  -- 3. Simplify the new hypothesis.
  --    `push_cast` will use ring homomorphism lemmas like `Int.cast_add`
  --    and `Int.cast_pow` to simplify the expression.
  --    It turns `↑(x ^ 2 + y ^ 2)` into `(↑x) ^ 2 + (↑y) ^ 2`
  --    and `↑3` into `(3 : ZMod 4)`.
  push_cast at h_mod_4

  -- Our proof state now contains:
  -- h_mod_4 : (x : ZMod 4) ^ 2 + (y : ZMod 4) ^ 2 = (3 : ZMod 4)

  -- 4. Get the contradiction. We state that for *all* elements
  --    `a, b` of `ZMod 4`, `a^2 + b^2 ≠ 3`.
  have h_contra : ∀ (a b : ZMod 4), a^2 + b^2 ≠ 3 := by
    -- The `decide` tactic automatically checks all 4*4 = 16 cases.
    decide

  -- 5. Apply this general fact to our specific `x` and `y`.
  --    `h_contra (x : ZMod 4) (y : ZMod 4)` is the proof
  --    `(x : ZMod 4)^2 + (y : ZMod 4)^2 ≠ 3`.
  --    This is a direct contradiction of `h_mod_4`.
  exact h_contra (x : ZMod 4) (y : ZMod 4) h_mod_4

/-!
# `no_sols_mod_n` Tactic

This file defines a tactic `no_sols_mod_n n` to automate
proofs of "no integer solutions" by reduction modulo `n`.

## Workflow
1. Begin your proof: `example : ¬ ∃ (x y : ℤ), ... := by`
2. Introduce the variables: `  rintro ⟨x, y, h⟩`
3. Call the tactic: `  no_sols_mod_n 4`

## How it Works
The tactic performs the following metaprogramming steps:
1. Finds the local `ℤ` variables (e.g., `x`, `y`).
2. Finds the last equality hypothesis (e.g., `h`).
3. Casts `h` to `ZMod n` to create a new hypothesis `h_mod_n`.
4. Simplifies `h_mod_n` with `push_cast`.
5. Creates new local variables for each `(x : ZMod n)`, e.g., `x_mod`.
6. Rewrites `h_mod_n` in terms of these new variables.
7. `revert`s all the new `_mod` variables and `h_mod_n`.
   This changes the goal from `⊢ False` to
   `⊢ ∀ (x_mod y_mod : ZMod n), x_mod^2 + ... = ... → False`
8. Calls `decide` to solve this new (finite) goal.
-/

open Lean Meta Elab Tactic

-- This helper function checks if an FVarId has type `ℤ`
def isIntFVar (fvarId : FVarId) : TacticM Bool := do
  let type ← inferType (mkFVar fvarId)
  return type.isConstOf ``Int

-- 1. Define the syntax
syntax (name := noSolsModN) "no_sols_mod_n " num : tactic

-- 2. Define the tactic implementation
@[tactic noSolsModN]
def elabNoSolsModN : Tactic := fun stx =>
-- Parse the modulus `n` from the syntax
match stx with
  | `(tactic| no_sols_mod_n $n_stx) =>
    withMainContext do

      -- 0. Call rintro to automatically deconstruct the goal
      -- try
      --   evalTactic (← `(tactic| rintro h; rcases h with ⟨⟩))
      -- catch e =>
      --   throwError "Tactic failed: Goal must be of the form
      --     `¬ ∃ (x y ... : ℤ), ...`. {e.toMessageData}"

      -- 1. Find the equality hypothesis `h`.
      -- We'll just find the last declaration in the context that is an equality.
      let h_decl? ← (← getLCtx).findDeclRevM? (fun d => do
        if d.isLet then
          return none
        let type ← inferType d.toExpr
        match type.eq? with
        | some (α, _lhs, _rhs) =>
          if α.isConstOf ``Int then
            return some d -- Found it, return `some` of the declaration
          else
            return none -- is an equality but not of Ints, return `none`
        | none => return none -- not an equality, ignore it
      )
      let .some h_decl := h_decl? |
        throwError "Could not find an equality hypothesis. Use `rintro ⟨..., h⟩` first."
      let h_ident := mkIdent h_decl.userName

      -- 2. Find all `ℤ` variables
      let all_fvars := (← getLCtx).getFVarIds
      let int_fvars ← all_fvars.filterM isIntFVar
      if int_fvars.isEmpty then
        throwError "Could not find any `ℤ` variables in the context."

      -- 3. Create the `ZMod n` type syntax
      let zmod_n_stx ← `(ZMod $n_stx)

      -- 4. Cast `h` to `ZMod n`
      let h_mod_ident := mkIdent `h_mod_n
      evalTactic (← `(tactic|
        have $h_mod_ident := congr_arg (Int.cast : ℤ → $zmod_n_stx) $h_ident
      ))

      -- Create a location array for `h_mod_ident` (`h_mod_n`)
      let h_mod_loc : Array (TSyntax `ident) := #[h_mod_ident]

      -- 5. `push_cast` at `h_mod_n`
      --    Use the array splice syntax `$h_mod_loc*`
      evalTactic (← `(tactic| push_cast at $h_mod_loc*))

      -- 6. For each `ℤ` var `x`, generalize `(↑x : ZMod n)` to a new var `x_mod`
      --    This is the new strategy to avoid `let`-bindings.
      let mut mod_fvars_to_revert : Array FVarId := #[]
      let mut eq_hyps_to_clear : Array (TSyntax `ident) := #[]

      for fvar in int_fvars do
        let x_ident := mkIdent (← fvar.getUserName)
        let x_mod_ident := mkIdent <| (← fvar.getUserName).appendAfter "_mod"
        let hx_eq_ident := mkIdent <| (← fvar.getUserName).appendAfter "_mod_eq"

        -- `generalize` tactic needs the expression to be generalized
        let expr_stx ← `((Int.cast $x_ident : $zmod_n_stx))

        -- Call: `generalize hx_eq_ident : (↑x) = x_mod_ident`
        -- This introduces `x_mod_ident` as a new *free* variable.
        -- We run this *at h_mod_n* to replace (↑x) there.
        evalTactic (← `(tactic|
          generalize $hx_eq_ident : $expr_stx = $x_mod_ident at $h_mod_loc*
        ))

        -- Save the new FVarIds
        let x_mod_fvar ← getFVarId x_mod_ident
        mod_fvars_to_revert := mod_fvars_to_revert.push x_mod_fvar
        eq_hyps_to_clear := eq_hyps_to_clear.push hx_eq_ident

      -- 7. Clear all the *original* integer vars, the *original*
      --    equality, and the *new* `_mod_eq` equalities.
      let mut clear_locs : Array (TSyntax `ident) := eq_hyps_to_clear
      clear_locs := clear_locs.push h_ident -- Add `h`
      for fvar in int_fvars do
        clear_locs := clear_locs.push (mkIdent (← fvar.getUserName)) -- Add `x`, `y`, ...

      evalTactic (← `(tactic| clear $clear_locs*))

       -- 8. Revert all the new `_mod` vars and `h_mod_n`
      let h_mod_fvar ← getFVarId h_mod_ident
      let current_goal ← getMainGoal
      let g' ← current_goal.revert (mod_fvars_to_revert.push h_mod_fvar)
      setGoals [g'.snd]

      -- 9. The goal is now `∀ (x_mod y_mod ...), ... → False`. Call `decide`.
      evalTactic (← `(tactic| decide))

      -- logInfo s!"Proof complete. Reduced modulo {n_stx} and solved with `decide`."
    -- Add a fallback case for the match
  | _ => throwUnsupportedSyntax


example : ¬ ∃ (x y : ℤ), x^2 + y^2 = 3 := by
  intro h; rcases h with ⟨⟩
  no_sols_mod_n 4
