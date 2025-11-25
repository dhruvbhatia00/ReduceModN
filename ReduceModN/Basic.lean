import Lean
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

open Lean Meta Elab Tactic PrettyPrinter

-- 1. Define the syntax
syntax (name := noSolsModN) "reduceModN " num : tactic

-- This helper function checks if an FVarId has type `ℤ`
def isIntFVar (fvarId : FVarId) : TacticM Bool := do
  let type ← inferType (mkFVar fvarId)
  return type.isConstOf ``Int

partial def recursively_call_cases (goal : MVarId) (h : FVarId)
  : TacticM (Array FVarId) := do
  try
    goal.withContext do
      let cases_subgoals ← goal.cases h
      let some new_cases_subgoal := cases_subgoals[0]? | throwError "todo: Fix this error message"
      let new_goal := new_cases_subgoal.mvarId

      let fields := new_cases_subgoal.fields
      let Expr.fvar int_fvar := fields[0]!
        | throwError "First field was not an FVar: {← delab fields[0]!}"
      let Expr.fvar new_h := fields[1]!
        | throwError "Second field was not an FVar: {← delab fields[1]!}"

      replaceMainGoal [new_goal]
      let collected_fvars ← recursively_call_cases new_goal new_h
      return collected_fvars ++ #[int_fvar]
  catch _ => return #[h]

@[tactic noSolsModN]
def elabNoSolsModN : Tactic := fun stx =>
-- Parse the modulus `n` from the syntax
match stx with
  | `(tactic| reduceModN $n_stx) => do
    let name_for_h_fvar ← mkFreshUserName `h

    let mainGoal ← getMainGoal

    let (h_fvar, goalAfterIntro) ← mainGoal.intro name_for_h_fvar
    let collected_fvars ← recursively_call_cases goalAfterIntro h_fvar
    let current_h_fvar := collected_fvars[0]!

    withMainContext do
      let h_decl ← current_h_fvar.getDecl
      -- logInfo m!"{h_decl.type}"
      let h_ident := mkIdent h_decl.userName
      -- logInfo m!"{h_decl.userName}"
      let int_fvars ← collected_fvars.filterM isIntFVar
      if int_fvars.isEmpty then
        throwError "Could not find any `ℤ` variables in the context."

      let zmod_n_stx ← `(ZMod $n_stx)
      let h_mod_ident := mkIdent (← mkFreshUserName `h_mod_n)

      evalTactic (← `(tactic|
        have $h_mod_ident := congr_arg (Int.cast : ℤ → $zmod_n_stx) $h_ident
      ))

      -- Create a location array for `h_mod_ident` (`h_mod_n`)
      let h_mod_loc : Array (TSyntax `ident) := #[h_mod_ident]

      -- 5. `push_cast` at `h_mod_n`
      --    Use the array splice syntax `$h_mod_loc*`
      evalTactic (← `(tactic| push_cast at $h_mod_loc*))

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

      let mut clear_locs : Array (TSyntax `ident) := eq_hyps_to_clear
      clear_locs := clear_locs.push h_ident -- Add `h`
      for fvar in int_fvars do
        clear_locs := clear_locs.push (mkIdent (← fvar.getUserName)) -- Add `x`, `y`, ...

      evalTactic (← `(tactic| clear $clear_locs*))

      let h_mod_fvar ← getFVarId h_mod_ident
      let current_goal ← getMainGoal
      let g' ← current_goal.revert (mod_fvars_to_revert.push h_mod_fvar)
      setGoals [g'.snd]

      -- 9. The goal is now `∀ (x_mod y_mod ...), ... → False`. Call `decide`.
      evalTactic (← `(tactic| decide))
  | _ => throwUnsupportedSyntax


example : ¬ ∃ (x y: ℤ), x^2 + y^2 = 3 := by
  reduceModN 4
