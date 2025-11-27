import Lean
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Lean.Meta.Tactic.TryThis

open Lean Meta Elab Tactic PrettyPrinter

/-
todo: add documentation.
-/

syntax (name := noSolsModN) "reduceModN " num : tactic

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
def elabReduceModN : Tactic := fun stx =>
match stx with
  | `(tactic| reduceModN $n_stx) => do
    let name_for_h_fvar ← mkFreshUserName `h

    let mainGoal ← getMainGoal

    let (h_fvar, goalAfterIntro) ← mainGoal.intro name_for_h_fvar
    let collected_fvars ← recursively_call_cases goalAfterIntro h_fvar
    let current_h_fvar := collected_fvars[0]!

    withMainContext do
      let h_decl ← current_h_fvar.getDecl
      let h_ident := mkIdent h_decl.userName
      let int_fvars ← collected_fvars.filterM isIntFVar
      if int_fvars.isEmpty then
        throwError "Could not find any `ℤ` variables in the context."

      let zmod_n_stx ← `(ZMod $n_stx)
      let h_mod_ident := mkIdent (← mkFreshUserName `h_mod_n)

      evalTactic (← `(tactic|
        have $h_mod_ident := congr_arg (Int.cast : ℤ → $zmod_n_stx) $h_ident
      ))

      let h_mod_loc : Array (TSyntax `ident) := #[h_mod_ident]

      evalTactic (← `(tactic| push_cast at $h_mod_loc*))

      let mut mod_fvars_to_revert : Array FVarId := #[]
      let mut eq_hyps_to_clear : Array (TSyntax `ident) := #[]

      for fvar in int_fvars do
        let x_ident := mkIdent (← fvar.getUserName)
        let x_mod_ident := mkIdent <| (← fvar.getUserName).appendAfter "_mod"
        let hx_eq_ident := mkIdent <| (← fvar.getUserName).appendAfter "_mod_eq"

        let expr_stx ← `((Int.cast $x_ident : $zmod_n_stx))

        evalTactic (← `(tactic|
          generalize $hx_eq_ident : $expr_stx = $x_mod_ident at $h_mod_loc*
        ))

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

      evalTactic (← `(tactic| decide))
  | _ => throwUnsupportedSyntax


register_option searchModN.max_modulus : Nat := {
  defValue := 50
  group    := "searchModN"
  descr    := "Maximum modulus n to check for the 'searchModN' tactic (default: 50)."
}

syntax (name := searchModN) "searchModN" : tactic

@[tactic searchModN]
def elabSearchModN : Tactic := fun _ =>
  withMainContext do
    let max_mod : ℕ := searchModN.max_modulus.get (← getOptions)

    if max_mod < 2 then
      logError m! "'searchModN.max_modulus' must be at least 2, but was set to {max_mod}.
      You can change this by using 'set_option searchModN.max_modulus'"

    let mut found_mod := none

    for n in [2:max_mod+1] do
      let s ← saveState
      let n_stx := Syntax.mkNumLit (toString n)
      let tactic_call ← `(tactic| reduceModN $n_stx)

      let result ← try
        evalTactic tactic_call
        pure true
      catch _ =>
        pure false

      if result then
        let newGoals ← getUnsolvedGoals
        if newGoals.isEmpty then
          logInfo m!"{n}"
          found_mod := some n
          break
        else
          s.restore

    match found_mod with
    | some n =>
      let suggestion := Syntax.mkApp (mkIdent `reduceModN) #[quote n]
      let stx ← getRef
      TryThis.addSuggestion stx suggestion
    | none =>
      logError m!"searchModN failed to find a working modulus between 2 and {max_mod}. \
      The max_modulus for this tactic was set to {max_mod}. \
      You can change this using 'set_option searchModN.max_modulus`."
