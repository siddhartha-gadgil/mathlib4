import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Simp

-- run_cmd mk_simp_attr `split_if_reduction
-- run_cmd add_doc_string `simp_attr.split_if_reduction "Simp set for if-then-else statements"

-- attribute [split_if_reduction] if_pos if_neg dif_pos dif_neg

-- meta def reduce_ifs_at (at_ : loc) : tactic unit := do
-- sls ← get_user_simp_lemmas `split_if_reduction,
-- let cfg : simp_config := { fail_if_unchanged := ff },
-- let discharger := assumption <|> (applyc `not_not_intro >> assumption),
-- hs ← at_.get_locals, hs.mmap' (λ h, simp_hyp sls [] h cfg discharger >> skip),
-- when at_.include_goal (simp_target sls [] cfg discharger >> skip)

open Lean
open Lean.Parser.Tactic
open Lean.Meta
open Lean.Elab.Tactic

-- TODO move this to Lean/Meta/Tactic/Simp.lean
-- TODO and refactor Lean/Elab/Tactic/Simp.lean to use it
def simpLocation (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (fvarIdToLemmaId : Elab.Tactic.FVarIdToLemmaId := {}) (loc : Location) : TacticM Unit := do
  match loc with
  | Location.targets hUserNames simplifyTarget =>
    withMainContext do
      let fvarIds ← hUserNames.mapM fun hUserName => return (← getLocalDeclFromUserName hUserName).fvarId
      go fvarIds simplifyTarget fvarIdToLemmaId
  | Location.wildcard =>
    withMainContext do
      go (← getNondepPropHyps (← getMainGoal)) (simplifyTarget := true) fvarIdToLemmaId
where
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) (fvarIdToLemmaId : Lean.Meta.FVarIdToLemmaId) : TacticM Unit := do
    let mvarId ← getMainGoal
    let result? ← simpGoal mvarId ctx (simplifyTarget := simplifyTarget) (discharge? := discharge?) (fvarIdsToSimp := fvarIdsToSimp) (fvarIdToLemmaId := fvarIdToLemmaId)
    match result? with
    | none => replaceMainGoal []
    | some (_, mvarId) => replaceMainGoal [mvarId]


namespace Tactic

/-- `simpIfs (at h)?` simplifies `if ... then ... else ...`
using `if_pos`, `if_neg`, `dif_pos`, and `dif_neg`,
and local hypotheses to discharge the conditions. -/
syntax (name := simpIfs) "simpIfs" (ppSpace location)? : tactic

open Lean.Elab.Tactic

-- open Elab.Tactic Elab Tactic in
elab_rules : tactic
| `(tactic| simpIfs $[$loc:location]?) => do
  let discharge := sorry
  let lemmas := sorry
  simpLocation (← Lean.Meta.Simp.Context.mkDefault) (some discharge) lemmas (expandOptLocation $ mkOptionalNode loc)
  -- done


example (h : false) : 1 = 1 := by
  simp
  simpIfs at h
  sorry


syntax (name := splitIfs) "splitIfs" (ppSpace location)? (" with " binderIdent+)? : tactic

end Tactic
