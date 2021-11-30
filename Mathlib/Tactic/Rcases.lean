/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import Mathlib.Tactic.Rename

/-!
# Stub for the `rcases` tactic.

The `rcases` tactic has not been implemented yet.
This file contains the syntax definition for `rcases` patterns,
as they are used in several places.

-/

namespace Mathlib.Tactic
open Lean

declare_syntax_cat rcasesPat
syntax rcasesPatMed := sepBy1(rcasesPat, " | ")
syntax rcasesPatLo := rcasesPatMed (" : " term)?
syntax (name := rcasesPat.one) ident : rcasesPat
syntax (name := rcasesPat.ignore) "_" : rcasesPat
syntax (name := rcasesPat.clear) "-" : rcasesPat
syntax (name := rcasesPat.tuple) "⟨" rcasesPatLo,* "⟩" : rcasesPat
syntax (name := rcasesPat.paren) "(" rcasesPatLo ")" : rcasesPat

section
open Parser.Tactic
syntax (name := rcases?) "rcases?" casesTarget,* (" : " num)? : tactic
syntax (name := rcases) "rcases" casesTarget,* (" with " rcasesPat)? : tactic
end

-- macro_rules
--   | `(tactic| rcases $xs,* with ⟨$pats,*⟩) => do
--     if xs.getElems.size == 1 then Macro.throwUnsupported
--     if pats.getElems.size != xs.getElems.size then
--       Macro.throwError "number of terms and patterns differ"
--     let mut tacs := #[]
--     for x in xs.getElems, pat in pats.getElems do
--       tacs := tacs.push <|<- `(tactic| rcases $x with $pat)
--     `(tactic| $[$tacs:tactic];*)

macro_rules
  | `(tactic| rcases $x with _) => `(tactic| skip)
  | `(tactic| rcases $x with $y:ident) =>
    `(tactic| rename' $x => $y:ident)

open Elab.Tactic in
elab_rules : tactic
  | `(tactic| rcases $x:casesTarget with -) => focus do
    for x in ← elabCasesTargets #[x] do
      liftMetaTactic1 (Meta.clear · x.fvarId!)

open Elab.Tactic in
elab_rules : tactic
  | `(tactic| rcases $x:casesTarget with ⟨$pats,*⟩) => focus do
    let pats := pats.getElems
    let #[x] ← elabCasesTargets #[x] | unreachable!
    let subgoals ← Meta.cases (← getMainGoal) x.fvarId!
    if pats.size != subgoals.size then
      throwError "expected {pats.size} subgoals, cases produced {subgoals.size}"
    let mut newGoals := []
    for pat in pats, subgoal in subgoals do
      setGoals [subgoal.mvarId]
      newGoals := newGoals ++ (← evalTacticAt (← `(tactic| rcases $(subgoal.fields):ident with $pat)) _)
    setGoals newGoals

set_option pp.rawOnError true
example : True := by rcases x, y with ⟨z, w⟩
example : True := by rcases x with ⟨z⟩
example (x : Unit) : True := by rcases x with -

declare_syntax_cat rintroPat
syntax (name := rintroPat.one) rcasesPat : rintroPat
syntax (name := rintroPat.binder) "(" rintroPat+ (" : " term)? ")" : rintroPat

syntax (name := rintro?) "rintro?" (" : " num)? : tactic
syntax (name := rintro) "rintro" (ppSpace rintroPat)* (" : " term)? : tactic

macro_rules
  | `(tactic|rintro $a:rcasesPat) =>
    `(tactic|intro a; rcases a with $a:rcasesPat)
  | `(tactic|rintro ($p:rintroPat : $ty)) =>
    `(tactic|refine fun a : $ty => ?_; rcases a with $p)
  | `(tactic|rintro ($p:rintroPat $ps:rintroPat* : $ty)) =>
    `(tactic|rintro ($p:rintroPat : $ty) <;> rintro ($ps:rintroPat* : $ty))
  | `(tactic|rintro $a:rintroPat $[$p:rintroPat]*) =>
    `(tactic|rintro $a:rintroPat <;> rintro $[$p:rintroPat]*)

end Lean.Parser.Tactic
