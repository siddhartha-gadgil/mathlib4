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

namespace Lean.Parser.Tactic

declare_syntax_cat rcasesPat
syntax rcasesPatMed := sepBy1(rcasesPat, " | ")
syntax rcasesPatLo := rcasesPatMed (" : " term)?
syntax (name := rcasesPat.one) ident : rcasesPat
syntax (name := rcasesPat.ignore) "_" : rcasesPat
syntax (name := rcasesPat.clear) "-" : rcasesPat
syntax (name := rcasesPat.tuple) "⟨" rcasesPatLo,* "⟩" : rcasesPat
syntax (name := rcasesPat.paren) "(" rcasesPatLo ")" : rcasesPat

syntax (name := rcases?) "rcases?" casesTarget,* (" : " num)? : tactic
syntax (name := rcases) "rcases" casesTarget,* (" with " rcasesPat)? : tactic

local elab "elabCasesTarget " casesTarget : term => sorry

macro_rules
  | `(tactic| rcases $xs,* with ⟨$pats,*⟩) => do
    if xs.getElems.size == 1 then Macro.throwUnsupported
    if pats.getElems.size != xs.getElems.size then
      Macro.throwError "number of terms and patterns differ"
    let mut tacs := #[]
    for x in xs.getElems, pat in pats.getElems do
      tacs := tacs.push <|<- `(tactic| rcases $x with $pat)
    `(tactic| $[$tacs:tactic];*)

macro_rules
  | `(tactic| rcases $x with _) => `(tactic| skip)
  | `(tactic| rcases $x with -) => `(tactic| clear (elabCasesTarget $x))
  | `(tactic| rcases $x with $y:ident) =>
    `(tactic| rename $x $y:ident)

set_option pp.rawOnError true
example : True := by rcases x, y with ⟨z, w⟩
example : True := by rcases x with ⟨z⟩

declare_syntax_cat rintroPat
syntax (name := rintroPat.one) rcasesPat : rintroPat
syntax (name := rintroPat.binder) "(" rintroPat+ (" : " term)? ")" : rintroPat

syntax (name := rintro?) "rintro?" (" : " num)? : tactic
syntax (name := rintro) "rintro" (ppSpace rintroPat)* (" : " term)? : tactic

macro_rules
  | `(tactic|rintro 

end Lean.Parser.Tactic
