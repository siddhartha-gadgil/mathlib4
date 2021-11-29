import .All


#eval 1+1

open Lean Elab Tactic Meta Std
open Elab.Tactic
#print prefix Lean.Environment
#print Lean.Environment
def fooT : MetaM Unit := do
let e ← getEnv
let numberOfDecls := e.constants.fold (λ n nm info => if True then n+1 else n) 0
-- IO.println e.allImportedModuleNames
IO.println numberOfDecls

namespace SMap

variable {α β γ : Type _} [BEq α] [Hashable α]
-- If I go via `List (α × β) Lean crashes with an error (stack overflow?)
def mapToRBMap (m : SMap α β) {cmp : α → α → Ordering} (f : β → γ) : RBMap α γ cmp :=
  m.fold (init := ∅) fun es a b => es.insert a (f b)

end SMap

namespace Lean.ConstMap
def toNameSet (m : ConstMap) : NameSet :=
  SMap.mapToRBMap m λ _ => ()
end Lean.ConstMap

namespace Std.RBMap

variable {α β : Type _} { cmp : α → α → Ordering}
def filter (t : RBMap α β cmp) (f : α → β → Bool) : RBMap α β cmp :=
  t.fold (init := ∅) fun es a b => match f a b with
  | true  => es.insert a b
  | false => es

def union (t₁ t₂ : RBMap α β cmp) : RBMap α β cmp :=
  t₂.fold (init := t₁) fun t a b => t.insert a b

end Std.RBMap

namespace Lean.Expr

/-- The names occurring in an expression.-/
def listNames (e : Expr) : NameSet :=
e.foldConsts ∅ λ nm nms => nms.insert nm

end Lean.Expr

namespace Lean.ConstantInfo

/-- The names referred to in the type.-/
def typeRefs (info : ConstantInfo) : NameSet :=
info.type.listNames

/-- The names referred to in the value of the expression.-/
def valueRefs (info : ConstantInfo) : NameSet :=
(info.value?.map λ e => e.listNames).getD ∅

/-- The names referred to in the expression. -/
def anyRefs (info : ConstantInfo) : NameSet :=
info.typeRefs.union info.valueRefs

end Lean.ConstantInfo

def NameTree : Type := RBMap Name ConstantInfo Name.quickCmp

def isInteresting (nm : Name) (info : ConstantInfo) : Bool :=
!nm.isInternal

def interestingDecls : MetaM NameTree := do
let e ← getEnv
let interestingDeclsList := (SMap.mapToRBMap e.constants id).filter isInteresting
return interestingDeclsList

/-- There is an edge from `v₁` to `v₂` if `v₁` references `v₂`. -/
def references (v₁ v₂ : Name × ConstantInfo) : Bool :=
v₁.2.anyRefs.contains v₂.1



#eval (do
  -- fooT
  let l ← interestingDecls
  let l2 := l.toList
  let es : RBMap Name NameSet Name.quickCmp := l.fold _ ∅
  IO.println $ l.size
  -- IO.println l2
  return ()
  -- IO.println l.size
  : MetaM Unit)

def dampingFactor : Float := 0.85


-- syntax (name := foo) "foo" : tactic
-- @[tactic «foo»] def evalFoo : Tactic := fun stx =>
--   match stx with
--   | `(tactic| foo) => fooT
--   | _ => throwUnsupportedSyntax

-- example : True := by -- 134651 decls
--   foo
--   trivial
