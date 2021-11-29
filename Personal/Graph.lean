import Mathlib.All


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

namespace Lean.Environment

def find! (e : Environment) (nm : Name) : ConstantInfo := (e.find? nm).get!

end Lean.Environment

namespace Std.RBMap

variable {α β : Type _} { cmp : α → α → Ordering}
def filter (t : RBMap α β cmp) (f : α → β → Bool) : RBMap α β cmp :=
  t.fold (init := ∅) fun es a b => match f a b with
  | true  => es.insert a b
  | false => es

-- where might be a more efficient way to do this using `RBNode.append`
def union (t₁ t₂ : RBMap α β cmp) : RBMap α β cmp :=
  t₂.fold (init := t₁) fun t a b => t.insert a b

def mapValue (t : RBMap α β cmp) (f : β → γ) : RBMap α γ cmp :=
t.fold (λ t' x y => t'.insert x (f y)) ∅

end Std.RBMap

namespace Lean.Expr

/-- The names occurring in an expression.-/
def listNames (e : Expr) : NameSet :=
e.foldConsts ∅ λ nm nms => nms.insert nm

end Lean.Expr

namespace Array

def range (n : Nat) : Array ℕ :=
(List.range n).toArray

def positions {α : Type _} (a : Array α) (cmp : α → α → Ordering) : RBMap α ℕ cmp :=
(a.zip $ range a.size).foldl (λ t (x, n) => t.insert x n) ∅

def sum (a : Array Float) : Float :=
a.foldr (·+·) 0

end Array

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

def isInteresting (nm : Name) (info : ConstantInfo) : Bool :=
!(nm.isInternal || info.isUnsafe)

/- by Gabriel -/
def getDeclsInCurrModule : CoreM (Array Name) := do
  (← getEnv).constants.map₂.toList.toArray.map (·.1)

/- by Gabriel -/
def getAllDecls : CoreM (Array Name) := do
  (← getDeclsInCurrModule) ++
    (← getEnv).constants.map₁.toArray.map (·.1)

/- by Gabriel -/
def getDeclsInMathlib : CoreM (Array Name) := do
  let mut decls ← getDeclsInCurrModule
  let mathlibModules := (← getEnv).header.moduleNames.map ((`Mathlib).isPrefixOf ·)
  for (declName, moduleIdx) in (← getEnv).const2ModIdx.toArray do
    if mathlibModules[moduleIdx] then
      decls := decls.push declName
  decls

def interestingDecls : CoreM (Array Name) := do
  let env ← getEnv
  (← getAllDecls).filter λ nm => isInteresting nm $ env.find! nm

-- /-- There is an edge from `v₁` to `v₂` if `v₁` references `v₂`. -/
-- def references (v₁ v₂ : Name × ConstantInfo) : Bool :=
-- v₁.2.anyRefs.contains v₂.1

--(some [Lean.ConstantInfo, Prod.snd, Prod.fst, Prod, Bool, Lean.NameSet.contains, Lean.Name, Lean.ConstantInfo.anyRefs])

def dampingFactor : Float := 0.85

structure NameNode where
  -- info : ConstantInfo
  name : Name
  outEdges : Array ℕ
  inEdges : Array ℕ
  weight : Float
deriving Inhabited

structure NameGraph where
  size  : ℕ
  nodes : Array NameNode
  -- nodes   : NameMap ConstantInfo
  -- edges   : NameMap NameSet
  -- weights : NameMap Float
deriving Inhabited
#check Array.qsort
def mkNameGraph : CoreM NameGraph := do
  let l ← interestingDecls
  let n := l.size
  let env ← getEnv
  let pos : NameMap ℕ := l.positions _
  let a : Array (Name × Array ℕ) := l.map λ nm => (nm, (env.find! nm).anyRefs.toArray.filterMap pos.find?)
  -- transpose outEdges
  let inEdges := Array (Array ℕ) := _
  return ⟨n, a.map λ ⟨nm, outEdges⟩ => ⟨nm, outEdges, _, (1 : Float) / Float.ofNat n⟩⟩
--l.map λ nm => ⟨nm, (env.find! nm).anyRefs.toArray.filterMap pos.find? , (1 : Float) / Float.ofNat n⟩

def edgeNames (g : NameGraph) (nn : NameNode) : Array Name :=
nn.edges.map λ n => g.nodes[n].name


-- as a trial: we let weight flow the wrong way
def step (g : NameGraph) : NameGraph :=
⟨g.size, g.nodes.map λ nn => ⟨nn.name, nn.edges,
  (1 - dampingFactor) / Float.ofNat g.size +
  dampingFactor * (nn.edges.map $ λ n => (g.nodes[n]).weight / Float.ofNat nn.edges.size).sum⟩⟩ -- todo: fix, using wrong length

-- #exit
#eval (do
  let env ← getEnv
  let g ← mkNameGraph
  let nr := 12341
  IO.println $ (g.nodes[nr].weight * (Float.ofNat g.size))
  IO.println $ (g.nodes[nr].name)
  IO.println $ (env.find! g.nodes[nr].name).anyRefs.toList
  IO.println $ (edgeNames g g.nodes[nr])
  let g := step g
  IO.println $ (g.nodes[nr].weight * (Float.ofNat g.size))
  return ()
  : MetaM Unit)


#check Array.qsort
