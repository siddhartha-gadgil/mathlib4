import Mathlib

open Lean Elab Tactic Meta Std
open Elab.Tactic Core

namespace SMap

variable {α β γ : Type _} [BEq α] [Hashable α]
-- If I go via `List (α × β)` Lean crashes with an error (stack overflow?)
def mapToRBMap (m : SMap α β) {cmp : α → α → Ordering} (f : β → γ) : RBMap α γ cmp :=
  m.fold (init := ∅) fun es a b => es.insert a (f b)

end SMap


protected def List.toStringSepAux {α : Type u} [ToString α] (sep : String := ", ") :
  Bool → List α → String
  | b,     []    => ""
  | true,  x::xs => toString x ++ List.toStringSepAux sep false xs
  | false, x::xs => sep ++ toString x ++ List.toStringSepAux sep false xs

protected def List.toStringSep {α : Type u} [ToString α] (sep : String := ", ") : List α → String
  | []    => "[]"
  | x::xs => "[" ++ List.toStringSepAux sep true (x::xs) ++ "]"

protected def Array.toString {α : Type u} [ToString α] (sep : String := ", ") (xs : Array α) :
  String :=
"#[" ++ (if xs.size == 0 then "" else
  ((xs.get? 0).map toString).get! ++ xs.foldl (λ str x => str ++ sep ++ toString x) "" 1) ++ "]"

/-- We modify the `ToString (Array α)` instance, because (1) we want a newline between items and (2)
  we got a stack overflow when printing a very large array (>100k entries). -/
instance [ToString α] : ToString (Array α) where
  toString := Array.toString ",\n"


-- namespace Lean.ConstMap
-- def toNameSet (m : ConstMap) : NameSet :=
--   SMap.mapToRBMap m λ _ => ()
-- end Lean.ConstMap

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

namespace Std
/-- a variant of RBMaps that stores a list of elements for each key.
   `find` returns the list of elements in the opposite order that they were inserted. -/
def RBLMap (α β : Type _) (cmp : α → α → Ordering) : Type _ := RBMap α (List β) cmp

@[inline] def mkRBLMap (α : Type) (β : Type) (cmp : α → α → Ordering) : RBLMap α β cmp :=
mkRBMap α (List β) cmp

namespace RBLMap

variable {α β : Type _} {cmp : α → α → Ordering}

def insert (t : RBLMap α β cmp) (x : α) (y : β) : RBLMap α β cmp :=
match t.find? x with
| none   => RBMap.insert t x [y]
| some l => RBMap.insert (t.erase x) x (y :: l)

def erase (t : RBLMap α β cmp) (k : α) : RBLMap α β cmp :=
RBMap.erase t k

def contains (t : RBLMap α β cmp) (k : α) : Bool :=
RBMap.contains t k

def find (t : RBLMap α β cmp) (k : α) : List β :=
(RBMap.find? t k).getD []

end RBLMap

def NameLMap (β : Type _) := RBLMap Name β Name.quickCmp

instance (β : Type _) : EmptyCollection (NameLMap β) := ⟨mkNameMap _⟩

end Std

namespace Lean.Expr

/-- The names occurring in an expression. -/
def listNames (e : Expr) : NameSet :=
e.foldConsts ∅ λ nm nms => nms.insert nm

end Lean.Expr

namespace Array

def positions {α : Type _} (a : Array α) (cmp : α → α → Ordering) : RBMap α ℕ cmp :=
(a.zip $ range a.size).foldl (λ t (x, n) => t.insert x n) ∅

def sum (a : Array Float) : Float :=
a.foldl (·+·) 0

def take {α : Type _} [Inhabited α] (a : Array α) (n : ℕ) : Array α :=
if a.size ≤ n then a else (range n).map (a.get! ·)

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
!(nm.isInternal || info.isUnsafe || (`Lean).isPrefixOf info.name)

/- by Gabriel -/
def getDeclsInCurrModule : CoreM (Array Name) := do
  (← getEnv).constants.map₂.toList.toArray.map (·.1)

/- by Gabriel -/
def getAllDecls : CoreM (Array Name) := do
  (← getDeclsInCurrModule) ++
    (← getEnv).constants.map₁.toArray.map (·.1)

/- by Gabriel -/
-- def getDeclsInMathlib : CoreM (Array Name) := do
--   let mut decls ← getDeclsInCurrModule
--   let mathlibModules := (← getEnv).header.moduleNames.map ((`Mathlib).isPrefixOf ·)
--   for (declName, moduleIdx) in (← getEnv).const2ModIdx.toArray do
--     if mathlibModules[moduleIdx] then
--       decls := decls.push declName
--   decls

def interestingDecls : CoreM (Array Name) := do
  let env ← getEnv
  (← getAllDecls).filter λ nm => isInteresting nm $ env.find! nm

def interestingDeclTree : CoreM (NameLMap Name) := do
let e ← getEnv
let interestingDeclsList := (SMap.mapToRBMap e.constants id).filter isInteresting
interestingDeclsList.mapValue λ info => info.anyRefs.toList

def transpose (t : NameLMap Name) : NameLMap Name :=
t.fold (λ tnew nm_src l => l.foldl (λ tnew nm_tgt => tnew.insert nm_tgt nm_src) tnew) ∅

/-- Edges point from a declaration `d` to all declarations occurring in `d`. -/
structure NameNode where
  name : Name
  outEdges : Array ℕ
  inEdges : Array ℕ
  weight : Float -- we choose the weights so that the sum of the weights is 1
deriving Inhabited

instance : ToString NameNode :=
⟨λ nn => "⟨" ++ toString nn.name ++ ", using " ++ toString nn.outEdges.size ++ ", used by " ++ toString nn.inEdges.size ++
  ", " ++ toString nn.weight ++ "⟩"⟩

/- TODO: currently we ignore all non-interesting declarations occurring in interesting declarations.
For _proof_i and _eqn_i declarations, it would be better to point at the corresponding interesting decl -/

def NameGraph := Array NameNode
deriving Inhabited


-- #print Array.get?
def mkNameGraph : CoreM NameGraph := do
  let l ← interestingDecls
  let env ← getEnv
  let pos : NameMap ℕ := l.positions _
  let inEdges ← transpose <$> interestingDeclTree
  return l.map λ nm => ⟨nm, (env.find! nm).anyRefs.toArray.filterMap pos.find?,
    (inEdges.find nm).toArray.filterMap pos.find?, (1 : Float) / Float.ofNat l.size⟩

def inEdgeNames (g : NameGraph) (nn : NameNode) : Array Name :=
nn.inEdges.map λ n => g[n].name

def outEdgeNames (g : NameGraph) (nn : NameNode) : Array Name :=
nn.outEdges.map λ n => g[n].name

def weightWithNoOutEdges (g : NameGraph) : Float :=
g.foldl (λ s nn => if nn.outEdges.isEmpty then s + nn.weight else s) 0

def totalWeight (g : NameGraph) : Float :=
g.foldl (λ s nn => s + nn.weight) 0

/--
Every step, `w(A)`, the weight of node `A` is changed to
`(1 - d) / N + d ∑_B w(B) / L(B)`
where:
* `d` is the damping factor
* `N` is the size of the graph
* we sum over all nodes `B` that has a edge to `A`
* `L(B)` is the number of outgoing edges out of `B`.
-/
def step (g : NameGraph) (dampingFactor : Float := 0.85) : NameGraph :=
let w := weightWithNoOutEdges g
g.map λ nn => { nn with weight :=
  (1 - dampingFactor + w * dampingFactor) / Float.ofNat g.size +
  dampingFactor * (nn.inEdges.foldl (λ s n => s + g[n].weight / Float.ofNat g[n].outEdges.size) 0) }

def sortByName (g : NameGraph) : NameGraph :=
g.qsort λ nn1 nn2 => nn1.name.quickCmp nn2.name == Ordering.lt

def sortRevByWeight (g : NameGraph) : NameGraph :=
g.qsort λ nn1 nn2 => nn1.weight > nn2.weight

def printData (printNum : ℕ := 0) (iter : ℕ := 5) (sort? : Bool := true) (trace? : Bool := false)
  (filter : Option String := none) :
  CoreM Unit := do
  let env ← getEnv
  if trace? then IO.println "generating graph..."
  let g ← mkNameGraph
  if iter > 0 then
    if trace? then IO.println "calculating weights..."
    let g := iter.iterate step g
    if sort? then
      if trace? then IO.println "sorting graph..."
      let g := sortRevByWeight g -- Todo: the inEdges and outEdges point at wrong things after sorting
      let g ←
        if filter == some "structure" then
          if trace? then IO.println "filtering nodes..."
          pure $ g.filter (isStructure env ·.name)
        else
          pure g
      let itemStr := if filter == some "structure" then "structures" else "entries"
      IO.println $ "After iterating " ++ toString iter ++ " times, " ++
        (if printNum > 0 then
          "the " ++ toString printNum ++ " " ++ itemStr ++ " with the highest weight:"
        else
          "all " ++ itemStr ++ " sorted by weight")
      IO.println $ if printNum > 0 then g.take printNum else g
    else
      IO.println $ "After iterating " ++ toString iter ++ " times, " ++
        (if printNum > 0 then toString printNum else "all") ++ " entries:"
      IO.println $ if printNum > 0 then g.take printNum else g
  else
    IO.println $ (if printNum > 0 then toString printNum else "all") ++ " entries from the graph:"
    IO.println $ if printNum > 0 then g.take printNum else g
  return ()

/--
To compile:
* Make sure you have `elan` (which you have if you have ever installed Lean)
* Run `elan self update`
* Clone/Download the `leanprover-community/mathlib4` repository
* Checkout the branch `fpvandoorn/graph`
* Run `lake build`
To run, you can run something like :
`time ./build/bin/mathlib 0 100 1 1 structure Mathbin > out.txt`
All arguments are optional, but you have to provide the arguments in order:
* The first argument is the number of entries printed (default = 0, which means print everything)
* The second argument is the number of iterations of the pagerank algorithm
* The third argument determines whether to sort the data (0 = don't sort, 1 (default) = sort)
* The fourth argument determines whether to print some debugging info (0 (default) = no, 1 = yes)
* The fifth argument determines which nodes to filter (currently "structure" means only print
  structures, any other argument means no filtering)
* The sixth argument determines which library to use ("Mathbin" (capitalized!) means use the
  libraries of Lean 3 + Lean 4, anything else means only use the Lean 4 library).
-/
def main (strs : List String) : IO UInt32 := do
  let env ←
    if strs.get? 5 == some "Mathbin" then
      initSearchPath (← Lean.findSysroot?) ["../mathlib3port/build/lib",
      "../mathlib3port/lean_packages/lean3port/build/lib/",
      "../mathlib3port/lean_packages/mathlib/build/lib/"]
      importModules [{module := `Mathbin}] {}
    else
      initSearchPath (← Lean.findSysroot?) ["build/lib"]
      importModules [{module := `Mathlib}] {}
  let args := ((strs.take 4).map String.toNat!).toArray
  let u ← CoreM.toIO
    (printData (args.getD 0 10) (args.getD 1 5) (args.getD 2 1 != 0) (args.getD 3 0 != 0)
      (strs.get? 4))
    {} {env := env}
  return 0
