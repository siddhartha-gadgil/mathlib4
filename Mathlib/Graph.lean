import Mathlib

open Lean Elab Tactic Meta Std
open Elab.Tactic Core

namespace SMap

variable {α β γ : Type _} [BEq α] [Hashable α]
-- If I go via `List (α × β)` Lean crashes with an error (stack overflow?)
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
a.foldr (·+·) 0

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
  weight : Float
deriving Inhabited

instance : ToString NameNode :=
⟨λ nn => "⟨" ++ toString nn.name ++ ", using " ++ toString nn.outEdges.size ++ ", used by " ++ toString nn.inEdges.size ++
  ", " ++ toString nn.weight ++ "⟩"⟩

protected def List.toStringSepAux {α : Type u} [ToString α] (sep : String := ", ") :
  Bool → List α → String
  | b,     []    => ""
  | true,  x::xs => toString x ++ List.toStringSepAux sep false xs
  | false, x::xs => sep ++ toString x ++ List.toStringSepAux sep false xs

protected def List.toStringSep {α : Type u} [ToString α] (sep : String := ", ") : List α → String
  | []    => "[]"
  | x::xs => "[" ++ List.toStringSepAux sep true (x::xs) ++ "]"

instance [ToString α] : ToString (Array α) where
  toString a := "!#" ++ a.toList.toStringSep ",\n"

/- TODO: currently we ignore all non-interesting declarations occurring in interesting declarations.
For _proof_i and _eqn_i declarations, it would be better to point at the corresponding interesting decl -/
/- Todo: we currently "lose" the weight of all declarations that do not refer to anything.
Probably best to uniformly distribute those weights back to all decls. -/

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

-- def nodesWithNoOutEdges (g : NameGraph) : List ℕ :=

def weightWithNoOutEdges (g : NameGraph) : Float :=
g.foldr (λ nn s => if nn.outEdges.isEmpty then s + nn.weight else s) 0

def totalWeight (g : NameGraph) : Float :=
g.foldr (λ nn s => s + nn.weight) 0

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
  dampingFactor * (nn.inEdges.foldr (λ n s => s + g[n].weight / Float.ofNat g[n].outEdges.size) 0) }

def sortByName (g : NameGraph) : NameGraph :=
g.qsort λ nn1 nn2 => nn1.name.quickCmp nn2.name == Ordering.lt

def sortRevByWeight (g : NameGraph) : NameGraph :=
g.qsort λ nn1 nn2 => nn1.weight > nn2.weight

/-
graph currently has 27035 nodes

after 1 step, top weights:
#[Nat, Eq, Lean.Name, Bool, Array, Lean.Expr, OfNat.ofNat, String, Option, instOfNatNat]
Nat's weight is 0.029

-/

def test (printNum : ℕ := 10) (iter : ℕ := 5) (sort? : Bool := true) : CoreM Unit := do
  let env ← getEnv
  let g ← mkNameGraph
  IO.println $ toString printNum ++ " entries from the graph:"
  -- IO.println $ (g.take printNum).map (·.name)
  IO.println $ g.take printNum
  -- IO.println $ "Total weight: " ++ toString (totalWeight g)
  -- IO.println $ "weight (no out edges): " ++ toString (weightWithNoOutEdges g)
  if iter > 0 then
    let g := iter.iterate step g
    IO.println $ "\nAfter iterating " ++ toString iter ++ " times, the same entries:"
    IO.println $ g.take printNum
    -- IO.println $ "Total weight: " ++ toString (totalWeight g)
    -- IO.println $ "weight (no out edges): " ++ toString (weightWithNoOutEdges g)
    if sort? then
      let g := sortRevByWeight g
      -- IO.println $ (g.take printNum).map (·.name)
      IO.println $ "\nAfter iterating " ++ toString iter ++ " times, the " ++ toString printNum ++
        " entries with the highest weight:"
      IO.println $ g.take printNum
  -- let g := step g
  -- let nr := 22313
  -- IO.println $ g[nr]
  -- -- IO.println $ (g[nr].weight * (Float.ofNat g.size))
  -- -- IO.println $ (g[nr].name)
  -- -- IO.println $ (env.find! g[nr].name).anyRefs.toList
  -- -- IO.println $ (outEdgeNames g g[nr])
  -- -- IO.println $ (inEdgeNames g g[nr])
  -- let nr := 20827
  -- IO.println $ (g[nr])
  -- let nr := 12341
  -- IO.println $ (g[nr])
  -- IO.println $ (g[nr].weight * (Float.ofNat g.size))
  return ()
set_option profiler true
-- #print importModules
-- #exit
-- #eval test 1000 10
-- #eval 1

/-
After iterating 10 times, the 1000 entries with the highest weight:
!#[⟨Nat, using 0, used by 8551, 0.030164⟩,
⟨Eq, using 0, used by 7667, 0.021300⟩,
⟨Lean.Name, using 0, used by 4578, 0.014304⟩,
⟨Bool, using 0, used by 3872, 0.011553⟩,
⟨PUnit, using 0, used by 1234, 0.010205⟩,
⟨Option, using 0, used by 3060, 0.009887⟩,
⟨Unit, using 1, used by 3414, 0.009493⟩,
⟨List, using 0, used by 2913, 0.008450⟩,
⟨String, using 0, used by 2861, 0.008058⟩,
⟨Array, using 0, used by 3574, 0.007157⟩,
⟨outParam, using 0, used by 254, 0.007117⟩,
⟨Lean.Expr, using 0, used by 3342, 0.007053⟩,
⟨Prod, using 0, used by 1892, 0.005570⟩,
⟨OfNat.ofNat, using 2, used by 4914, 0.005544⟩,
⟨instOfNatNat, using 3, used by 4631, 0.005186⟩,
⟨Eq.refl, using 1, used by 3293, 0.005077⟩,
⟨Lean.Syntax, using 0, used by 2251, 0.004760⟩,
⟨OfNat, using 1, used by 33, 0.004729⟩,
⟨And, using 0, used by 1583, 0.004091⟩,
⟨Eq.ndrec, using 2, used by 2311, 0.003577⟩,
⟨UInt64, using 0, used by 425, 0.002982⟩,
⟨Option.some, using 1, used by 1993, 0.002781⟩,
⟨Lean.Name.anonymous, using 1, used by 2512, 0.002649⟩,
⟨Lean.Name.mkStr, using 7, used by 2385, 0.002495⟩,
⟨False, using 0, used by 255, 0.002445⟩,
⟨Inhabited, using 0, used by 511, 0.002337⟩,
⟨Monad, using 0, used by 687, 0.002299⟩,
⟨Lean.ParserDescr, using 0, used by 660, 0.002295⟩,
⟨Bool.true, using 1, used by 2508, 0.002269⟩,
⟨BEq, using 0, used by 388, 0.002236⟩,
⟨Option.none, using 1, used by 1283, 0.002159⟩,
⟨ReaderT, using 0, used by 544, 0.002107⟩,
⟨Iff, using 0, used by 397, 0.002045⟩,
⟨Not, using 1, used by 651, 0.002035⟩,
⟨Hashable, using 0, used by 304, 0.001970⟩,
⟨Lean.MVarId, using 0, used by 1202, 0.001914⟩,
⟨IO.RealWorld, using 1, used by 1271, 0.001912⟩,
⟨And.intro, using 1, used by 1370, 0.001912⟩,
⟨HEq, using 0, used by 960, 0.001898⟩,
⟨Prod.mk, using 1, used by 843, 0.001888⟩,
⟨Decidable, using 0, used by 257, 0.001882⟩,
⟨Bool.false, using 1, used by 1445, 0.001850⟩,
⟨Eq.rec, using 2, used by 19, 0.001845⟩,
⟨Unit.unit, using 2, used by 1032, 0.001836⟩,
⟨HAdd, using 1, used by 8, 0.001761⟩,
⟨List.nil, using 1, used by 1403, 0.001758⟩,
⟨rfl, using 2, used by 670, 0.001686⟩,
⟨OfNat.mk, using 2, used by 19, 0.001630⟩,
⟨LT, using 0, used by 71, 0.001628⟩,
⟨Lean.SyntaxNodeKind, using 1, used by 1103, 0.001566⟩,
⟨Bind, using 0, used by 18, 0.001554⟩,
⟨HAdd.hAdd, using 1, used by 1581, 0.001486⟩,
⟨instHAdd, using 4, used by 1581, 0.001486⟩,
⟨StateRefT', using 2, used by 1199, 0.001472⟩,
⟨Pure, using 0, used by 16, 0.001469⟩,
⟨Add, using 0, used by 44, 0.001458⟩,
⟨Lean.PrettyPrinter.Parenthesizer, using 2, used by 481, 0.001417⟩,
⟨List.cons, using 1, used by 1082, 0.001401⟩,
⟨Lean.PrettyPrinter.Formatter, using 2, used by 484, 0.001387⟩,
⟨Lean.Level, using 0, used by 857, 0.001377⟩,
⟨Option.casesOn, using 4, used by 701, 0.001365⟩,
⟨Lean.FVarId, using 0, used by 798, 0.001347⟩,
⟨Applicative, using 0, used by 45, 0.001324⟩,
⟨Except, using 0, used by 312, 0.001306⟩,
⟨Lean.Parser.Parser, using 0, used by 548, 0.001301⟩,
⟨Lean.Meta.MetaM, using 6, used by 1354, 0.001251⟩,
⟨SizeOf.sizeOf, using 2, used by 1100, 0.001217⟩,
⟨instAddNat, using 4, used by 1347, 0.001201⟩,
⟨Ordering, using 0, used by 168, 0.001187⟩,
⟨Fin, using 1, used by 479, 0.001169⟩,
⟨Lean.Environment, using 0, used by 666, 0.001166⟩,
⟨EStateM.Result, using 0, used by 63, 0.001166⟩,
⟨Eq.symm, using 3, used by 1218, 0.001143⟩,
⟨Or, using 0, used by 321, 0.001113⟩,
⟨PUnit.unit, using 1, used by 548, 0.001106⟩,
⟨Nat.succ, using 1, used by 547, 0.001105⟩,
⟨Int, using 0, used by 411, 0.001082⟩,
⟨String.Pos, using 1, used by 464, 0.001071⟩,
⟨Monad.toBind, using 2, used by 1940, 0.001060⟩,
⟨Prod.casesOn, using 3, used by 435, 0.001057⟩,
⟨Exists, using 0, used by 228, 0.001056⟩,
⟨IO.Error, using 0, used by 599, 0.001055⟩,
⟨Lean.MessageData, using 0, used by 571, 0.001042⟩,
⟨Bind.bind, using 1, used by 1932, 0.001042⟩,
⟨LE, using 0, used by 31, 0.001041⟩,
⟨PProd, using 0, used by 383, 0.001028⟩,
⟨Std.Format, using 0, used by 392, 0.001020⟩,
⟨ST.Ref, using 0, used by 45, 0.001011⟩,
⟨Applicative.toPure, using 2, used by 1812, 0.001002⟩,
⟨LT.lt, using 1, used by 616, 0.001000⟩,
⟨Pure.pure, using 1, used by 1761, 0.000991⟩,
⟨Lean.KVMap, using 0, used by 83, 0.000972⟩,
⟨Lean.Core.CoreM, using 7, used by 925, 0.000961⟩,
⟨Subtype, using 0, used by 106, 0.000949⟩,
⟨EIO, using 2, used by 677, 0.000941⟩,
⟨Lean.Json, using 0, used by 275, 0.000934⟩,
⟨Lean.Expr.Data, using 1, used by 448, 0.000893⟩,
⟨UInt32, using 0, used by 319, 0.000890⟩,
⟨HEq.refl, using 1, used by 918, 0.000876⟩,
⟨EStateM, using 1, used by 209, 0.000872⟩,
⟨Inhabited.mk, using 1, used by 378, 0.000869⟩,
⟨IO, using 2, used by 636, 0.000869⟩,
⟨SizeOf, using 0, used by 126, 0.000857⟩,
⟨Lean.IR.FnBody, using 0, used by 339, 0.000857⟩,
⟨Std.RBNode, using 0, used by 185, 0.000840⟩,
⟨Monad.toApplicative, using 2, used by 1037, 0.000832⟩,
⟨Lean.instHashableName, using 4, used by 323, 0.000810⟩,
⟨instLTNat, using 4, used by 591, 0.000787⟩,
⟨Lean.IR.VarId, using 0, used by 344, 0.000780⟩,
⟨Char, using 0, used by 294, 0.000763⟩,
⟨eq_of_heq, using 5, used by 886, 0.000743⟩,
⟨rfl.proof_1, using 2, used by 1, 0.000732⟩,
⟨Eq.casesOn, using 3, used by 874, 0.000723⟩,
⟨Iff.intro, using 1, used by 210, 0.000723⟩,
⟨USize, using 0, used by 237, 0.000711⟩,
⟨Lean.IR.IRType, using 0, used by 324, 0.000708⟩,
⟨ite, using 3, used by 1182, 0.000703⟩,
⟨MonadLiftT, using 0, used by 63, 0.000703⟩,
⟨Float, using 0, used by 131, 0.000699⟩,
⟨Lean.PrettyPrinter.ParenthesizerM, using 6, used by 47, 0.000697⟩,
⟨Lean.ToJson, using 0, used by 139, 0.000695⟩,
⟨Lean.PrettyPrinter.FormatterM, using 6, used by 60, 0.000695⟩,
⟨Mul, using 0, used by 44, 0.000695⟩,
⟨optParam, using 0, used by 541, 0.000693⟩,
⟨Lean.BinderInfo, using 0, used by 263, 0.000692⟩,
⟨Lean.ParserDescr.node, using 3, used by 592, 0.000691⟩,
⟨Eq.propIntro, using 3, used by 841, 0.000689⟩,
⟨Lean.ParserDescr.binary, using 2, used by 582, 0.000682⟩,
⟨LE.le, using 1, used by 436, 0.000675⟩,
⟨Lean.Option, using 0, used by 88, 0.000658⟩,
⟨Lean.LocalContext, using 0, used by 378, 0.000649⟩,
⟨Lean.Options, using 1, used by 342, 0.000636⟩,
⟨True, using 0, used by 365, 0.000633⟩,
⟨HMul, using 1, used by 8, 0.000631⟩,
⟨BEq.mk, using 2, used by 81, 0.000631⟩,
⟨And.casesOn, using 3, used by 663, 0.000628⟩,
⟨MonadLift, using 0, used by 42, 0.000605⟩,
⟨Lean.Name.instBEqName, using 4, used by 469, 0.000586⟩,
⟨HAppend, using 1, used by 9, 0.000579⟩,
⟨Id, using 0, used by 281, 0.000567⟩,
⟨Lean.MetavarContext, using 0, used by 317, 0.000565⟩,
⟨Lean.LocalDecl, using 0, used by 352, 0.000555⟩,
⟨Array.size, using 4, used by 576, 0.000548⟩,
⟨Lean.Exception, using 0, used by 665, 0.000539⟩,
⟨Lean.ParserDescr.symbol, using 2, used by 440, 0.000537⟩,
⟨Lean.SourceInfo, using 0, used by 337, 0.000537⟩,
⟨Std.RBMap, using 4, used by 123, 0.000526⟩,
⟨Lean.Lsp.SymbolKind, using 0, used by 81, 0.000524⟩,
⟨Lean.Meta.State, using 0, used by 769, 0.000521⟩,
⟨Lean.Lsp.DocumentUri, using 1, used by 151, 0.000519⟩,
⟨DecidableEq, using 2, used by 123, 0.000516⟩,
⟨Lean.ParserDescr.nonReservedSymbol, using 3, used by 453, 0.000515⟩,
⟨Append, using 0, used by 19, 0.000510⟩,
⟨UInt8, using 0, used by 184, 0.000510⟩,
⟨Functor, using 0, used by 39, 0.000510⟩,
⟨ToString, using 0, used by 112, 0.000506⟩,
⟨instHMul, using 4, used by 445, 0.000506⟩,
⟨HMul.hMul, using 1, used by 445, 0.000506⟩,
⟨Lean.FromJson, using 0, used by 127, 0.000504⟩,
⟨ReaderT.instMonadReaderT, using 17, used by 733, 0.000498⟩,
⟨Lean.Lsp.Range, using 0, used by 164, 0.000493⟩,
⟨Lean.DataValue, using 0, used by 200, 0.000492⟩,
⟨instDecidableEqBool, using 13, used by 1038, 0.000491⟩,
⟨Hashable.mk, using 2, used by 34, 0.000488⟩,
⟨Lean.Lsp.TextDocumentPositionParams, using 0, used by 111, 0.000485⟩,
⟨Lean.Meta.Context, using 0, used by 750, 0.000471⟩,
⟨arbitrary, using 1, used by 285, 0.000467⟩,
⟨Lean.Name.str, using 3, used by 112, 0.000464⟩,
⟨HAppend.hAppend, using 1, used by 705, 0.000458⟩,
⟨Std.PersistentArray, using 0, used by 188, 0.000457⟩,
⟨Lean.ToJson.mk, using 2, used by 115, 0.000456⟩,
⟨instHAppend, using 4, used by 701, 0.000456⟩,
⟨Lean.NameSet, using 3, used by 167, 0.000455⟩,
⟨Lean.Parser.ParserState, using 0, used by 161, 0.000451⟩,
⟨MProd, using 0, used by 130, 0.000446⟩,
⟨ForInStep, using 0, used by 241, 0.000437⟩,
⟨instDecidableEqNat, using 3, used by 352, 0.000433⟩,
⟨List.casesOn, using 4, used by 180, 0.000427⟩,
⟨Lean.Name.quickCmp, using 9, used by 80, 0.000427⟩,
⟨Lean.IR.Index, using 1, used by 120, 0.000423⟩,
⟨id, using 0, used by 156, 0.000417⟩,
⟨Exists.intro, using 1, used by 163, 0.000409⟩,
⟨Lean.ParserDescr.cat, using 3, used by 355, 0.000408⟩,
⟨Decidable.casesOn, using 5, used by 43, 0.000406⟩,
⟨instLENat, using 4, used by 327, 0.000404⟩,
⟨Lean.IR.Arg, using 0, used by 208, 0.000403⟩,
⟨Lean.Elab.Term.TermElabM, using 6, used by 505, 0.000402⟩,
⟨Lean.FromJson.mk, using 4, used by 107, 0.000398⟩,
⟨PSigma, using 0, used by 40, 0.000394⟩,
⟨Hashable.hash, using 2, used by 46, 0.000393⟩,
⟨PointedType, using 0, used by 14, 0.000391⟩,
⟨Lean.IR.Expr, using 0, used by 208, 0.000390⟩,
⟨Lean.Parser.ParserContext, using 0, used by 125, 0.000390⟩,
⟨StateRefT'.instMonadStateRefT', using 6, used by 786, 0.000389⟩,
⟨Substring, using 0, used by 187, 0.000389⟩,
⟨Lean.Core.State, using 0, used by 533, 0.000387⟩,
⟨Mem, using 1, used by 9, 0.000387⟩,
⟨PProd.fst, using 1, used by 331, 0.000385⟩,
⟨Std.HashMap, using 5, used by 198, 0.000384⟩,
⟨Coe, using 0, used by 73, 0.000382⟩,
⟨Std.Rbcolor, using 0, used by 83, 0.000380⟩,
⟨Function.comp, using 0, used by 220, 0.000379⟩,
⟨Lean.Meta.instMonadMetaM, using 24, used by 927, 0.000379⟩,
⟨MonadExceptOf, using 0, used by 43, 0.000378⟩,
⟨Sub, using 0, used by 32, 0.000377⟩,
⟨Alternative.toApplicative, using 2, used by 919, 0.000376⟩,
⟨Acc, using 0, used by 45, 0.000375⟩,
⟨Lean.Literal, using 0, used by 296, 0.000375⟩,
⟨Lean.ConstantInfo, using 0, used by 196, 0.000374⟩,
⟨Semiring, using 0, used by 101, 0.000369⟩,
⟨Lean.Parser.ParserFn, using 2, used by 111, 0.000368⟩,
⟨Nat.zero, using 1, used by 110, 0.000365⟩,
⟨Lean.Core.Context, using 0, used by 513, 0.000363⟩,
⟨Lean.Level.Data, using 1, used by 117, 0.000362⟩,
⟨System.FilePath, using 0, used by 124, 0.000362⟩,
⟨Nonempty, using 0, used by 59, 0.000360⟩,
⟨HSub, using 1, used by 8, 0.000360⟩,
⟨mixHash, using 1, used by 27, 0.000359⟩,
⟨Lean.JsonRpc.RequestID, using 0, used by 117, 0.000358⟩,
⟨ByteArray, using 0, used by 126, 0.000353⟩,
⟨String.Iterator, using 0, used by 70, 0.000352⟩,
⟨Lean.NameMap, using 3, used by 162, 0.000352⟩,
⟨Preorder, using 0, used by 56, 0.000352⟩,
⟨Std.PersistentHashMap, using 2, used by 142, 0.000349⟩,
⟨Decidable.isTrue, using 1, used by 100, 0.000348⟩,
⟨Lean.JsonRpc.ErrorCode, using 0, used by 73, 0.000348⟩,
⟨Add.mk, using 1, used by 13, 0.000348⟩,
⟨Lean.PrettyPrinter.Formatter.andthen.formatter, using 14, used by 283, 0.000346⟩,
⟨Std.AssocList, using 0, used by 96, 0.000346⟩,
⟨HAdd.mk, using 2, used by 4, 0.000346⟩,
⟨Decidable.isFalse, using 2, used by 99, 0.000345⟩,
⟨congrArg, using 3, used by 422, 0.000342⟩,
⟨Alternative, using 0, used by 29, 0.000341⟩,
⟨Nat.casesOn, using 4, used by 141, 0.000341⟩,
⟨BEq.beq, using 2, used by 426, 0.000340⟩,
⟨propext, using 2, used by 80, 0.000338⟩,
⟨Add.add, using 1, used by 3, 0.000335⟩,
⟨List.rec, using 3, used by 164, 0.000333⟩,
⟨Lean.Meta.DiscrTree.Key, using 0, used by 125, 0.000332⟩,
⟨Std.RBTree, using 3, used by 41, 0.000332⟩,
⟨Empty, using 0, used by 34, 0.000330⟩,
⟨Lean.IR.Decl, using 0, used by 216, 0.000326⟩,
⟨Lean.IR.FunId, using 1, used by 206, 0.000325⟩,
⟨Repr, using 0, used by 86, 0.000325⟩,
⟨Lean.Elab.Info, using 0, used by 164, 0.000324⟩,
⟨instHashableString, using 4, used by 4, 0.000323⟩,
⟨Lean.MacroScope, using 1, used by 257, 0.000323⟩,
⟨Ord.compare, using 2, used by 152, 0.000322⟩,
⟨Lean.ConstantVal, using 0, used by 111, 0.000322⟩,
⟨Lean.IR.Param, using 0, used by 234, 0.000321⟩,
⟨EmptyCollection, using 0, used by 32, 0.000321⟩,
⟨Std.ToFormat, using 0, used by 64, 0.000320⟩,
⟨Prod.rec, using 2, used by 2, 0.000319⟩,
⟨Lean.ParserDescr.unary, using 2, used by 299, 0.000318⟩,
⟨Lean.Parser.Token, using 1, used by 110, 0.000317⟩,
⟨Lean.Elab.Term.State, using 0, used by 468, 0.000316⟩,
⟨Lean.Elab.Term.Do.Code, using 0, used by 117, 0.000314⟩,
⟨inferInstanceAs, using 0, used by 80, 0.000314⟩,
⟨Nat.add, using 10, used by 45, 0.000312⟩,
⟨UInt16, using 0, used by 107, 0.000312⟩,
⟨Nat.rec, using 3, used by 138, 0.000311⟩,
⟨Lean.Lsp.TextDocumentIdentifier, using 0, used by 71, 0.000310⟩,
⟨ReaderT.instMonadLiftReaderT, using 3, used by 846, 0.000309⟩,
⟨Option.rec, using 3, used by 2, 0.000309⟩,
⟨Lean.PrettyPrinter.Parenthesizer.andthen.parenthesizer, using 14, used by 282, 0.000308⟩,
⟨Mem.mem, using 1, used by 210, 0.000307⟩,
⟨MonadControlT, using 0, used by 68, 0.000304⟩,
⟨Lean.Parser.symbol.formatter, using 4, used by 263, 0.000301⟩,
⟨Lean.Parser.symbol.parenthesizer, using 4, used by 263, 0.000301⟩,
⟨List.toArray, using 5, used by 518, 0.000301⟩,
⟨Except.ok, using 1, used by 121, 0.000299⟩,
⟨Lean.FileMap, using 0, used by 130, 0.000299⟩,
⟨Lean.Elab.Term.Context, using 0, used by 449, 0.000296⟩,
⟨Eq.mpr, using 3, used by 377, 0.000296⟩,
⟨Lean.Meta.TransparencyMode, using 0, used by 61, 0.000293⟩,
⟨Ord, using 0, used by 25, 0.000292⟩,
⟨Int.ofNat, using 2, used by 182, 0.000291⟩,
⟨Except.error, using 1, used by 117, 0.000291⟩,
⟨StateT, using 1, used by 111, 0.000290⟩,
⟨Lean.InternalExceptionId, using 0, used by 60, 0.000290⟩,
⟨Lean.Core.instMonadCoreM, using 25, used by 437, 0.000289⟩,
⟨Lean.Widget.TaggedText, using 0, used by 65, 0.000288⟩,
⟨instMonadLiftT_1, using 2, used by 611, 0.000287⟩,
⟨Lean.IR.CtorInfo, using 0, used by 128, 0.000287⟩,
⟨Setoid, using 0, used by 46, 0.000287⟩,
⟨Lean.InductiveVal, using 0, used by 188, 0.000284⟩,
⟨Lean.OpenDecl, using 0, used by 152, 0.000284⟩,
⟨instMonadLiftT, using 5, used by 604, 0.000281⟩,
⟨Semigroup, using 0, used by 42, 0.000281⟩,
⟨USize.size, using 7, used by 87, 0.000278⟩,
⟨IO.Ref, using 2, used by 120, 0.000278⟩,
⟨LT.mk, using 1, used by 24, 0.000277⟩,
⟨Lean.Parser.ParserInfo, using 0, used by 38, 0.000277⟩,
⟨Lean.Meta.FVarSubst, using 0, used by 101, 0.000276⟩,
⟨Or.inr, using 1, used by 157, 0.000276⟩,
⟨Lean.PrettyPrinter.Formatter.withAntiquot.formatter, using 2, used by 280, 0.000275⟩,
⟨Task, using 0, used by 102, 0.000274⟩,
⟨Or.inl, using 1, used by 157, 0.000274⟩,
⟨Lean.PrettyPrinter.Parenthesizer.withAntiquot.parenthesizer, using 2, used by 280, 0.000273⟩,
⟨instHSub, using 4, used by 323, 0.000271⟩,
⟨HSub.hSub, using 1, used by 323, 0.000271⟩,
⟨Lean.IR.UnreachableBranches.Value, using 0, used by 70, 0.000270⟩,
⟨Lean.Parser.mkAntiquot.formatter, using 33, used by 279, 0.000270⟩,
⟨Std.PersistentHashMap.Node, using 0, used by 78, 0.000269⟩,
⟨Lean.Parser.mkAntiquot.parenthesizer, using 33, used by 279, 0.000269⟩,
⟨Lean.Meta.instAlternativeMetaM, using 35, used by 734, 0.000268⟩,
⟨Lean.Parser.Parser.mk, using 3, used by 73, 0.000267⟩,
⟨Lean.PrettyPrinter.Parenthesizer.State, using 0, used by 65, 0.000267⟩,
⟨Zero, using 0, used by 40, 0.000266⟩,
⟨ToString.mk, using 2, used by 89, 0.000266⟩,
⟨HMod, using 1, used by 14, 0.000266⟩,
⟨Neg, using 0, used by 31, 0.000264⟩,
⟨List.instMemList, using 5, used by 186, 0.000261⟩,
⟨Lean.Parser.symbol, using 4, used by 266, 0.000261⟩,
⟨WellFounded, using 0, used by 49, 0.000260⟩,
⟨instHAndThen, using 5, used by 287, 0.000259⟩,
⟨HAndThen.hAndThen, using 2, used by 287, 0.000259⟩,
⟨Lean.Elab.DefKind, using 0, used by 60, 0.000258⟩,
⟨Mod, using 0, used by 16, 0.000258⟩,
⟨Lean.Elab.Modifiers, using 0, used by 135, 0.000258⟩,
⟨ST, using 2, used by 330, 0.000258⟩,
⟨Lean.Parser.instAndThenParser, using 6, used by 285, 0.000258⟩,
⟨Nat.le, using 1, used by 33, 0.000257⟩,
⟨IO.FS.Stream, using 0, used by 111, 0.000256⟩,
⟨Function.left_inverse, using 1, used by 33, 0.000253⟩,
⟨Sum, using 0, used by 40, 0.000252⟩,
⟨BaseIO, using 2, used by 330, 0.000251⟩,
⟨Std.PersistentArrayNode, using 0, used by 115, 0.000249⟩,
⟨Std.PersistentHashMap.Entry, using 0, used by 54, 0.000249⟩,
⟨Lean.Parser.leadingNode.formatter, using 7, used by 269, 0.000247⟩,
⟨Lean.PrettyPrinter.Parenthesizer.leadingNode.parenthesizer, using 49, used by 269, 0.000247⟩,
⟨IO.Process.Stdio, using 0, used by 26, 0.000246⟩,
⟨AddSemigroup, using 0, used by 35, 0.000245⟩,
⟨Lean.Parsec, using 2, used by 114, 0.000243⟩,
⟨MonadExcept, using 1, used by 24, 0.000243⟩,
⟨Std.HashMapImp, using 0, used by 55, 0.000243⟩,
⟨Lean.Meta.Simp.Result, using 0, used by 82, 0.000242⟩,
⟨Lean.Parser.withAntiquot, using 6, used by 281, 0.000241⟩,
⟨MonadLift.mk, using 1, used by 18, 0.000241⟩,
⟨Lean.PrettyPrinter.Formatter.orelse.formatter, using 5, used by 70, 0.000240⟩,
⟨Std.RBNode.WellFormed, using 2, used by 41, 0.000240⟩,
⟨Lean.PrettyPrinter.Parenthesizer.orelse.parenthesizer, using 32, used by 70, 0.000240⟩,
⟨Lean.ParserDescr.const, using 2, used by 215, 0.000239⟩,
⟨Id.instMonadId, using 14, used by 230, 0.000238⟩,
⟨Subtype.val, using 1, used by 95, 0.000237⟩,
⟨Lean.Parser.mkAntiquot, using 39, used by 281, 0.000237⟩,
⟨IO.Process.StdioConfig, using 0, used by 39, 0.000237⟩,
⟨Lean.Meta.Match.Pattern, using 0, used by 89, 0.000237⟩,
⟨Lean.Parser.LeadingIdentBehavior, using 0, used by 68, 0.000235⟩,
⟨Lean.Elab.Term.Do.ToTerm.Kind, using 0, used by 41, 0.000234⟩,
⟨Lean.Name.hash, using 10, used by 3, 0.000232⟩,
⟨Div, using 0, used by 26, 0.000231⟩,
⟨Lean.PrettyPrinter.Parenthesizer.Context, using 0, used by 55, 0.000230⟩,
⟨Lean.PrettyPrinter.Formatter.State, using 0, used by 71, 0.000230⟩,
⟨Semigroup.toMul, using 2, used by 202, 0.000229⟩,
⟨instMonadEIO, using 6, used by 510, 0.000229⟩,
⟨Lean.EnvExtensionInterface, using 0, used by 19, 0.000229⟩,
⟨Lean.MData, using 1, used by 248, 0.000228⟩,
⟨Lean.PersistentEnvExtension, using 0, used by 75, 0.000227⟩,
⟨Lean.PrettyPrinter.Formatter.Context, using 0, used by 68, 0.000226⟩,
⟨Lean.Elab.ContextInfo, using 0, used by 113, 0.000226⟩,
⟨Lean.SMap, using 2, used by 101, 0.000225⟩,
⟨One, using 0, used by 26, 0.000225⟩,
⟨Subtype.mk, using 1, used by 81, 0.000225⟩,
⟨Lean.Parser.AliasValue, using 0, used by 31, 0.000224⟩,
⟨Quot, using 0, used by 21, 0.000224⟩,
⟨Repr.mk, using 3, used by 74, 0.000224⟩,
⟨DoResultPR, using 0, used by 44, 0.000223⟩,
⟨absurd, using 2, used by 105, 0.000222⟩,
⟨Lean.Parser.FirstTokens, using 0, used by 41, 0.000222⟩,
⟨instMulNat, using 4, used by 218, 0.000221⟩,
⟨StateRefT'.instMonadLiftStateRefT', using 4, used by 698, 0.000220⟩,
⟨Lean.FVarIdSet, using 4, used by 91, 0.000219⟩,
⟨UInt32.size, using 3, used by 85, 0.000219⟩,
⟨Lean.JsonNumber, using 0, used by 86, 0.000219⟩,
⟨FloatSpec, using 0, used by 16, 0.000218⟩,
⟨instOrdNat, using 7, used by 101, 0.000217⟩,
⟨Eq.trans, using 2, used by 319, 0.000217⟩,
⟨Lean.IR.AltCore, using 0, used by 80, 0.000217⟩,
⟨instBEq, using 5, used by 268, 0.000217⟩,
⟨Lean.NameGenerator, using 0, used by 82, 0.000216⟩,
⟨dite, using 3, used by 175, 0.000215⟩,
⟨Lean.LBool, using 0, used by 36, 0.000215⟩,
⟨Lean.IR.JoinPointId, using 0, used by 118, 0.000215⟩,
⟨instSubNat, using 4, used by 271, 0.000214⟩,
⟨Lean.Parser.leadingNode, using 10, used by 269, 0.000214⟩,
⟨SeqRight, using 0, used by 14, 0.000212⟩,
⟨Lean.Lsp.Position, using 0, used by 53, 0.000211⟩,
⟨Lean.AttributeKind, using 0, used by 60, 0.000211⟩,
⟨MonadLiftT.mk, using 1, used by 8, 0.000211⟩,
⟨liftM, using 2, used by 383, 0.000210⟩,
⟨MProd.mk, using 1, used by 125, 0.000210⟩,
⟨Lean.LOption, using 0, used by 34, 0.000209⟩,
⟨Monoid, using 0, used by 47, 0.000209⟩,
⟨IO.AsyncList, using 0, used by 57, 0.000208⟩,
⟨List.length, using 17, used by 81, 0.000205⟩,
⟨Lean.MonadRef, using 0, used by 47, 0.000205⟩,
⟨HAndThen, using 1, used by 8, 0.000204⟩,
⟨WellFoundedRelation, using 0, used by 23, 0.000204⟩,
⟨UInt64.size, using 3, used by 75, 0.000203⟩,
⟨Lean.Parsec.ParseResult, using 0, used by 27, 0.000203⟩,
⟨Lean.Meta.Simp.Config, using 0, used by 51, 0.000202⟩,
⟨Lean.Meta.Match.Example, using 0, used by 57, 0.000202⟩,
⟨Lean.Position, using 0, used by 73, 0.000200⟩,
⟨ToString.toString, using 2, used by 227, 0.000200⟩,
⟨And.rec, using 2, used by 4, 0.000199⟩,
⟨Lean.MetavarKind, using 0, used by 42, 0.000199⟩,
⟨MonadState, using 1, used by 19, 0.000199⟩,
⟨Lean.ExprStructEq, using 0, used by 78, 0.000199⟩,
⟨Lean.Meta.Simp.Context, using 0, used by 100, 0.000199⟩,
⟨Lean.Elab.Command.State, using 0, used by 140, 0.000199⟩,
⟨Lean.TagAttribute, using 0, used by 26, 0.000199⟩,
⟨Lean.ParserDescr.parser, using 2, used by 190, 0.000199⟩,
⟨Lean.MessageSeverity, using 0, used by 38, 0.000198⟩,
⟨Equiv, using 0, used by 32, 0.000198⟩,
⟨Lean.Meta.Config, using 0, used by 50, 0.000197⟩,
⟨Preorder.toLE, using 2, used by 109, 0.000197⟩,
⟨Decidable.decide, using 6, used by 158, 0.000197⟩,
⟨instSizeOfName, using 4, used by 219, 0.000195⟩,
⟨Ne, using 2, used by 113, 0.000194⟩,
⟨Nat.lt, using 3, used by 6, 0.000193⟩,
⟨Lean.Server.WithRpcRef, using 0, used by 50, 0.000192⟩,
⟨False.elim, using 2, used by 50, 0.000190⟩,
⟨Lean.ReducibilityHints, using 0, used by 48, 0.000190⟩,
⟨Lean.Elab.Visibility, using 0, used by 39, 0.000189⟩,
⟨Nat.decLt, using 6, used by 221, 0.000189⟩,
⟨AddSemigroup.toAdd, using 2, used by 177, 0.000188⟩,
⟨OrElse, using 0, used by 19, 0.000187⟩,
⟨Lean.ToMessageData, using 0, used by 21, 0.000187⟩,
⟨UInt8.size, using 3, used by 73, 0.000187⟩,
⟨Lean.PrefixTreeNode, using 0, used by 44, 0.000186⟩,
⟨Lean.Syntax.Traverser, using 0, used by 59, 0.000185⟩,
⟨MonadReaderOf, using 0, used by 28, 0.000184⟩,
⟨Lean.ConstructorVal, using 0, used by 120, 0.000183⟩,
⟨Subsingleton, using 0, used by 38, 0.000183⟩,
⟨Array.data, using 2, used by 15, 0.000183⟩,
⟨UInt16.size, using 3, used by 71, 0.000182⟩,
⟨Lean.Meta.Match.MatcherInfo, using 0, used by 75, 0.000182⟩,
⟨Lean.JsonRpc.Message, using 0, used by 90, 0.000181⟩,
⟨Dvd, using 0, used by 8, 0.000181⟩,
⟨Except.casesOn, using 4, used by 75, 0.000181⟩,
⟨Lean.Elab.Command.StructFieldKind, using 0, used by 31, 0.000181⟩,
⟨Int.negSucc, using 2, used by 113, 0.000181⟩,
⟨instHOrElse, using 5, used by 120, 0.000181⟩,
⟨HOrElse.hOrElse, using 2, used by 120, 0.000181⟩,
⟨Lean.ImportM.Context, using 0, used by 209, 0.000180⟩,
⟨Lean.ImportM, using 3, used by 240, 0.000180⟩,
⟨AndThen, using 0, used by 12, 0.000180⟩,
⟨MonadFunctor, using 0, used by 19, 0.000180⟩,
⟨Applicative.toFunctor, using 2, used by 182, 0.000179⟩,
⟨Equivalence, using 0, used by 19, 0.000179⟩,
⟨Nat.below, using 4, used by 110, 0.000179⟩,
⟨Lean.DefinitionVal, using 0, used by 92, 0.000179⟩,
⟨MonadStateOf, using 0, used by 21, 0.000179⟩,
⟨String.instAppendString, using 4, used by 213, 0.000178⟩,
⟨Lean.QuotKind, using 0, used by 30, 0.000178⟩,
⟨Set, using 0, used by 40, 0.000177⟩,
⟨Lean.Declaration, using 0, used by 80, 0.000177⟩,
⟨Lean.Expr.instBEqExpr, using 4, used by 144, 0.000177⟩,
⟨Coe.mk, using 1, used by 61, 0.000177⟩,
⟨Lean.Compiler.SpecArgKind, using 0, used by 28, 0.000176⟩,
⟨of_eq_true, using 5, used by 273, 0.000176⟩,
⟨Exists.casesOn, using 3, used by 69, 0.000175⟩,
⟨HEq.rec, using 2, used by 5, 0.000175⟩,
⟨Array.mk, using 2, used by 86, 0.000175⟩,
⟨or, using 4, used by 168, 0.000175⟩,
⟨List.below, using 4, used by 124, 0.000175⟩,
⟨Lean.Expr.instHashableExpr, using 4, used by 125, 0.000174⟩,
⟨Lean.LocalInstances, using 2, used by 97, 0.000174⟩,
⟨Lean.Elab.Term.StructInst.FieldVal, using 0, used by 44, 0.000174⟩,
⟨Lean.AttributeImpl, using 0, used by 94, 0.000174⟩,
⟨Lean.Server.Watchdog.WorkerEvent, using 0, used by 53, 0.000174⟩,
⟨Lean.DefinitionSafety, using 0, used by 45, 0.000174⟩,
⟨Lean.Lsp.TextDocumentSyncKind, using 0, used by 35, 0.000173⟩,
⟨Lean.KernelException, using 0, used by 75, 0.000173⟩,
⟨LE.mk, using 1, used by 17, 0.000173⟩,
⟨Std.RBNode.leaf, using 1, used by 71, 0.000172⟩,
⟨Bool.casesOn, using 4, used by 64, 0.000171⟩,
⟨Lean.MetavarDecl, using 0, used by 94, 0.000171⟩,
⟨Iff.mp, using 1, used by 66, 0.000171⟩,
⟨HasEquiv, using 0, used by 10, 0.000171⟩,
⟨ReprAtom, using 0, used by 18, 0.000171⟩,
⟨Lean.HeadIndex, using 0, used by 42, 0.000171⟩,
⟨Lean.Meta.CongrArgKind, using 0, used by 29, 0.000170⟩,
⟨HMod.hMod, using 1, used by 145, 0.000170⟩,
⟨Lean.Elab.ElabInfo, using 0, used by 52, 0.000169⟩,
⟨Lean.RecursorVal, using 0, used by 75, 0.000168⟩,
⟨Lean.Parser.maxPrec, using 3, used by 99, 0.000168⟩,
⟨Append.mk, using 1, used by 14, 0.000168⟩,
⟨Lean.Parser.InputContext, using 0, used by 54, 0.000168⟩,
⟨Function.injective, using 1, used by 60, 0.000167⟩,
⟨Iff.mpr, using 1, used by 66, 0.000167⟩,
⟨Lean.Widget.CodeWithInfos, using 2, used by 74, 0.000167⟩,
⟨instSizeOfNat, using 3, used by 169, 0.000167⟩,
⟨GT.gt, using 2, used by 185, 0.000165⟩,
⟨MonadLiftT.monadLift, using 1, used by 7, 0.000165⟩,
⟨Lean.MonadEnv, using 0, used by 96, 0.000165⟩,
⟨HPow, using 1, used by 10, 0.000165⟩,
⟨Std.HashSetImp, using 0, used by 44, 0.000165⟩,
⟨Lean.Lsp.DiagnosticSeverity, using 0, used by 32, 0.000165⟩,
⟨Fin.mk, using 4, used by 111, 0.000165⟩,
⟨Nat.brecOn, using 9, used by 109, 0.000163⟩,
⟨Lean.KeyedDeclsAttribute, using 0, used by 39, 0.000163⟩,
⟨Lean.Elab.InfoTree, using 0, used by 88, 0.000163⟩,
⟨Std.Format.FlattenBehavior, using 0, used by 29, 0.000163⟩,
⟨Lean.MacroM, using 5, used by 111, 0.000163⟩,
⟨Subarray, using 0, used by 75, 0.000163⟩,
⟨IO.FS.FileType, using 0, used by 27, 0.000163⟩,
⟨cast, using 2, used by 5, 0.000162⟩,
⟨Numeric, using 0, used by 25, 0.000162⟩,
⟨Subset, using 0, used by 9, 0.000161⟩,
⟨Lean.Elab.RecKind, using 0, used by 34, 0.000161⟩,
⟨Nat.gcd, using 6, used by 94, 0.000161⟩,
⟨Lean.Name.num, using 3, used by 106, 0.000161⟩,
⟨Functor.map, using 1, used by 136, 0.000160⟩,
⟨Lean.Server.Snapshots.Snapshot, using 0, used by 73, 0.000160⟩,
⟨List.brecOn, using 9, used by 123, 0.000160⟩,
⟨Lean.Lsp.FileSource, using 0, used by 34, 0.000160⟩,
⟨MonadWithReaderOf, using 0, used by 27, 0.000160⟩,
⟨Fin.val, using 2, used by 88, 0.000159⟩,
⟨and, using 4, used by 200, 0.000159⟩,
⟨Std.ToFormat.mk, using 2, used by 47, 0.000158⟩,
⟨PartialOrder, using 0, used by 27, 0.000158⟩,
⟨Lean.Lsp.VersionedTextDocumentIdentifier, using 0, used by 48, 0.000158⟩,
⟨Lean.Elab.WF.TerminationHint, using 0, used by 37, 0.000157⟩,
⟨StateM, using 2, used by 73, 0.000157⟩,
⟨HDiv, using 1, used by 9, 0.000157⟩,
⟨Lean.ScopedEnvExtension.Entry, using 0, used by 49, 0.000157⟩,
⟨Lean.AttributeApplicationTime, using 0, used by 30, 0.000157⟩,
⟨Lean.MessageLog, using 0, used by 77, 0.000156⟩,
⟨Lean.Elab.Term.TermElab, using 4, used by 74, 0.000156⟩,
⟨Lean.Message, using 0, used by 64, 0.000156⟩,
⟨Lean.TraceState, using 0, used by 53, 0.000156⟩,
⟨Lean.Compiler.InlineAttributeKind, using 0, used by 19, 0.000156⟩,
⟨Lean.Expr.app, using 2, used by 225, 0.000156⟩,
⟨Pow, using 0, used by 10, 0.000156⟩,
⟨Lean.Elab.Term.Do.CodeBlock, using 0, used by 53, 0.000155⟩,
⟨instHMod, using 4, used by 137, 0.000155⟩,
⟨LinearOrder, using 0, used by 64, 0.000155⟩,
⟨Lean.Elab.Term.Arg, using 0, used by 65, 0.000155⟩,
⟨Lean.Lsp.RpcRef, using 0, used by 55, 0.000154⟩,
⟨HOrElse, using 1, used by 8, 0.000154⟩,
⟨Preorder.toLT, using 2, used by 92, 0.000154⟩,
⟨TC, using 0, used by 14, 0.000153⟩,
⟨MonadFunctorT, using 0, used by 12, 0.000153⟩,
⟨AddMonoid, using 0, used by 32, 0.000152⟩,
⟨Lean.Parser.SyntaxNodeKindSet, using 5, used by 54, 0.000152⟩,
⟨EStateM.Result.ok, using 1, used by 40, 0.000152⟩,
⟨SeqLeft, using 0, used by 14, 0.000151⟩,
⟨Lean.Meta.SimpLemma, using 0, used by 59, 0.000150⟩,
⟨EStateM.instMonadEStateM, using 18, used by 188, 0.000150⟩,
⟨congrFun, using 3, used by 239, 0.000150⟩,
⟨Lean.Elab.Term.StructInst.Struct, using 0, used by 63, 0.000150⟩,
⟨Seq, using 0, used by 14, 0.000150⟩,
⟨Lean.AxiomVal, using 0, used by 71, 0.000149⟩,
⟨Lean.Parser.Parser.fn, using 2, used by 36, 0.000149⟩,
⟨PointedType.type, using 1, used by 15, 0.000149⟩,
⟨SizeOf.mk, using 2, used by 6, 0.000149⟩,
⟨Lean.Expr.forallE, using 3, used by 220, 0.000149⟩,
⟨Lean.MonadQuotation, using 0, used by 23, 0.000149⟩,
⟨Lean.Level.PP.Result, using 0, used by 39, 0.000148⟩,
⟨Lean.Expr.lam, using 3, used by 219, 0.000148⟩,
⟨Lean.Expr.bvar, using 3, used by 208, 0.000148⟩,
⟨Lean.ReducibilityStatus, using 0, used by 22, 0.000148⟩,
⟨Lean.Expr.mdata, using 3, used by 219, 0.000148⟩,
⟨Lean.Expr.const, using 5, used by 214, 0.000148⟩,
⟨Sigma, using 0, used by 25, 0.000148⟩,
⟨Lean.Macro.Context, using 0, used by 93, 0.000148⟩,
⟨noConfusionTypeEnum, using 3, used by 43, 0.000147⟩,
⟨Applicative.toSeqRight, using 2, used by 87, 0.000147⟩,
⟨Lean.Syntax.node, using 4, used by 231, 0.000147⟩,
⟨Lean.Elab.Tactic.TacticM, using 6, used by 163, 0.000147⟩,
⟨Mathlib.Tactic.Lint.LintVerbosity, using 0, used by 21, 0.000147⟩,
⟨ShiftLeft, using 0, used by 15, 0.000146⟩,
⟨Lean.LocalInstance, using 0, used by 46, 0.000146⟩,
⟨Lean.Elab.TacticInfo, using 0, used by 59, 0.000146⟩,
⟨ShiftRight, using 0, used by 15, 0.000146⟩,
⟨ExceptT, using 1, used by 86, 0.000146⟩,
⟨instMonadExceptOfEIO, using 8, used by 474, 0.000145⟩,
⟨Lean.Expr.letE, using 3, used by 216, 0.000145⟩,
⟨CoeT, using 0, used by 13, 0.000144⟩,
⟨Std.RBNode.node, using 2, used by 63, 0.000144⟩,
⟨Lean.Expr.proj, using 4, used by 215, 0.000144⟩,
⟨Lean.Lsp.DocumentHighlightKind, using 0, used by 24, 0.000144⟩,
⟨Lean.Elab.Tactic.State, using 0, used by 142, 0.000144⟩,
⟨Lean.IR.LocalContext, using 5, used by 70, 0.000144⟩,
⟨Lean.Expr.sort, using 3, used by 210, 0.000144⟩,
⟨MonadControl, using 0, used by 17, 0.000143⟩,
⟨FloatArray, using 0, used by 50, 0.000143⟩,
⟨EST, using 1, used by 8, 0.000143⟩,
⟨Function.right_inverse, using 1, used by 34, 0.000143⟩,
⟨Lean.PrettyPrinter.Delaborator.SubExpr, using 0, used by 57, 0.000143⟩,
⟨Lean.DeclarationRange, using 0, used by 34, 0.000143⟩,
⟨Lean.Parser.Error, using 0, used by 62, 0.000142⟩,
⟨Lean.Server.FileWorker.ElabTaskError, using 0, used by 42, 0.000142⟩,
⟨Lean.Widget.CodeToken, using 0, used by 33, 0.000142⟩,
⟨CoeTail, using 0, used by 16, 0.000142⟩,
⟨Lean.Syntax.missing, using 1, used by 132, 0.000141⟩,
⟨Lean.Expr.fvar, using 3, used by 209, 0.000141⟩,
⟨Lean.Expr.lit, using 3, used by 209, 0.000141⟩,
⟨Lean.OpaqueVal, using 0, used by 70, 0.000141⟩,
⟨PSigma.mk, using 1, used by 25, 0.000140⟩,
⟨Lean.Name.beq, using 23, used by 1, 0.000140⟩,
⟨Std.PHashMap, using 3, used by 68, 0.000140⟩,
⟨Lean.Expr.mvar, using 3, used by 207, 0.000140⟩,
⟨Nat.instModNat, using 4, used by 126, 0.000140⟩,
⟨Lean.Json.CompressWorkItem, using 0, used by 26, 0.000140⟩,
⟨Lean.Lsp.MarkupKind, using 0, used by 23, 0.000139⟩,
⟨Lean.Parser.Parser.info, using 2, used by 30, 0.000139⟩,
⟨Std.Format.text, using 2, used by 89, 0.000139⟩,
⟨instMonadLiftBaseIOEIO, using 5, used by 302, 0.000139⟩,
⟨trivial, using 2, used by 32, 0.000139⟩,
⟨Lean.Lsp.Trace, using 0, used by 26, 0.000139⟩,
⟨Lean.StructureFieldInfo, using 0, used by 45, 0.000138⟩,
⟨CoeTC, using 0, used by 14, 0.000138⟩,
⟨Lean.Meta.DiscrTree, using 0, used by 63, 0.000138⟩,
⟨Nat.decEq, using 13, used by 1, 0.000138⟩,
⟨Function.surjective, using 2, used by 45, 0.000137⟩,
⟨HMul.mk, using 2, used by 4, 0.000137⟩,
⟨MonadReader, using 1, used by 8, 0.000137⟩,
⟨Lean.SimplePersistentEnvExtension, using 3, used by 32, 0.000137⟩,
⟨OrOp, using 0, used by 15, 0.000137⟩,
⟨Lean.Elab.InfoState, using 0, used by 63, 0.000137⟩,
⟨Lean.Elab.TermInfo, using 0, used by 70, 0.000137⟩,
⟨instMonadExcept, using 6, used by 246, 0.000136⟩,
⟨Lean.Meta.Simp.Step, using 0, used by 43, 0.000136⟩,
⟨Inv, using 0, used by 15, 0.000136⟩,
⟨AndOp, using 0, used by 15, 0.000136⟩,
⟨Xor, using 0, used by 15, 0.000136⟩,
⟨Mul.mk, using 1, used by 13, 0.000136⟩,
⟨EStateM.Result.error, using 1, used by 35, 0.000136⟩,
⟨Lean.EnvExtension, using 2, used by 35, 0.000136⟩,
⟨IO.AccessRight, using 0, used by 25, 0.000136⟩,
⟨Lean.Elab.CompletionInfo, using 0, used by 66, 0.000136⟩,
⟨Lean.IR.IndexSet, using 4, used by 37, 0.000136⟩,
⟨Lean.Parser.ModuleParserState, using 0, used by 57, 0.000135⟩,
⟨CoeHTCT, using 0, used by 14, 0.000135⟩,
⟨Prod.fst, using 1, used by 108, 0.000135⟩,
⟨instMonadState, using 7, used by 239, 0.000135⟩,
⟨Classical.propDecidable, using 3, used by 45, 0.000135⟩,
⟨Lean.Macro.Exception, using 0, used by 94, 0.000134⟩,
⟨Lean.Syntax.atom, using 3, used by 214, 0.000134⟩,
⟨Std.HashMapImp.WellFormed, using 3, used by 30, 0.000134⟩,
⟨ReaderT.instMonadExceptOfReaderT, using 10, used by 456, 0.000134⟩,
⟨Lean.KeyedDeclsAttribute.OLeanEntry, using 0, used by 39, 0.000134⟩,
⟨MProd.casesOn, using 3, used by 49, 0.000134⟩,
⟨ForInStep.yield, using 1, used by 199, 0.000133⟩,
⟨Lean.Elab.Term.LetRecToLift, using 0, used by 48, 0.000133⟩,
⟨Lean.TheoremVal, using 0, used by 68, 0.000133⟩,
⟨IO.FS.Mode, using 0, used by 16, 0.000133⟩,
⟨Char.ofNat, using 19, used by 110, 0.000133⟩,
⟨PartialOrder.toPreorder, using 2, used by 93, 0.000132⟩,
⟨eq_self, using 6, used by 195, 0.000132⟩,
⟨Pure.mk, using 1, used by 18, 0.000131⟩,
⟨Bind.mk, using 1, used by 18, 0.000131⟩,
⟨Lean.Meta.ReduceMatcherResult, using 0, used by 23, 0.000131⟩,
⟨Lean.IR.LitVal, using 0, used by 59, 0.000130⟩,
⟨Lean.ScopedEnvExtension.Descr, using 0, used by 31, 0.000130⟩,
⟨not, using 5, used by 177, 0.000130⟩,
⟨Lean.PrettyPrinter.Parenthesizer.visitToken, using 41, used by 14, 0.000130⟩,
⟨IO.instMonadLiftSTRealWorldBaseIO, using 6, used by 283, 0.000130⟩,
⟨Lean.SearchPath, using 1, used by 41, 0.000130⟩,
⟨Lean.Lsp.DiagnosticTag, using 0, used by 28, 0.000130⟩,
⟨Lean.Elab.Attribute, using 0, used by 68, 0.000130⟩,
⟨Lean.Expr.casesOn, using 23, used by 197, 0.000130⟩,
⟨Lean.Lsp.TextDocumentItem, using 0, used by 29, 0.000130⟩,
⟨HAppend.mk, using 2, used by 5, 0.000129⟩,
⟨System.SearchPath, using 2, used by 5, 0.000129⟩,
⟨Lean.PersistentEnvExtensionState, using 0, used by 30, 0.000129⟩,
⟨Lean.Parser.Trie, using 0, used by 28, 0.000129⟩,
⟨True.intro, using 1, used by 26, 0.000129⟩,
⟨Lean.Elab.WF.TerminationHintValue, using 0, used by 35, 0.000128⟩,
⟨Lean.ExternAttrData, using 0, used by 69, 0.000128⟩,
⟨panicWithPosWithDecl, using 4, used by 127, 0.000127⟩,
⟨Mul.mul, using 1, used by 3, 0.000127⟩,
⟨Lean.Server.DocumentMeta, using 0, used by 47, 0.000126⟩,
⟨Lean.ParserDescr.trailingNode, using 3, used by 88, 0.000126⟩,
⟨Lean.IR.CtorFieldInfo, using 0, used by 32, 0.000125⟩,
⟨Std.MonadShareCommon, using 0, used by 11, 0.000125⟩,
⟨ulift, using 0, used by 12, 0.000125⟩,
⟨plift, using 0, used by 12, 0.000125⟩,
⟨Or.casesOn, using 4, used by 96, 0.000124⟩,
⟨Lean.instHashableMVarId, using 3, used by 96, 0.000124⟩,
⟨Lean.Lsp.CompletionItem, using 0, used by 37, 0.000124⟩,
⟨Sub.mk, using 1, used by 13, 0.000124⟩,
⟨Lean.PrettyPrinter.Delaborator.Pos, using 1, used by 70, 0.000124⟩,
⟨Function.const, using 0, used by 39, 0.000124⟩,
⟨Lean.IR.EmitC.Context, using 0, used by 79, 0.000124⟩,
⟨Std.HashSet, using 5, used by 47, 0.000123⟩,
⟨Lean.Lsp.LineRange, using 0, used by 28, 0.000123⟩,
⟨Lean.Elab.Term.StructInst.Source, using 0, used by 42, 0.000123⟩,
⟨Lean.Meta.SynthInstance.ConsumerNode, using 0, used by 45, 0.000123⟩,
⟨MonadExcept.throw, using 1, used by 168, 0.000123⟩,
⟨Lean.instBEqMVarId, using 3, used by 101, 0.000123⟩,
⟨AddCommSemigroup, using 0, used by 26, 0.000122⟩,
⟨CoeHead, using 0, used by 12, 0.000122⟩,
⟨Lean.IR.DeclInfo, using 0, used by 73, 0.000122⟩,
⟨DoResultPRBC, using 0, used by 13, 0.000122⟩,
⟨Lean.MonadError, using 0, used by 64, 0.000122⟩,
⟨Nat.decLe, using 15, used by 105, 0.000122⟩,
⟨Lean.ExternEntry, using 0, used by 42, 0.000122⟩,
⟨CoeDep, using 0, used by 12, 0.000121⟩,
⟨Lean.Elab.Command.Context, using 0, used by 107, 0.000121⟩,
⟨Lean.Lsp.SemanticTokenType, using 0, used by 16, 0.000121⟩,
⟨Lean.SourceInfo.none, using 1, used by 182, 0.000121⟩,
⟨ReaderT.instAlternativeReaderT, using 8, used by 325, 0.000121⟩,
⟨Lean.ScopedEnvExtension, using 0, used by 29, 0.000120⟩,
⟨Lean.TrailingParserDescr, using 1, used by 79, 0.000120⟩,
⟨Lean.Elab.Term.instMonadTermElabM, using 28, used by 352, 0.000120⟩,
⟨ULift, using 0, used by 11, 0.000120⟩,
⟨Lean.Lsp.ServerCapabilities, using 0, used by 31, 0.000120⟩,
⟨Lean.ScopedEnvExtension.State, using 0, used by 35, 0.000120⟩,
⟨Monad.mk, using 3, used by 18, 0.000120⟩,
⟨StateRefT'.instMonadExceptOfStateRefT', using 8, used by 418, 0.000119⟩,
⟨Lean.Lsp.MarkupContent, using 0, used by 34, 0.000119⟩,
⟨Complement, using 0, used by 12, 0.000119⟩,
⟨UInt64.mk, using 3, used by 59, 0.000119⟩,
⟨Id.run, using 1, used by 43, 0.000119⟩,
⟨Lean.Elab.Term.MVarErrorKind, using 0, used by 28, 0.000118⟩,
⟨Lean.Lsp.DiagnosticWith, using 0, used by 23, 0.000118⟩,
⟨Lean.Meta.Simp.SimpLetCase, using 0, used by 14, 0.000118⟩,
⟨Lean.Elab.FieldInfo, using 0, used by 50, 0.000118⟩,
⟨Lean.QuotVal, using 0, used by 57, 0.000117⟩,
⟨USize.mk, using 3, used by 61, 0.000117⟩,
⟨Neg.neg, using 1, used by 105, 0.000117⟩,
⟨UInt32.mk, using 3, used by 62, 0.000117⟩,
⟨Lean.Parser.TokenTable, using 2, used by 40, 0.000117⟩,
⟨SeqRight.seqRight, using 2, used by 82, 0.000117⟩,
⟨EmptyCollection.emptyCollection, using 1, used by 158, 0.000117⟩,
⟨Lean.ExprSet, using 4, used by 46, 0.000116⟩,
⟨Lean.Widget.InteractiveGoal, using 0, used by 45, 0.000116⟩,
⟨Lean.KVMap.Value, using 0, used by 23, 0.000116⟩,
⟨Lean.Xml.Content, using 0, used by 39, 0.000116⟩,
⟨Lean.Parser.ParserCache, using 0, used by 42, 0.000116⟩,
⟨Lean.Compiler.SpecializeAttributeKind, using 0, used by 13, 0.000115⟩,
⟨Array.mkEmpty, using 4, used by 63, 0.000115⟩,
⟨Lean.Elab.Tactic.Context, using 0, used by 132, 0.000115⟩,
⟨Applicative.mk, using 6, used by 18, 0.000115⟩,
⟨Lean.Meta.SynthInstance.Waiter, using 0, used by 28, 0.000115⟩,
⟨Array.push, using 4, used by 168, 0.000115⟩,
⟨False.rec, using 1, used by 3, 0.000114⟩,
⟨DivInvMonoid, using 0, used by 28, 0.000114⟩,
⟨Lean.Meta.Cache, using 0, used by 35, 0.000114⟩,
⟨PSum, using 0, used by 14, 0.000114⟩,
⟨instToStringString, using 3, used by 174, 0.000114⟩,
⟨Prod.snd, using 1, used by 85, 0.000114⟩,
⟨Lean.Compiler.atMostOnce.AtMostOnceData, using 0, used by 19, 0.000114⟩,
⟨Lean.mkConst, using 24, used by 149, 0.000114⟩,
⟨PLift, using 0, used by 9, 0.000113⟩,
⟨IO.FS.SystemTime, using 0, used by 28, 0.000113⟩,
⟨Lean.Elab.Term.SavedState, using 0, used by 39, 0.000113⟩,
⟨Lean.Server.FileWorker.GoToKind, using 0, used by 14, 0.000113⟩,
⟨Lean.Elab.Term.StructInst.FieldLHS, using 0, used by 50, 0.000113⟩,
⟨Lean.AddMessageContext, using 0, used by 40, 0.000113⟩,
⟨Lean.Elab.Term.SyntheticMVarKind, using 0, used by 34, 0.000113⟩,
⟨Lean.Export.Entry, using 0, used by 36, 0.000112⟩,
⟨Append.append, using 1, used by 1, 0.000112⟩,
⟨Lean.Parser.TokenCacheEntry, using 0, used by 24, 0.000112⟩,
⟨Lean.ParametricAttribute, using 0, used by 27, 0.000112⟩,
⟨Ring, using 0, used by 34, 0.000112⟩,
⟨Lean.Elab.MacroExpansionInfo, using 0, used by 42, 0.000111⟩,
⟨Lean.Elab.CommandInfo, using 0, used by 40, 0.000111⟩,
⟨Lean.MonadError.mk, using 5, used by 365, 0.000111⟩,
⟨Lean.Lsp.Location, using 0, used by 27, 0.000111⟩,
⟨Lean.Meta.AbstractMVarsResult, using 0, used by 48, 0.000111⟩,
⟨Lean.KVMap.instValueBool, using 9, used by 69, 0.000111⟩,
⟨Lean.Name.casesOn, using 8, used by 77, 0.000111⟩,
⟨StateRefT'.instAlternativeStateRefT', using 7, used by 335, 0.000111⟩,
⟨EmptyCollection.mk, using 1, used by 23, 0.000110⟩,
⟨List.instAppendList, using 4, used by 101, 0.000110⟩,
⟨Lean.Parser.termParser.formatter, using 8, used by 102, 0.000110⟩,
⟨Lean.Parser.termParser.parenthesizer, using 8, used by 102, 0.000110⟩,
⟨instInhabitedNat, using 4, used by 82, 0.000110⟩,
⟨Lean.ParserDescr.nodeWithAntiquot, using 3, used by 53, 0.000109⟩,
⟨Lean.instInhabitedName, using 4, used by 107, 0.000109⟩,
⟨Lean.MonadOptions, using 0, used by 44, 0.000109⟩,
⟨instSizeOf, using 3, used by 116, 0.000109⟩,
⟨Lean.Meta.ApplyNewGoals, using 0, used by 12, 0.000108⟩,
⟨UInt8.mk, using 3, used by 59, 0.000108⟩,
⟨Lean.Syntax.getOp, using 3, used by 174, 0.000108⟩,
⟨Setoid.r, using 1, used by 17, 0.000108⟩,
⟨Lean.KVMap.get, using 5, used by 47, 0.000108⟩,
⟨Lean.Meta.Simp.SimpM, using 6, used by 47, 0.000108⟩,
⟨UInt16.mk, using 3, used by 59, 0.000108⟩,
⟨Lean.Import, using 0, used by 48, 0.000107⟩,
⟨Lean.Elab.Term.Quotation.HeadCheck, using 0, used by 30, 0.000107⟩,
⟨Lean.Elab.MacroStackElem, using 0, used by 24, 0.000107⟩,
⟨Lean.KeyedDeclsAttribute.AttributeEntry, using 0, used by 26, 0.000107⟩,
⟨DoResultSBC, using 0, used by 11, 0.000107⟩,
⟨Lean.IR.LocalContextEntry, using 0, used by 39, 0.000107⟩,
⟨Lean.NamePart, using 0, used by 24, 0.000107⟩,
⟨Lean.Lsp.DocumentSymbolAux, using 0, used by 32, 0.000107⟩,
⟨EStateM.Backtrackable, using 1, used by 14, 0.000107⟩,
⟨Lean.Elab.Term.StructInst.Field, using 0, used by 48, 0.000107⟩,
⟨List.Perm, using 1, used by 22, 0.000107⟩,
⟨Lean.Meta.DefEqContext, using 0, used by 46, 0.000106⟩,
⟨SubNegMonoid, using 0, used by 21, 0.000106⟩,
⟨Lean.Meta.RecursorInfo, using 0, used by 28, 0.000106⟩,
⟨String.mk, using 3, used by 29, 0.000106⟩,
⟨Functor.mk, using 1, used by 15, 0.000106⟩,
⟨Lean.ToMessageData.toMessageData, using 2, used by 300, 0.000106⟩,
⟨congr, using 3, used by 177, 0.000106⟩,
⟨Lean.Meta.RecursorUnivLevelPos, using 0, used by 26, 0.000106⟩,
⟨instOfNat, using 4, used by 113, 0.000106⟩,
⟨Lean.Macro.State, using 0, used by 91, 0.000105⟩,
⟨Lean.PrettyPrinter.Delaborator.SubExpr.HoleIterator, using 0, used by 30, 0.000105⟩,
⟨Lean.Elab.PreDefinition, using 0, used by 45, 0.000105⟩,
⟨Lean.Meta.UnificationConstraint, using 0, used by 23, 0.000105⟩,
⟨Std.Range, using 0, used by 61, 0.000105⟩,
⟨StdGen, using 0, used by 24, 0.000105⟩,
⟨Lean.Server.RequestError, using 0, used by 51, 0.000105⟩,
⟨Lean.Elab.Term.PatternVar, using 0, used by 34, 0.000105⟩,
⟨Lean.Server.Watchdog.FileWorker, using 0, used by 47, 0.000105⟩,
⟨Lean.Elab.Term.LetRecDeclView, using 0, used by 28, 0.000105⟩,
⟨Numeric.OfNat, using 5, used by 77, 0.000105⟩,
⟨Lean.Json.Structured, using 0, used by 58, 0.000104⟩,
⟨funext, using 5, used by 61, 0.000104⟩,
⟨Lean.Elab.Term.NamedArg, using 0, used by 51, 0.000104⟩,
⟨NonScalar, using 0, used by 34, 0.000104⟩,
⟨Lean.Elab.Command.CommandElabM, using 2, used by 116, 0.000104⟩,
⟨Lean.AttrM, using 1, used by 67, 0.000104⟩,
⟨Lean.Lsp.DocumentSymbol, using 0, used by 33, 0.000104⟩,
⟨Lean.Elab.Command.StructFieldView, using 0, used by 30, 0.000104⟩,
⟨DecidableRel, using 1, used by 39, 0.000103⟩,
⟨Monoid.toSemigroup, using 2, used by 95, 0.000103⟩,
⟨Lean.Parser.optional.formatter, using 6, used by 78, 0.000103⟩,
⟨Lean.Parser.optional.parenthesizer, using 6, used by 78, 0.000103⟩,
⟨LinearOrder.toPartialOrder, using 2, used by 73, 0.000103⟩,
⟨namedPattern, using 0, used by 91, 0.000103⟩,
⟨Lean.SimpleScopedEnvExtension.Descr, using 0, used by 14, 0.000103⟩,
⟨Lean.Meta.SimpLemmas, using 0, used by 50, 0.000102⟩,
⟨Lean.PrettyPrinter.Delaborator.Context, using 0, used by 71, 0.000102⟩,
⟨Lean.DeclarationRanges, using 0, used by 26, 0.000102⟩,
⟨ForIn, using 1, used by 26, 0.000102⟩,
⟨Lean.Meta.SavedState, using 0, used by 40, 0.000102⟩,
⟨OptionT, using 1, used by 25, 0.000102⟩,
⟨Quotient, using 3, used by 25, 0.000102⟩,
⟨Lean.Elab.Term.Quotation.MatchResult, using 0, used by 23, 0.000102⟩,
⟨Lean.Elab.Command.InductiveView, using 0, used by 33, 0.000102⟩,
⟨Lean.CollectLevelParams.State, using 0, used by 18, 0.000102⟩,
⟨Lean.PrettyPrinter.Delaborator.TopDownAnalyze.Context, using 0, used by 36, 0.000101⟩,
⟨Lean.Meta.Closure.State, using 0, used by 35, 0.000101⟩,
⟨Lean.MessageDataContext, using 0, used by 41, 0.000101⟩,
⟨ReaderT.instMonadFunctorReaderT, using 4, used by 289, 0.000101⟩,
⟨Tactic.Ring.HornerExpr, using 0, used by 39, 0.000101⟩,
⟨ForInStep.done, using 1, used by 59, 0.000101⟩,
⟨Quot.mk, using 1, used by 20, 0.000101⟩,
⟨Lean.Lsp.DocumentFilter, using 0, used by 17, 0.000101⟩,
⟨Ord.mk, using 2, used by 17, 0.000101⟩,
⟨Lean.Elab.Command.Scope, using 0, used by 51, 0.000101⟩,
⟨Nat.instDvdNat, using 8, used by 67, 0.000100⟩,
⟨Dvd.dvd, using 1, used by 67, 0.000100⟩,
⟨instMonadStateOf, using 13, used by 197, 0.000100⟩,
⟨Lean.Compiler.NumScalarTypeInfo, using 0, used by 29, 0.000100⟩,
⟨Lean.Lsp.LeanFileProgressProcessingInfo, using 0, used by 25, 0.000100⟩,
⟨Lean.Meta.SynthInstance.Answer, using 0, used by 44, 0.000100⟩,
⟨Lean.Server.FileWorker.EditableDocument, using 0, used by 51, 0.000100⟩,
⟨Std.ToFormat.format, using 2, used by 144, 0.000100⟩,
⟨Lean.Rat, using 0, used by 31, 0.000100⟩,
⟨Lean.FVarId.name, using 2, used by 37, 0.000100⟩,
⟨Lean.JsonRpc.Notification, using 0, used by 25, 0.000100⟩,
⟨Lean.ProjectionFunctionInfo, using 0, used by 27, 0.000099⟩,
⟨Lean.EnvExtensionInterface.ext, using 1, used by 6, 0.000099⟩,
⟨Option.getD, using 2, used by 57, 0.000099⟩,
⟨Lean.Occurrences, using 0, used by 24, 0.000099⟩,
⟨Lean.Meta.CongrLemma, using 0, used by 37, 0.000099⟩,
⟨Lean.Widget.InteractiveHypothesis, using 0, used by 43, 0.000099⟩,
⟨Lean.Elab.Tactic.Simp.DischargeWrapper, using 0, used by 30, 0.000099⟩,
⟨And.left, using 1, used by 41, 0.000099⟩,
⟨Lean.AttributeImplCore, using 0, used by 34, 0.000099⟩,
⟨Lean.CollectFVars.State, using 0, used by 23, 0.000099⟩,
⟨Int.instOfNatInt, using 5, used by 94, 0.000099⟩,
⟨Lean.Syntax.ident, using 7, used by 129, 0.000098⟩,
⟨Lean.ParserCompiler.CombinatorAttribute, using 0, used by 27, 0.000098⟩,
⟨Lean.Lsp.ClientCapabilities, using 0, used by 21, 0.000098⟩,
⟨Lean.instToMessageDataString, using 4, used by 294, 0.000098⟩,
⟨And.right, using 1, used by 42, 0.000097⟩,
⟨Std.PHashSet, using 3, used by 48, 0.000097⟩,
⟨WellFoundedRelation.rel, using 1, used by 20, 0.000097⟩,
⟨Lean.TransformStep, using 0, used by 33, 0.000097⟩,
⟨Lean.Meta.PostponedEntry, using 0, used by 47, 0.000097⟩,
⟨Lean.Parser.termParser, using 8, used by 104, 0.000097⟩,
⟨Lean.Elab.Term.Do.Alt, using 0, used by 39, 0.000097⟩,
⟨Lean.Compiler.SpecInfo, using 0, used by 39, 0.000097⟩,
⟨HPow.hPow, using 1, used by 59, 0.000096⟩,
⟨modify, using 5, used by 151, 0.000096⟩,
⟨Lean.ToMessageData.mk, using 2, used by 17, 0.000096⟩,
⟨Lean.TraceElem, using 0, used by 39, 0.000095⟩,
⟨Lean.Option.name, using 2, used by 41, 0.000095⟩,
⟨Lean.Widget.InfoWithCtx, using 0, used by 25, 0.000095⟩,
⟨USize.val, using 3, used by 47, 0.000095⟩,
⟨Union, using 0, used by 8, 0.000095⟩,
⟨Inter, using 0, used by 8, 0.000095⟩,
⟨Sdiff, using 0, used by 8, 0.000095⟩,
⟨Lean.IR.Borrow.ParamMap.Key, using 0, used by 25, 0.000095⟩,
⟨Lean.mkApp, using 28, used by 52, 0.000095⟩,
⟨Lean.Lsp.DiagnosticCode, using 0, used by 31, 0.000095⟩,
⟨Lean.Lsp.TextDocumentContentChangeEvent, using 0, used by 30, 0.000094⟩,
⟨Lean.PPContext, using 0, used by 35, 0.000094⟩,
⟨Std.PersistentHashMap.Stats, using 0, used by 18, 0.000094⟩,
⟨Lean.Elab.Term.SavedContext, using 0, used by 33, 0.000094⟩,
⟨Lean.Meta.Match.InjectionAnyResult, using 0, used by 13, 0.000094⟩,
⟨Mod.mk, using 1, used by 11, 0.000094⟩,
⟨Lean.Lsp.SemanticTokensLegend, using 0, used by 23, 0.000094⟩,
⟨Lean.Quote, using 0, used by 18, 0.000094⟩,
⟨Lean.EnvExtensionInterfaceImp, using 1, used by 6, 0.000094⟩,
⟨Lean.KVMap.mk, using 5, used by 70, 0.000094⟩,
⟨Lean.Meta.DiscrTree.Trie, using 0, used by 41, 0.000094⟩,
⟨noConfusionEnum, using 9, used by 42, 0.000094⟩,
⟨Lean.Parser.ParserExtension.OLeanEntry, using 0, used by 34, 0.000094⟩,
⟨Lean.Meta.ElimInfo, using 0, used by 33, 0.000093⟩,
⟨Lean.ScopedEnvExtension.StateStack, using 0, used by 37, 0.000093⟩,
⟨Lean.EnvironmentHeader, using 0, used by 28, 0.000093⟩,
⟨cond.match_1, using 6, used by 8, 0.000093⟩,
⟨Lean.Lsp.SaveOptions, using 0, used by 23, 0.000093⟩,
⟨Lean.JsonRpc.Response, using 0, used by 19, 0.000093⟩,
⟨Lean.Lsp.FileSource.mk, using 2, used by 28, 0.000093⟩,
⟨STWorld, using 1, used by 32, 0.000093⟩,
⟨Lean.Lsp.WorkDoneProgressReport, using 0, used by 24, 0.000093⟩,
⟨Seq.mk, using 2, used by 13, 0.000093⟩,
⟨SeqLeft.mk, using 2, used by 13, 0.000093⟩,
⟨SeqRight.mk, using 2, used by 13, 0.000093⟩,
⟨UInt32.val, using 3, used by 49, 0.000093⟩,
⟨Lean.Elab.Term.ElabAppArgs.State, using 0, used by 24, 0.000092⟩,
⟨Lean.Lsp.TextDocumentSyncOptions, using 0, used by 27, 0.000092⟩,
⟨Lean.Meta.Closure.ToProcessElement, using 0, used by 28, 0.000092⟩,
⟨DoResultBC, using 0, used by 9, 0.000092⟩,
⟨OrElse.mk, using 2, used by 14, 0.000092⟩,
⟨Lean.JsonRpc.Request, using 0, used by 24, 0.000092⟩,
⟨HDiv.hDiv, using 1, used by 103, 0.000092⟩,
⟨Std.PersistentHashSet, using 2, used by 22, 0.000092⟩,
⟨Lean.instInhabitedExpr, using 9, used by 108, 0.000092⟩,
⟨FloatSpec.float, using 1, used by 17, 0.000092⟩,
⟨Lean.TagDeclarationExtension, using 3, used by 8, 0.000091⟩,
⟨Lean.Lsp.SemanticTokensOptions, using 0, used by 25, 0.000091⟩,
⟨Lean.Meta.SimpAll.Entry, using 0, used by 27, 0.000091⟩,
⟨Acc.intro, using 1, used by 14, 0.000091⟩,
⟨Lean.Meta.ParamInfo, using 0, used by 28, 0.000091⟩,
⟨Lean.PrettyPrinter.Formatter.tokenWithAntiquot.formatter, using 23, used by 3, 0.000091⟩,
⟨Lean.PrettyPrinter.Parenthesizer.tokenWithAntiquot.parenthesizer, using 23, used by 3, 0.000091⟩,
⟨Lean.Parser.ParserExtension.Entry, using 0, used by 36, 0.000091⟩,
⟨Lean.Lsp.TextEdit, using 0, used by 16, 0.000091⟩,
⟨instHDiv, using 4, used by 102, 0.000091⟩,
⟨Lean.Parser.ParserModuleContext, using 0, used by 31, 0.000090⟩,
⟨Lean.Elab.Command.StructView, using 0, used by 21, 0.000090⟩,
⟨Lean.PrettyPrinter.Formatter.symbolNoAntiquot.formatter, using 72, used by 4, 0.000090⟩,
⟨Lean.IR.ExplicitRC.VarInfo, using 0, used by 21, 0.000090⟩,
⟨Lean.PrettyPrinter.Formatter.checkPrec.formatter, using 15, used by 13, 0.000090⟩,
⟨Lean.Elab.DefViewElabHeader, using 0, used by 27, 0.000090⟩,
⟨Lean.Server.Watchdog.ServerContext, using 0, used by 36, 0.000090⟩,
⟨MonadWithReader, using 1, used by 8, 0.000090⟩,
⟨AddMonoid.toAddSemigroup, using 2, used by 83, 0.000089⟩,
⟨Lean.MessageData.ofFormat, using 2, used by 119, 0.000089⟩,
⟨Lean.Elab.Term.MatchAltView, using 0, used by 29, 0.000089⟩,
⟨Lean.Parser.PrattParsingTables, using 0, used by 31, 0.000089⟩,
⟨Lean.ToExpr, using 0, used by 22, 0.000089⟩,
⟨IO.FS.Handle, using 0, used by 23, 0.000089⟩,
⟨String.Range, using 0, used by 22, 0.000089⟩,
⟨Lean.Server.Watchdog.WorkerState, using 0, used by 24, 0.000088⟩,
⟨Int.casesOn, using 5, used by 31, 0.000088⟩,
⟨Substring.mk, using 3, used by 27, 0.000088⟩,
⟨Lean.Elab.Term.CollectPatternVars.Context, using 0, used by 24, 0.000088⟩,
⟨GE.ge, using 2, used by 75, 0.000088⟩,
⟨Std.HashMapBucket, using 9, used by 34, 0.000088⟩,
⟨Lean.Lsp.ServerInfo, using 0, used by 24, 0.000088⟩,
⟨CoeFun, using 1, used by 11, 0.000088⟩,
⟨Std.PersistentArray.Stats, using 0, used by 17, 0.000088⟩,
⟨Lean.Lsp.InitializeParams, using 0, used by 32, 0.000088⟩,
⟨MonadExceptOf.mk, using 1, used by 13, 0.000088⟩,
⟨Lean.IR.EmitC.M, using 4, used by 74, 0.000088⟩,
⟨Lean.Parsec.instAlternativeParsec, using 7, used by 76, 0.000088⟩,
⟨Lean.IR.IndexRenaming, using 4, used by 33, 0.000088⟩,
⟨Nonempty.intro, using 1, used by 16, 0.000088⟩,
⟨Lean.Parser.instOrElseParser, using 6, used by 69, 0.000087⟩,
⟨StateRefT'.instMonadStateOfStateRefT', using 9, used by 174, 0.000087⟩,
⟨Mathlib.Tactic.Lint.Linter, using 0, used by 26, 0.000087⟩,
⟨Lean.Level.succ, using 2, used by 61, 0.000087⟩,
⟨List.mem, using 14, used by 25, 0.000087⟩,
⟨HSub.mk, using 2, used by 4, 0.000087⟩,
⟨UInt64.val, using 3, used by 47, 0.000087⟩,
⟨Div.mk, using 1, used by 14, 0.000087⟩,
⟨Decidable.rec, using 4, used by 2, 0.000087⟩,
⟨instOfNatUInt64, using 5, used by 47, 0.000087⟩,
⟨StateRefT'.instMonadFunctorStateRefT', using 7, used by 272, 0.000087⟩,
⟨Lean.PrettyPrinter.Delaborator.DelabM, using 6, used by 61, 0.000087⟩,
⟨Lean.Parser.optional, using 6, used by 78, 0.000087⟩,
⟨USize.toNat, using 5, used by 91, 0.000087⟩,
⟨ToStream, using 1, used by 12, 0.000086⟩,
⟨ReprAtom.mk, using 1, used by 14, 0.000086⟩,
⟨Lean.Elab.Term.Do.DoIfView, using 0, used by 14, 0.000086⟩,
⟨Lean.CollectMVars.State, using 0, used by 19, 0.000086⟩,
⟨Lean.Lsp.DiagnosticRelatedInformation, using 0, used by 28, 0.000086⟩,
⟨CoeSort, using 1, used by 11, 0.000086⟩,
⟨Lean.KeyedDeclsAttribute.Def, using 0, used by 27, 0.000086⟩,
⟨Lean.Meta.InductionSubgoal, using 0, used by 24, 0.000086⟩,
⟨Lean.IR.ExpandResetReuse.ProjMap, using 5, used by 14, 0.000086⟩,
⟨Lean.Meta.MatcherApp, using 0, used by 30, 0.000086⟩,
⟨Std.PArray, using 1, used by 41, 0.000085⟩,
⟨Lean.Meta.Match.Alt, using 0, used by 33, 0.000085⟩,
⟨Lean.Elab.Term.StructInst.ExplicitSourceInfo, using 0, used by 25, 0.000085⟩]
All Messages (1)
-/
-- #print IO.Error
def main (strs : List String) : IO UInt32 := do
  initSearchPath (← Lean.findSysroot?) ["build/lib"]
  let env ← importModules [{module := `Mathlib}] {}
  let u ← CoreM.toIO test {} {env := env}
  return 0

-- #exit
-- #eval (do
--   let env ← getEnv
--   let g ← mkNameGraph
--   IO.println g.size
--   return ()
--   : CoreM Unit)
-- #exit


-- #check Array.qsort
#print UInt64.ofNatCore
