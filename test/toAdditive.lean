import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.NormCast
import Mathlib.Tactic.RunCmd
import Mathlib.Lean.Exception
import Mathlib.Util.Time
import Qq.MetaM
open Qq Lean Meta Elab Command ToAdditive

-- work in a namespace so that it doesn't matter if names clash
namespace Test

-- [note] use the below options for diagnostics:
-- set_option trace.to_additive true
-- set_option trace.to_additive_detail true
-- set_option pp.universes true
-- set_option pp.explicit true
-- set_option pp.notation false

@[to_additive bar0]
def foo0 {α} [Mul α] [One α] (x y : α) : α := x * y * 1

theorem bar0_works : bar0 3 4 = 7 := by decide

class my_has_pow (α : Type u) (β : Type v) :=
(pow : α → β → α)

instance : my_has_pow Nat Nat := ⟨fun a b => a ^ b⟩

class my_has_scalar (M : Type u) (α : Type v) :=
(smul : M → α → α)

instance : my_has_scalar Nat Nat := ⟨fun a b => a * b⟩
attribute [to_additive (reorder := 1) my_has_scalar] my_has_pow
attribute [to_additive (reorder := 1 4)] my_has_pow.pow

@[to_additive bar1]
def foo1 {α : Type u} [my_has_pow α ℕ] (x : α) (n : ℕ) : α := @my_has_pow.pow α ℕ _ x n

theorem foo1_works : foo1 3 4 = Nat.pow 3 4 := by decide
theorem bar1_works : bar1 3 4 = 3 * 4 := by decide

infix:80 " ^ " => my_has_pow.pow

instance dummy_pow : my_has_pow ℕ $ PLift ℤ := ⟨fun _ _ => 5⟩

@[to_additive bar2]
def foo2 {α} [my_has_pow α ℕ] (x : α) (n : ℕ) (m : PLift ℤ) : α := x ^ (n ^ m)

theorem foo2_works : foo2 2 3 (PLift.up 2) = Nat.pow 2 5 := by decide
theorem bar2_works : bar2 2 3 (PLift.up 2) =  2 * 5 := by decide

@[to_additive bar3]
def foo3 {α} [my_has_pow α ℕ] (x : α) : ℕ → α := @my_has_pow.pow α ℕ _ x

theorem foo3_works : foo3 2 3 = Nat.pow 2 3 := by decide
theorem bar3_works : bar3 2 3 =  2 * 3 := by decide

@[to_additive bar4]
def foo4 {α : Type u} : Type v → Type (max u v) := @my_has_pow α

@[to_additive bar4_test]
lemma foo4_test {α β : Type u} : @foo4 α β = @my_has_pow α β := rfl

@[to_additive bar5]
def foo5 {α} [my_has_pow α ℕ] [my_has_pow ℕ ℤ] : True := True.intro

@[to_additive bar6]
def foo6 {α} [my_has_pow α ℕ] : α → ℕ → α := @my_has_pow.pow α ℕ _

-- fails because of workaround in `transform`. Not sure if this will show up in practice
-- @[to_additive bar7]
-- def foo7 := @my_has_pow.pow

-- theorem foo7_works : foo7 2 3 = Nat.pow 2 3 := by decide
-- theorem bar7_works : bar7 2 3 =  2 * 3 := by decide

/-- Check that we don't additivize `Nat` expressions. -/
@[to_additive bar8]
def foo8 (a b : ℕ) := a * b

theorem bar8_works : bar8 2 3 = 6 := by decide

/-- Check that we don't additivize `Nat` numerals. -/
@[to_additive bar9]
def foo9 := 1

theorem bar9_works : bar9 = 1 := by decide

@[to_additive bar10]
def foo10 (n m : ℕ) := HPow.hPow n m + n * m * 2 + 1 * 0 + 37 * 1 + 2

theorem bar10_works : bar10 = foo10 := by rfl

@[to_additive bar11]
def foo11 (n : ℕ) (m : ℤ) := n * m * 2 + 1 * 0 + 37 * 1 + 2

theorem bar11_works : bar11 = foo11 := by rfl

@[to_additive bar12]
def foo12 (_ : Nat) (_ : Int) : Fin 37 := ⟨2, by decide⟩

@[to_additive (reorder := 1 4) bar13]
lemma foo13 {α β : Type u} [my_has_pow α β] (x : α) (y : β) : x ^ y = x ^ y := rfl

@[to_additive (reorder := 1 4) bar14]
def foo14 {α β : Type u} [my_has_pow α β] (x : α) (y : β) : α := (x ^ y) ^ y

@[to_additive (reorder := 1 4) bar15]
lemma foo15 {α β : Type u} [my_has_pow α β] (x : α) (y : β) : foo14 x y = (x ^ y) ^ y := rfl

@[to_additive (reorder := 1 4) bar16]
lemma foo16 {α β : Type u} [my_has_pow α β] (x : α) (y : β) : foo14 x y = (x ^ y) ^ y := foo15 x y

initialize testExt : SimpExtension ←
  registerSimpAttr `simp_test "test"

@[to_additive bar17]
def foo17 [Group α] (x : α) : α := x * 1

@[to_additive (attr := simp) bar18]
lemma foo18 [Group α] (x : α) : foo17 x = x ∧ foo17 x = 1 * x :=
  ⟨mul_one x, mul_one x |>.trans <| one_mul x |>.symm⟩

example [Group α] (x : α) : foo17 x = 1 * x := by simp
example [Group α] (x : α) : foo17 x = x := by simp
example [AddGroup α] (x : α) : bar17 x = 0 + x := by simp
example [AddGroup α] (x : α) : bar17 x = x := by simp

run_cmd do
  let mul1 := `test.toAdditive._auxLemma |>.mkNum 1
  let mul2 := `test.toAdditive._auxLemma |>.mkNum 2
  let add1 := `test.toAdditive._auxLemma |>.mkNum 3
  let add2 := `test.toAdditive._auxLemma |>.mkNum 4
  if ToAdditive.findTranslation? (← getEnv) mul1 != some add1 then throwError "1"
  if ToAdditive.findTranslation? (← getEnv) mul2 != some add2 then throwError "2"

/- test the eta-expansion applied on `foo6`. -/
run_cmd do
  let c ← getConstInfo `Test.foo6
  let e : Expr ← Elab.Command.liftCoreM <| MetaM.run' <| ToAdditive.expand c.value!
  let t ← Elab.Command.liftCoreM <| MetaM.run' <| ToAdditive.expand c.type
  let decl := c |>.updateName `Test.barr6 |>.updateType t |>.updateValue e |>.toDeclaration!
  Elab.Command.liftCoreM <| addAndCompile decl
  -- test that we cannot transport a declaration to itself
  successIfFail <| Elab.Command.liftCoreM <|
    ToAdditive.addToAdditiveAttr `bar11_works { ref := ← getRef }

/- Test on inductive types -/
inductive AddInd : ℕ → Prop where
  | basic : AddInd 2
  | zero : AddInd 0

@[to_additive]
inductive MulInd : ℕ → Prop where
  | basic : MulInd 2
  | one : MulInd 1

run_cmd do
  unless findTranslation? (← getEnv) `Test.MulInd.one == some `Test.AddInd.zero do throwError "1"
  unless findTranslation? (← getEnv) `Test.MulInd.basic == none do throwError "2"
  unless findTranslation? (← getEnv) `Test.MulInd == some `Test.AddInd do throwError "3"

/-! Test the namespace bug (#8733). This code should *not* generate a lemma
  `add_some_def.in_namespace`. -/
def some_def.in_namespace : Bool := false

def some_def {α : Type u} [Mul α] (x : α) : α :=
if some_def.in_namespace then x * x else x


-- cannot apply `@[to_additive]` to `some_def` if `some_def.in_namespace` doesn't have the attribute
run_cmd Elab.Command.liftCoreM <| successIfFail <|
    ToAdditive.transformDecl { ref := ← getRef} `Test.some_def `Test.add_some_def


attribute [to_additive some_other_name] some_def.in_namespace
attribute [to_additive add_some_def] some_def

run_cmd do
  Elab.Command.liftCoreM <| successIfFail (getConstInfo `Test.add_some_def.in_namespace)

-- [todo] currently this test breaks.
-- example : (AddUnits.mk_of_add_eq_zero 0 0 (by simp) : ℕ)
--         = (AddUnits.mk_of_add_eq_zero 0 0 (by simp) : ℕ) :=
-- by norm_cast

section

set_option linter.unusedVariables false
-- porting note : not sure what the tests do, but the linter complains.

def foo_mul {I J K : Type} (n : ℕ) {f : I → Type} (L : Type) [∀ i, One (f i)]
  [Add I] [Mul L] : true := by trivial


@[to_additive]
instance pi.has_one {I : Type} {f : I → Type} [(i : I) → One $ f i] : One ((i : I) → f i) :=
  ⟨fun _ => 1⟩

run_cmd do
  let n ← (Elab.Command.liftCoreM <| MetaM.run' <| ToAdditive.firstMultiplicativeArg
    `Test.pi.has_one)
  if n != 1 then throwError "{n} != 1"
  let n ← (Elab.Command.liftCoreM <| MetaM.run' <| ToAdditive.firstMultiplicativeArg
    `Test.foo_mul)
  if n != 4 then throwError "{n} != 4"

end

@[to_additive]
def nat_pi_has_one {α : Type} [One α] : One ((x : Nat) → α) := by infer_instance

@[to_additive]
def pi_nat_has_one {I : Type} : One ((x : I) → Nat)  := pi.has_one

example : @pi_nat_has_one = @pi_nat_has_zero := rfl

section test_noncomputable

@[to_additive Bar.bar]
noncomputable def Foo.foo (h : ∃ _ : α, True) : α := Classical.choose h

@[to_additive Bar.bar']
def Foo.foo' : ℕ := 2

theorem Bar.bar'_works : Bar.bar' = 2 := by decide

run_cmd (do
  if !isNoncomputable (← getEnv) `Test.Bar.bar then throwError "bar shouldn't be computable"
  if isNoncomputable (← getEnv) `Test.Bar.bar' then throwError "bar' should be computable")
end test_noncomputable

section instances

class FooClass (α) : Prop where
  refle : ∀ a : α, a = a

@[to_additive]
instance FooClass_one [One α] : FooClass α := ⟨λ _ => rfl ⟩

lemma one_fooClass [One α] : FooClass α := by infer_instance

lemma zero_fooClass [Zero α] : FooClass α := by infer_instance

end instances

/- Check that `to_additive` works if a `_match` aux declaration is created. -/
@[to_additive]
def IsUnit [Mul M] (a : M) : Prop := a ≠ a

@[to_additive]
theorem isUnit_iff_exists_inv [Mul M] {a : M} : IsUnit a ↔ ∃ _ : α, a ≠ a :=
  ⟨fun h => absurd rfl h, fun ⟨_, hab⟩ => hab⟩

/-! Test that `@[to_additive]` correctly translates auxiliary declarations that do not have the
original declaration name as prefix.-/
@[to_additive]
def IsUnit' [Monoid M] (a : M) : Prop := ∃ b : M, a * b = 1

@[to_additive]
theorem isUnit'_iff_exists_inv [CommMonoid M] {a : M} : IsUnit' a ↔ ∃ b, a * b = 1 := Iff.rfl

@[to_additive]
theorem isUnit'_iff_exists_inv' [CommMonoid M] {a : M} : IsUnit' a ↔ ∃ b, b * a = 1 := by
  simp [isUnit'_iff_exists_inv, mul_comm]

def Ones : ℕ → Q(Nat)
| 0     => q(1)
| (n+1) => q($(Ones n) + $(Ones n))

-- this test just exists to see if this finishes in finite time. It should take <100ms.
-- #time
run_cmd do
  let e : Expr := Ones 400
  let _ ← Elab.Command.liftCoreM <| MetaM.run' <| ToAdditive.applyReplacementFun e





/-!
Some arbitrary tests to check whether additive names are guessed correctly.
-/
section guessName

open ToAdditive

def checkGuessName (s t : String) : Elab.Command.CommandElabM Unit :=
  unless guessName s == t do throwError "failed: {guessName s} != {t}"

run_cmd
  checkGuessName "HMul_Eq_LEOne_Conj₂MulLT'" "HAdd_Eq_Nonpos_Conj₂AddLT'"
  checkGuessName "OneMulSMulInvDivPow"       "ZeroAddVAddNegSubNSMul"
  checkGuessName "ProdFinprodNPowZPow"       "SumFinsumNSMulZSMul"

  -- The current design swaps all instances of `Comm`+`Add` in order to have
  -- `AddCommMonoid` instead of `CommAddMonoid`.
  checkGuessName "comm_mul_CommMul_commMul" "comm_add_AddComm_addComm"
  checkGuessName "mul_comm_MulComm_mulComm" "add_comm_AddComm_addComm"
  checkGuessName "mul_single_eq_same" "single_eq_same"
  checkGuessName "mul_support" "support"
  checkGuessName "mul_tsupport" "tsupport"
  checkGuessName "mul_indicator" "indicator"

  checkGuessName "CommMonoid" "AddCommMonoid"
  checkGuessName "commMonoid" "addCommMonoid"

  checkGuessName "CancelCommMonoid" "AddCancelCommMonoid"
  checkGuessName "cancelCommMonoid" "addCancelCommMonoid"
  checkGuessName "CancelMonoid" "AddCancelMonoid"
  checkGuessName "cancelMonoid" "addCancelMonoid"
  checkGuessName "RightCancelMonoid" "AddRightCancelMonoid"
  checkGuessName "rightCancelMonoid" "addRightCancelMonoid"
  checkGuessName "LeftCancelMonoid" "AddLeftCancelMonoid"
  checkGuessName "leftCancelMonoid" "addLeftCancelMonoid"

  checkGuessName "IsLeftRegular" "IsAddLeftRegular"
  checkGuessName "isRightRegular" "isAddRightRegular"
  checkGuessName "IsRegular" "IsAddRegular"

  checkGuessName "LTOne_LEOne_OneLE_OneLT" "Neg_Nonpos_Nonneg_Pos"
  checkGuessName "LTHMulHPowLEHDiv" "LTHAddHSMulLEHSub"
  checkGuessName "OneLEHMul" "NonnegHAdd"
  checkGuessName "OneLTHPow" "PosHSMul"
  checkGuessName "OneLTPow" "PosNSMul"
  checkGuessName "instCoeTCOneHom" "instCoeTCZeroHom"
  checkGuessName "instCoeTOneHom" "instCoeTZeroHom"
  checkGuessName "instCoeOneHom" "instCoeZeroHom"
  checkGuessName "invFun_eq_symm" "invFun_eq_symm"
  checkGuessName "MulEquiv.symmInvFun" "AddEquiv.symmInvFun"

end guessName

end Test
