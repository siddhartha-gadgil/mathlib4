/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

! This file was ported from Lean 3 source module data.nat.gcd.big_operators
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Basic

/-! # Lemmas about coprimality with big products.

These lemmas are kept separate from `Data.Nat.GCD.Basic` in order to minimize imports.
-/


namespace Nat

-- Porting note: commented out the next line
-- open BigOperators

/-- See `IsCoprime.prod_left` for the corresponding lemma about `IsCoprime` -/
theorem coprime_prod_left {ι : Type _} {x : ℕ} {s : ι → ℕ} {t : Finset ι} :
    (∀ i : ι, i ∈ t → coprime (s i) x) → coprime (∏ i : ι in t, s i) x :=
  Finset.prod_induction s (fun y ↦ y.coprime x) (fun a b ↦ coprime.mul) (by simp)
#align nat.coprime_prod_left Nat.coprime_prod_left

/-- See `IsCoprime.prod_right` for the corresponding lemma about `IsCoprime` -/
theorem coprime_prod_right {ι : Type _} {x : ℕ} {s : ι → ℕ} {t : Finset ι} :
    (∀ i : ι, i ∈ t → coprime x (s i)) → coprime x (∏ i : ι in t, s i) :=
  Finset.prod_induction s (fun y ↦ x.coprime y) (fun a b ↦ coprime.mul_right) (by simp)
#align nat.coprime_prod_right Nat.coprime_prod_right

end Nat
