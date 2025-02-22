/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
Ported by: Scott Morrison

! This file was ported from Lean 3 source module data.int.dvd.basic
! leanprover-community/mathlib commit fc2ed6f838ce7c9b7c7171e58d78eaf7b438fb0e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Cast.Basic

/-!
# Basic lemmas about the divisibility relation in `ℤ`.
-/


open Nat

namespace Int

@[norm_cast]
theorem coe_nat_dvd {m n : ℕ} : (↑m : ℤ) ∣ ↑n ↔ m ∣ n :=
  ⟨fun ⟨a, ae⟩ =>
    m.eq_zero_or_pos.elim (fun m0 => by simp [m0] at ae; simp [ae, m0]) fun m0l => by
      cases'
        eq_ofNat_of_zero_le
          (@nonneg_of_mul_nonneg_right ℤ _ m a (by simp [ae.symm]) (by simpa using m0l)) with
        k e
      subst a
      exact ⟨k, Int.ofNat.inj ae⟩,
    fun ⟨k, e⟩ => Dvd.intro k <| by rw [e, Int.ofNat_mul]⟩
#align int.coe_nat_dvd Int.coe_nat_dvd

theorem coe_nat_dvd_left {n : ℕ} {z : ℤ} : (↑n : ℤ) ∣ z ↔ n ∣ z.natAbs := by
  rcases natAbs_eq z with (eq | eq) <;> rw [eq] <;> simp [←coe_nat_dvd]
#align int.coe_nat_dvd_left Int.coe_nat_dvd_left

theorem coe_nat_dvd_right {n : ℕ} {z : ℤ} : z ∣ (↑n : ℤ) ↔ z.natAbs ∣ n := by
  rcases natAbs_eq z with (eq | eq) <;> rw [eq] <;> simp [←coe_nat_dvd]
#align int.coe_nat_dvd_right Int.coe_nat_dvd_right

#align int.le_of_dvd Int.le_of_dvd

#align int.eq_one_of_dvd_one Int.eq_one_of_dvd_one

#align int.eq_one_of_mul_eq_one_right Int.eq_one_of_mul_eq_one_right

#align int.eq_one_of_mul_eq_one_left Int.eq_one_of_mul_eq_one_left

theorem ofNat_dvd_of_dvd_natAbs {a : ℕ} : ∀ {z : ℤ} (_ : a ∣ z.natAbs), ↑a ∣ z
  | Int.ofNat _, haz => Int.coe_nat_dvd.2 haz
  | -[k+1], haz => by
    change ↑a ∣ -(k + 1 : ℤ)
    apply dvd_neg_of_dvd
    apply Int.coe_nat_dvd.2
    exact haz
#align int.of_nat_dvd_of_dvd_nat_abs Int.ofNat_dvd_of_dvd_natAbs

theorem dvd_natAbs_of_ofNat_dvd {a : ℕ} : ∀ {z : ℤ} (_ : ↑a ∣ z), a ∣ z.natAbs
  | Int.ofNat _, haz => Int.coe_nat_dvd.1 (Int.dvd_natAbs.2 haz)
  | -[k+1], haz =>
    have haz' : (↑a : ℤ) ∣ (↑(k + 1) : ℤ) := dvd_of_dvd_neg haz
    Int.coe_nat_dvd.1 haz'
#align int.dvd_nat_abs_of_of_nat_dvd Int.dvd_natAbs_of_ofNat_dvd

#align int.dvd_antisymm Int.dvd_antisymm

end Int
