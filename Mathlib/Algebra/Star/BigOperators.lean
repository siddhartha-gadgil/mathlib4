/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.star.big_operators
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Star.Basic

/-! # Big-operators lemmas about `star` algebraic operations

These results are kept separate from `Algebra.Star.Basic` to avoid it needing to import `Finset`.
-/


variable {R : Type _}

-- Porting note: commented out the next line
-- open BigOperators

@[simp]
theorem star_prod [CommMonoid R] [StarSemigroup R] {α : Type _} (s : Finset α) (f : α → R) :
    star (∏ x in s, f x) = ∏ x in s, star (f x) := map_prod (starMulAut : R ≃* R) _ _
#align star_prod star_prod

@[simp]
theorem star_sum [AddCommMonoid R] [StarAddMonoid R] {α : Type _} (s : Finset α) (f : α → R) :
    star (∑ x in s, f x) = ∑ x in s, star (f x) := (starAddEquiv : R ≃+ R).map_sum _ _
#align star_sum star_sum
