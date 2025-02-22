/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module data.rat.big_operators
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Rat.Cast
import Mathlib.Algebra.BigOperators.Basic

/-! # Casting lemmas for rational numbers involving sums and products
-/

-- Porting note: big operators are currently global
--open BigOperators

variable {ι α : Type _}

namespace Rat

section WithDivRing

variable [DivisionRing α] [CharZero α]

@[simp, norm_cast]
theorem cast_list_sum (s : List ℚ) : (↑s.sum : α) = (s.map (↑)).sum :=
  map_list_sum (Rat.castHom α) _
#align rat.cast_list_sum Rat.cast_list_sum

@[simp, norm_cast]
theorem cast_multiset_sum (s : Multiset ℚ) : (↑s.sum : α) = (s.map (↑)).sum :=
  map_multiset_sum (Rat.castHom α) _
#align rat.cast_multiset_sum Rat.cast_multiset_sum

@[simp, norm_cast]
theorem cast_sum (s : Finset ι) (f : ι → ℚ) : (∑ i in s, f i) = ∑ i in s, (f i : α) :=
  (map_sum (Rat.castHom α) _ s)
#align rat.cast_sum Rat.cast_sum

@[simp, norm_cast]
theorem cast_list_prod (s : List ℚ) : (↑s.prod : α) = (s.map (↑)).prod :=
  map_list_prod (Rat.castHom α) _
#align rat.cast_list_prod Rat.cast_list_prod

end WithDivRing

section Field

variable [Field α] [CharZero α]

@[simp, norm_cast]
theorem cast_multiset_prod (s : Multiset ℚ) : (↑s.prod : α) = (s.map (↑)).prod :=
  map_multiset_prod (Rat.castHom α) _
#align rat.cast_multiset_prod Rat.cast_multiset_prod

@[simp, norm_cast]
theorem cast_prod (s : Finset ι) (f : ι → ℚ) : (∏ i in s, f i) = ∏ i in s, (f i : α) :=
  map_prod (Rat.castHom α) _ _
#align rat.cast_prod Rat.cast_prod

end Field

end Rat
