import Mathlib
import Submission.Work.L2F.Defs

namespace Work.L2F.Conic

open Polynomial
open scoped Polynomial

/-- In a finite field of odd characteristic the element `2` is nonzero, so the characteristic
is not `2`. -/
lemma ringChar_ne_two_of_two_ne_zero (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    ringChar F ≠ 2 := by
  intro h
  exact h2 ((CharP.cast_eq_zero_iff F (ringChar F) 2).mpr (by rw [h]))

/-- Every element of a finite field of odd characteristic is a sum of two squares.
Proof: `A = {a² | a : F}` has `(q+1)/2` elements (the squaring map on `Fˣ` is two-to-one, plus `0`)
and so does `c - A = {c - b² | b : F}`; two subsets of the `q`-element set `F` whose cardinalities
add up to `q + 1` meet, and an element of the intersection gives `a² = c - b²`. -/
theorem exists_sq_add_sq (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (c : F) :
    ∃ a b : F, a ^ 2 + b ^ 2 = c := by
  have hodd : Fintype.card F % 2 = 1 :=
    FiniteField.odd_card_of_char_ne_two (ringChar_ne_two_of_two_ne_zero F h2)
  obtain ⟨a, b, hab⟩ :=
    FiniteField.exists_root_sum_quadratic (f := (X ^ 2 : F[X])) (g := (X ^ 2 - C c : F[X]))
      (degree_X_pow 2) (degree_X_pow_sub_C (by norm_num) c) hodd
  refine ⟨a, b, ?_⟩
  have h : a ^ 2 + (b ^ 2 - c) = 0 := by simpa using hab
  linear_combination h

end Work.L2F.Conic
