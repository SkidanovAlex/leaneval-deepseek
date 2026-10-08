import Mathlib
import Submission.Work.L2F.Defs

namespace Work.L2F.Conic

open Polynomial
open scoped Polynomial

/-- For `d ≠ 0` every element of a finite field of odd characteristic is of the form
`a² - d·b²`.  Same counting proof as `exists_sq_add_sq`: `A = {a²}` and `c + d·A` both have
`(q+1)/2` elements, so they meet. -/
theorem exists_sq_sub_mul_sq (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (d : F) (hd : d ≠ 0) (c : F) : ∃ a b : F, a ^ 2 - d * b ^ 2 = c := by
  have hchar : ringChar F ≠ 2 := by
    intro h
    have hc := CharP.cast_eq_zero F (ringChar F)
    rw [h] at hc
    exact h2 hc
  have hodd : Fintype.card F % 2 = 1 :=
    FiniteField.odd_card_of_char_ne_two hchar
  -- `exists_root_sum_quadratic` on `f = X²` and `g = -d·X² - c` gives `a² + (-d·b² - c) = 0`.
  obtain ⟨a, b, hab⟩ :=
    FiniteField.exists_root_sum_quadratic (f := (X ^ 2 : F[X])) (g := C (-d) * X ^ 2 - C c)
      (degree_X_pow 2)
      (by
        rw [degree_sub_C
          (show 0 < degree (C (-d) * X ^ 2) by
            rw [degree_C_mul_X_pow 2 (neg_ne_zero.mpr hd)]; norm_num)]
        exact degree_C_mul_X_pow 2 (neg_ne_zero.mpr hd)) hodd
  refine ⟨a, b, ?_⟩
  have h : a ^ 2 + (-d * b ^ 2 - c) = 0 := by simpa using hab
  linear_combination h

end Work.L2F.Conic
