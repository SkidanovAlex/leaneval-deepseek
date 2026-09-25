import Mathlib

namespace Work.Tower.CMAdjoin

open Polynomial in
/-- Chinese remainder theorem for `X ^ 2 + 1` over a field that already contains a
square root `r` of `-1` (in characteristic `≠ 2`, so that the roots `r ≠ -r` are
distinct): `F[X] / (X ^ 2 + 1) ≃+* F × F`, since `X ^ 2 + 1 = (X - r)(X + r)` splits
into comaximal linear factors. -/
theorem quotient_X_sq_add_one_equiv_prod (F : Type*) [Field F] (r : F) (hr : r ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) :
    Nonempty ((Polynomial F ⧸ Ideal.span
      ({(Polynomial.X ^ 2 + 1 : Polynomial F)} : Set (Polynomial F))) ≃+* F × F) := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  have hunit : IsUnit (r - (-r)) := by
    apply isUnit_iff_ne_zero.mpr
    rw [sub_neg_eq_add, ← two_mul]
    exact mul_ne_zero h2 hr0
  have hcopI : IsCoprime (Ideal.span ({X - C r} : Set (Polynomial F)))
      (Ideal.span ({X - C (-r)} : Set (Polynomial F))) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr
      (Polynomial.isCoprime_X_sub_C_of_isUnit_sub hunit)
  have hfac : (X - C r) * (X - C (-r)) = (X ^ 2 + 1 : Polynomial F) := by
    have hr' : (C r : Polynomial F) ^ 2 = -1 := by rw [← map_pow, hr, map_neg, map_one]
    rw [map_neg]
    linear_combination -hr'
  have hspan : Ideal.span ({X - C r} : Set (Polynomial F)) ⊓
        Ideal.span ({X - C (-r)} : Set (Polynomial F))
      = Ideal.span ({X ^ 2 + 1} : Set (Polynomial F)) := by
    rw [← hfac, ← Ideal.mul_eq_inf_of_coprime (Ideal.isCoprime_iff_sup_eq.mp hcopI),
      Ideal.span_singleton_mul_span_singleton]
  rw [← hspan]
  exact ⟨(Ideal.quotientInfEquivQuotientProd _ _ hcopI).trans
    (RingEquiv.prodCongr (Polynomial.quotientSpanXSubCAlgEquiv r).toRingEquiv
      (Polynomial.quotientSpanXSubCAlgEquiv (-r)).toRingEquiv)⟩

end Work.Tower.CMAdjoin
