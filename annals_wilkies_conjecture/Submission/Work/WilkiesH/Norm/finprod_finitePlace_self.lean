import Mathlib

namespace Work.WilkiesH.Norm

lemma finprod_finitePlace_self {K : Type*} [Field K] [NumberField K]
    {b : NumberField.RingOfIntegers K} (hb : b ≠ 0) :
    (∏ᶠ v : NumberField.FinitePlace K, v (b : K))
      * (Ideal.absNorm (Ideal.span ({b} : Set (NumberField.RingOfIntegers K))) : ℝ) = 1 := by
  have hN : ((Algebra.norm ℤ b : ℤ) : ℝ) ≠ 0 := by
    have : (Algebra.norm ℤ b : ℤ) ≠ 0 := by
      rw [Algebra.norm_ne_zero_iff]; exact hb
    exact_mod_cast this
  rw [NumberField.FinitePlace.prod_eq_inv_abs_norm_int hb,
    Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs,
    inv_mul_cancel₀ (abs_ne_zero.mpr hN)]

end Work.WilkiesH.Norm
