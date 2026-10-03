import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

/-- If `f : ℤ → ℂ` has finite `ℒᵖ`-seminorm with respect to counting measure on `ℤ` for some
exponent `p ≠ 0`, then `f` is pointwise bounded.

For `p = ⊤` this is the statement that the essential supremum for the counting measure is an
ordinary supremum (every point has positive counting measure).  For `p ≠ 0, ⊤` a single point has
counting measure `1`, so `‖f n‖ₑ ^ p.toReal ≤ ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂count` and extraction of the
`(1/p.toReal)`-th root (using `0 < p.toReal`) bounds every value by `‖f‖_{ℓᵖ} < ⊤`.

This is `Work.KMTAreas.A7.eLpNorm_finite_bounded` without the hypothesis `1 ≤ p`
(so it applies to the exponents `0 < p < 1` as well). -/
theorem bounded_of_eLpNorm_count_lt_top {p : ENNReal} (hp : p ≠ 0) {f : ℤ → ℂ}
    (h : MeasureTheory.eLpNorm f p MeasureTheory.Measure.count < ⊤) :
    ∃ C : ℝ, ∀ y : ℤ, ‖f y‖ ≤ C := by
  by_cases hptop : p = ⊤
  · -- `p = ⊤`: the essential supremum over the counting measure is an ordinary supremum.
    subst hptop
    rw [MeasureTheory.eLpNorm_exponent_top (hf := by pw_aesm),
        MeasureTheory.eLpNormEssSup_lt_top_iff_isBoundedUnder] at h
    obtain ⟨C, hC⟩ := h
    refine ⟨(C : ℝ), fun n => ?_⟩
    have h1 : ‖f n‖₊ ≤ C := (MeasureTheory.Measure.ae_count_iff.mp hC) n
    exact_mod_cast h1
  · -- `p ≠ 0, ⊤`: bound each value by the `ℒᵖ`-seminorm of `f`.
    have hq : p.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp, hptop⟩
    have hqpos : 0 < p.toReal := ENNReal.toReal_pos hp hptop
    set A : ENNReal := MeasureTheory.eLpNorm f p MeasureTheory.Measure.count with hA
    have hAtop : A ≠ ⊤ := by rw [hA]; exact h.ne
    refine ⟨A.toReal, fun n => ?_⟩
    have hstep : ‖f n‖ₑ ^ p.toReal
        ≤ ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂MeasureTheory.Measure.count := by
      rw [MeasureTheory.lintegral_count]
      exact ENNReal.le_tsum (f := fun a : ℤ => ‖f a‖ₑ ^ p.toReal) n
    have hrpow : (‖f n‖ₑ ^ p.toReal) ^ (1 / p.toReal) = ‖f n‖ₑ := by
      rw [← ENNReal.rpow_mul, mul_one_div_cancel hq, ENNReal.rpow_one]
    have hle : ‖f n‖ₑ ≤ A := by
      calc ‖f n‖ₑ = (‖f n‖ₑ ^ p.toReal) ^ (1 / p.toReal) := hrpow.symm
        _ ≤ (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂MeasureTheory.Measure.count) ^ (1 / p.toReal) :=
              ENNReal.rpow_le_rpow hstep (one_div_pos.mpr hqpos).le
        _ = A := by
              rw [hA]
              exact (MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (f := f) hp hptop).symm
    have hne : ‖f n‖ₑ ≠ ⊤ := ne_top_of_le_ne_top hAtop hle
    have h2 := (ENNReal.toReal_le_toReal hne hAtop).mpr hle
    rwa [enorm_eq_nnnorm, toReal_coe_nnnorm] at h2

end Work.KMTAreas.A7
