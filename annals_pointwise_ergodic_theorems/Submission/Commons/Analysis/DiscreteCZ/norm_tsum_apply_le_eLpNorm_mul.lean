import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace Commons.Analysis.DiscreteCZ

open MeasureTheory ENNReal

/-- **Hölder's inequality for a discrete bilinear pairing.**
For a sequence `Φ : ℤ → (H →L[ℂ] ℂ)` of bounded linear functionals and a sequence `f : ℤ → H`,
the norm of the "pairing" `∑' x, Φ x (f x)` is bounded by the product of the `ℓ^q`-norm of `Φ`
and the `ℓ^p`-norm of `f`, for conjugate exponents `p, q`. -/
theorem norm_tsum_apply_le_eLpNorm_mul {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (Φ : ℤ → (H →L[ℂ] ℂ)) (f : ℤ → H) {p q : ℝ} (hpq : p.HolderConjugate q) :
    ‖∑' x : ℤ, Φ x (f x)‖ₑ
      ≤ MeasureTheory.eLpNorm Φ (ENNReal.ofReal q) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        * MeasureTheory.eLpNorm f (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  have hqpos : 0 < q := hpq.symm.pos
  have hppos : 0 < p := hpq.pos
  have hpt : ∀ x : ℤ, ‖Φ x (f x)‖ₑ ≤ ‖Φ x‖ₑ * ‖f x‖ₑ := by
    intro x
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul (norm_nonneg (Φ x))]
    exact ENNReal.ofReal_le_ofReal ((Φ x).le_opNorm (f x))
  calc ‖∑' x : ℤ, Φ x (f x)‖ₑ
      ≤ ∑' x : ℤ, ‖Φ x (f x)‖ₑ := enorm_tsum_le_tsum_enorm
    _ ≤ ∑' x : ℤ, ‖Φ x‖ₑ * ‖f x‖ₑ := ENNReal.tsum_le_tsum hpt
    _ = ∫⁻ x : ℤ, ‖Φ x‖ₑ * ‖f x‖ₑ ∂(Measure.count : Measure ℤ) :=
        (lintegral_count (fun x : ℤ => ‖Φ x‖ₑ * ‖f x‖ₑ)).symm
    _ ≤ (∫⁻ x : ℤ, ‖Φ x‖ₑ ^ q ∂(Measure.count : Measure ℤ)) ^ (1 / q)
          * (∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂(Measure.count : Measure ℤ)) ^ (1 / p) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ℤ) (p := q) (q := p)
          hpq.symm (f := fun x : ℤ => ‖Φ x‖ₑ) (g := fun x : ℤ => ‖f x‖ₑ)
          (Measurable.of_discrete.aemeasurable) (Measurable.of_discrete.aemeasurable)
    _ = MeasureTheory.eLpNorm Φ (ENNReal.ofReal q) (Measure.count : Measure ℤ)
          * MeasureTheory.eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := Φ) (μ := (Measure.count : Measure ℤ))
              (ENNReal.ofReal_pos.mpr hqpos).ne' ENNReal.ofReal_ne_top AEStronglyMeasurable.of_discrete,
            eLpNorm_eq_lintegral_rpow_enorm_toReal (f := f) (μ := (Measure.count : Measure ℤ))
              (ENNReal.ofReal_pos.mpr hppos).ne' ENNReal.ofReal_ne_top AEStronglyMeasurable.of_discrete]
        simp [ENNReal.toReal_ofReal hqpos.le, ENNReal.toReal_ofReal hppos.le]

end Commons.Analysis.DiscreteCZ