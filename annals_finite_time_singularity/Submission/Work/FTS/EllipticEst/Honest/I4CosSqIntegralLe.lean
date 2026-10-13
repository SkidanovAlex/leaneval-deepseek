import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.I4SliceDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open MeasureTheory Set

/-- On `Iθ = [0, π/2]` the factor `cos²θ` is at most `1` and the weight `I4sig` is
non-negative, so the weighted integral of `(cos θ · ψ)²` is dominated by that of `ψ²`. -/
theorem I4CosSqIntegralLe (Φ : ℝ → ℝ)
    (hA : MeasureTheory.IntegrableOn (fun θ => I4psi Φ θ ^ 2 * I4sig θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (Real.cos θ * I4psi Φ θ) ^ 2 * I4sig θ)
      ≤ ∫ θ in Work.Spaces.Iθ, I4psi Φ θ ^ 2 * I4sig θ := by
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (Real.cos θ * I4psi Φ θ) ^ 2 * I4sig θ ≤ I4psi Φ θ ^ 2 * I4sig θ := by
    intro θ hθ
    have hσ : 0 ≤ I4sig θ := I4sig_nonneg hθ
    have hψ : 0 ≤ I4psi Φ θ ^ 2 := sq_nonneg _
    have hc : (Real.cos θ) ^ 2 ≤ 1 := Real.cos_sq_le_one θ
    have h1 : (Real.cos θ) ^ 2 * (I4psi Φ θ ^ 2 * I4sig θ)
        ≤ 1 * (I4psi Φ θ ^ 2 * I4sig θ) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hψ hσ)
    nlinarith [h1]
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    simpa only [Work.Spaces.Iθ] using measurableSet_Icc
  have hbdd : MeasureTheory.IntegrableOn
      (fun θ => (Real.cos θ) ^ 2 * (I4psi Φ θ ^ 2 * I4sig θ)) Work.Spaces.Iθ :=
    hA.bdd_mul (c := 1) (Real.continuous_cos.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun θ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.cos θ))]
        exact Real.cos_sq_le_one θ))
  have hf : MeasureTheory.IntegrableOn
      (fun θ => (Real.cos θ * I4psi Φ θ) ^ 2 * I4sig θ) Work.Spaces.Iθ :=
    hbdd.congr_fun (fun θ _ => by ring) hIθ
  exact MeasureTheory.setIntegral_mono_on hf hA hIθ hpt

end Work.FTS.EllipticEst.Honest
