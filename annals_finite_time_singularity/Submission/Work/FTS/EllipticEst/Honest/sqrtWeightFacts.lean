import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

theorem sqrtWeightFacts {s : Set ℝ} (hs : MeasurableSet s) {p σ : ℝ → ℝ}
    (hσ : ∀ θ ∈ s, 0 ≤ σ θ)
    (hp : MeasureTheory.IntegrableOn (fun θ => p θ ^ 2 * σ θ) s) :
    AEMeasurable (fun θ => Real.sqrt (p θ ^ 2 * σ θ)) (MeasureTheory.volume.restrict s) ∧
    MeasureTheory.Integrable (fun θ => Real.sqrt (p θ ^ 2 * σ θ) ^ 2)
      (MeasureTheory.volume.restrict s) ∧
    (∀ θ ∈ s, Real.sqrt (p θ ^ 2 * σ θ) ^ 2 = p θ ^ 2 * σ θ) ∧
    (∫ θ in s, Real.sqrt (p θ ^ 2 * σ θ) ^ 2) = ∫ θ in s, p θ ^ 2 * σ θ := by
  have hnn : ∀ θ ∈ s, 0 ≤ p θ ^ 2 * σ θ := fun θ hθ => mul_nonneg (sq_nonneg _) (hσ θ hθ)
  have hpt : ∀ θ ∈ s, Real.sqrt (p θ ^ 2 * σ θ) ^ 2 = p θ ^ 2 * σ θ :=
    fun θ hθ => Real.sq_sqrt (hnn θ hθ)
  have hae : (fun θ => Real.sqrt (p θ ^ 2 * σ θ) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict s] (fun θ => p θ ^ 2 * σ θ) :=
    (MeasureTheory.ae_restrict_mem hs).mono fun θ hθ => hpt θ hθ
  exact ⟨hp.aemeasurable.sqrt, hp.congr hae.symm, hpt, MeasureTheory.integral_congr_ae hae⟩

end Work.FTS.EllipticEst.Honest
