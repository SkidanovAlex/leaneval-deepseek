import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open MeasureTheory Set

theorem DivSinL2WtCmp (γ : ℝ) (hγ : 0 ≤ 2 - γ) (h : ℝ → ℝ)
    (hcont : ContinuousOn h Work.Spaces.Iθ) :
    ∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
      ≤ ∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 := by
  have hsin_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    rw [Work.Spaces.Iθ] at hθ
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) ≤ (h θ) ^ 2 := by
    intro θ hθ
    exact mul_le_of_le_one_right (sq_nonneg _)
      (Real.rpow_le_one (hsin_nn θ hθ) (Real.sin_le_one _) hγ)
  have hmem : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hint : IntegrableOn (fun θ => (h θ) ^ 2) Work.Spaces.Iθ volume := by
    rw [Work.Spaces.Iθ] at hcont ⊢
    exact (hcont.pow 2).integrableOn_compact isCompact_Icc
  refine MeasureTheory.integral_mono_of_nonneg ?_ hint ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem hmem] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin_nn θ hθ) _)
  · filter_upwards [MeasureTheory.ae_restrict_mem hmem] with θ hθ
    exact hpt θ hθ

end Work.Elliptic
