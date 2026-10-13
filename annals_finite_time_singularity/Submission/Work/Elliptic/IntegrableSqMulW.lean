import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open MeasureTheory Set Filter
open scoped Real Topology

/-- On `(1,∞)` the weight `w(z) = (1+z)²/z²` is at least `1`. -/
private lemma one_le_w_of_one_lt {z : ℝ} (hz : 1 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  rw [one_le_div (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith [sq_nonneg (1 + z), sq_nonneg z]

/-- If `f² w²` is integrable on `(1,∞)`, so is `f²`, with no larger integral. -/
theorem IntegrableSqMulW {f : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun z : ℝ => (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun z : ℝ => (f z) ^ 2) (Set.Ioi 1) ∧
      ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2
        ≤ ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
  have hw_meas : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
    have h : Measurable (fun z : ℝ => Work.Spaces.w z) := by
      simp only [Work.Spaces.w]
      fun_prop
    exact h.pow_const 2
  -- pointwise bound on `(1,∞)`: `f² ≤ f² · w²`
  have hpt : ∀ᵐ z ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      (f z) ^ 2 ≤ (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ (one_le_w_of_one_lt hz))
  -- on `(1,∞)`, `f² = (f² w²)/w²`
  have heq : (fun z : ℝ => (f z) ^ 2 * (Work.Spaces.w z) ^ 2 / (Work.Spaces.w z) ^ 2)
      =ᵐ[volume.restrict (Set.Ioi (1 : ℝ))] (fun z : ℝ => (f z) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
      have := one_le_w_of_one_lt hz
      positivity
    exact mul_div_cancel_right₀ _ hw
  have hf2_meas : AEStronglyMeasurable (fun z : ℝ => (f z) ^ 2)
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    (hint.aestronglyMeasurable.div₀ hw_meas.aestronglyMeasurable).congr heq
  have hf2 : Integrable (fun z : ℝ => (f z) ^ 2) (volume.restrict (Set.Ioi (1 : ℝ))) :=
    hint.mono' hf2_meas (hpt.mono fun z hz => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hz)
  refine ⟨hf2, ?_⟩
  exact integral_mono_ae hf2 hint hpt

end Work.Elliptic
