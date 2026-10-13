import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.StabilityFar.Decay.integrable_indicator_inv_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl

open MeasureTheory

/-- The pointwise arithmetic behind the domination of the Biot--Savart-type weight
`‖x-y‖⁻³ · ⟪y-x,v⟫` by the integrable weight `‖x-y‖⁻²`: the extra factor `‖x-y‖` is
absorbed by the extra inverse power.  (The identity holds for all real `a`, with the
convention `0⁻¹ = 0`.) -/
private lemma inv_cube_mul_self_eq (a : ℝ) : (a ^ (3 : ℕ))⁻¹ * a = (a ^ (2 : ℕ))⁻¹ := by
  rcases eq_or_ne a 0 with h | h
  · rw [h]; norm_num
  · field_simp

/-- **The vector-valued Biot--Savart kernel against a fixed vector is `L¹`.**  For a
vorticity `ω` that is a.e.-strongly-measurable, bounded by `M` and supported in the closed ball
`B(0,R)`, the integrand

  `y ↦ ‖x-y‖⁻³ • (⟪y-x,v⟫ • ω y)`

is Bochner-integrable, for every `x` and `v` — including at the singular point `y = x`.

Indeed `⟪y-x,v⟫` is `O(‖y-x‖)`, so the integrand is dominated by `M‖v‖·‖x-y‖⁻²` on the support
ball, which is integrable in `ℝ³` (`Work.StabilityFar.Decay.integrable_indicator_inv_sq`), and it
vanishes identically off that ball. -/
theorem integrable_inv_cube_inner_smul {ω : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3} {M R : ℝ}
    (hM : 0 ≤ M) (hbdd : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (x : Work.FTS.BSSwirl.R3) (v : Work.FTS.BSSwirl.R3) :
    MeasureTheory.Integrable
      (fun y : Work.FTS.BSSwirl.R3 =>
        ((‖x - y‖ ^ (3 : ℕ))⁻¹ : ℝ) • (inner ℝ (y - x) v • ω y))
      MeasureTheory.volume := by
  classical
  -- a.e.-strong-measurability: the scalar weight `‖x-y‖⁻³ · ⟪y-x,v⟫` is measurable, and the
  -- pointwise product of a measurable scalar with an a.e.-strongly-measurable vector field is
  -- a.e.-strongly-measurable.
  have haesm : AEStronglyMeasurable
      (fun y : R3 => ((‖x - y‖ ^ (3 : ℕ))⁻¹ : ℝ) • (inner ℝ (y - x) v • ω y)) volume := by
    have hd : AEStronglyMeasurable (fun y : R3 => inner ℝ (y - x) v) volume := by
      have hc : Continuous (fun y : R3 => inner ℝ (y - x) v) := by fun_prop
      exact hc.aestronglyMeasurable
    have hinner : AEStronglyMeasurable (fun y : R3 => inner ℝ (y - x) v • ω y) volume :=
      hd.smul hmeas
    have hcc : AEStronglyMeasurable (fun y : R3 => ((‖x - y‖ ^ (3 : ℕ))⁻¹ : ℝ)) volume := by
      have hm : Measurable (fun y : R3 => ‖x - y‖ ^ (3 : ℕ)) := by fun_prop
      exact (Measurable.inv hm).aestronglyMeasurable
    exact (hcc.smul hinner).congr (Filter.Eventually.of_forall fun y => rfl)
  -- the dominating function: `M‖v‖·‖x-y‖⁻²` on the support ball `B(0,R)`, else `0`.
  have hC : (0 : ℝ) ≤ M * ‖v‖ := mul_nonneg hM (norm_nonneg v)
  refine Integrable.mono' (g := fun y : R3 => (Metric.closedBall (0 : R3) R).indicator
      (fun y => M * ‖v‖ * ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y)
    (Work.StabilityFar.Decay.integrable_indicator_inv_sq x hC) haesm ?_
  -- the pointwise domination, valid everywhere (not merely a.e.)
  filter_upwards with y
  by_cases hy : y ∈ Metric.closedBall (0 : R3) R
  · rw [Set.indicator_of_mem hy]
    have hA : ∀ z : R3, ‖((‖x - y‖ ^ (3 : ℕ))⁻¹ : ℝ) • z‖
        = (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖z‖ := by
      intro z
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hB : ‖inner ℝ (y - x) v • ω y‖ = |inner ℝ (y - x) v| * ‖ω y‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    have hcore : (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖x - y‖ ≤ (‖x - y‖ ^ (2 : ℕ))⁻¹ :=
      le_of_eq (inv_cube_mul_self_eq _)
    calc ‖((‖x - y‖ ^ (3 : ℕ))⁻¹ : ℝ) • (inner ℝ (y - x) v • ω y)‖
        = (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖inner ℝ (y - x) v • ω y‖ := hA _
      _ = (‖x - y‖ ^ (3 : ℕ))⁻¹ * (|inner ℝ (y - x) v| * ‖ω y‖) := by rw [hB]
      _ ≤ (‖x - y‖ ^ (3 : ℕ))⁻¹ * (‖y - x‖ * ‖v‖ * M) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul (abs_real_inner_le_norm _ _) (hbdd y) (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖x - y‖ * (M * ‖v‖) := by
            rw [norm_sub_rev y x]; ring
      _ ≤ (‖x - y‖ ^ (2 : ℕ))⁻¹ * (M * ‖v‖) :=
            mul_le_mul_of_nonneg_right hcore (mul_nonneg hM (norm_nonneg v))
      _ = M * ‖v‖ * (‖x - y‖ ^ (2 : ℕ))⁻¹ := by ring
  · have hω0 : ω y = 0 := by
      by_contra h
      exact hy (hsupp y h)
    rw [Set.indicator_of_notMem hy]
    simp [hω0]

end Work.FTS.BSSwirl
