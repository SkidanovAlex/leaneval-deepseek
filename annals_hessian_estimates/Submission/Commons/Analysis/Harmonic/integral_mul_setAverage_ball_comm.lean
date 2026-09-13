import Mathlib.MeasureTheory.Integral.Average
import Submission.Commons.Analysis.Measure.setAverage_mul_const
import Submission.Commons.Analysis.Harmonic.integral_mul_integral_ball_comm
import Submission.Commons.Analysis.Harmonic.integrableOn_mul_ballIntegral
import Submission.Commons.Analysis.Harmonic.integrable_mul_ballIntegral

namespace Commons.Analysis.Harmonic

open MeasureTheory Metric Set Filter Function
open scoped Topology RealInnerProductSpace InnerProductSpace ENNReal BigOperators

open MeasureTheory Metric Set Filter Function in
open scoped Topology RealInnerProductSpace InnerProductSpace ENNReal BigOperators in
theorem integral_mul_setAverage_ball_comm {n : ℕ} {u φ : EuclideanSpace ℝ (Fin n) → ℝ}
    {K : Set (EuclideanSpace ℝ (Fin n))} {r : ℝ} (hr : 0 < r) (hKc : IsCompact K)
    (hφcont : Continuous φ) (hφsupp : tsupport φ ⊆ K)
    (huc : ContinuousOn u (Metric.cthickening r K)) :
    (∫ x in K, φ x * (⨍ y in Metric.ball x r, (u y - u x)))
      = ∫ y, u y * (⨍ x in Metric.ball y r, (φ x - φ y)) := by
  classical
  -- the constant value of `volume.real (ball x r)`
  set c : ℝ := volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) with hcdef
  have hc : ∀ x : EuclideanSpace ℝ (Fin n), volume.real (Metric.ball x r) = c := by
    intro x
    rw [hcdef, Measure.real_def, Measure.real_def, Measure.addHaar_ball_center volume x r]
  have hc_ne : c ≠ 0 := by
    rw [hcdef, Measure.real_def]
    exact (ENNReal.toReal_pos (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) hr).ne'
      isBounded_ball.measure_lt_top.ne).ne'
  have hcinv : c⁻¹ * c = 1 := inv_mul_cancel₀ hc_ne
  -- `K` is contained in its `r`-cthickening
  have hKsubC : K ⊆ Metric.cthickening r K := fun x hx =>
    mem_cthickening_of_dist_le x x r K hx (by simpa using hr.le)
  -- ===== left-hand side =====
  have hL1 : ∀ x ∈ K, φ x * (⨍ y in Metric.ball x r, (u y - u x))
      = c⁻¹ * (φ x * (∫ y in Metric.ball x r, u y)) - φ x * u x := by
    intro x hx
    have hsub : Metric.ball x r ⊆ Metric.cthickening r K := fun y hy =>
      mem_cthickening_of_dist_le y x r K hx (le_of_lt hy)
    have hballfin : volume (Metric.ball x r) ≠ ∞ := isBounded_ball.measure_lt_top.ne
    have huib : IntegrableOn u (Metric.ball x r) volume :=
      huc.integrableOn_of_subset_isCompact hKc.cthickening isOpen_ball.measurableSet hsub hballfin
    have hsplit : (∫ y in Metric.ball x r, (u y - u x))
        = (∫ y in Metric.ball x r, u y) - c * u x := by
      rw [integral_sub huib (integrableOn_const hballfin), setIntegral_const, hc x, smul_eq_mul]
    have key : (⨍ y in Metric.ball x r, (u y - u x))
        = c⁻¹ * ((∫ y in Metric.ball x r, u y) - c * u x) := by
      rw [setAverage_eq, hc x, hsplit, smul_eq_mul]
    rw [key]
    have h1 : c⁻¹ * ((∫ y in Metric.ball x r, u y) - c * u x)
        = c⁻¹ * (∫ y in Metric.ball x r, u y) - u x := by
      rw [mul_sub, ← mul_assoc, hcinv, one_mul]
    rw [h1, mul_sub]; ring
  have hLah : IntegrableOn (fun x => c⁻¹ * (φ x * (∫ y in Metric.ball x r, u y))) K :=
    ((Commons.Analysis.Harmonic.integrableOn_mul_ballIntegral hr hKc hφcont hφsupp huc) :
      Integrable _ (volume.restrict K)).const_mul c⁻¹
  have hLuh : IntegrableOn (fun x => φ x * u x) K :=
    (hφcont.continuousOn.mul (huc.mono hKsubC)).integrableOn_compact hKc
  have hLHS : (∫ x in K, φ x * (⨍ y in Metric.ball x r, (u y - u x)))
      = c⁻¹ * (∫ x in K, φ x * (∫ y in Metric.ball x r, u y)) - (∫ x in K, φ x * u x) := by
    rw [setIntegral_congr_fun hKc.measurableSet (fun x hx => hL1 x hx)]
    rw [integral_sub hLah hLuh, integral_const_mul]
  -- ===== right-hand side =====
  have hR1 : ∀ y : EuclideanSpace ℝ (Fin n), u y * (⨍ x in Metric.ball y r, (φ x - φ y))
      = c⁻¹ * (u y * (∫ x in Metric.ball y r, φ x)) - u y * φ y := by
    intro y
    have hballfin : volume (Metric.ball y r) ≠ ∞ := isBounded_ball.measure_lt_top.ne
    have hφib : IntegrableOn φ (Metric.ball y r) volume :=
      hφcont.continuousOn.integrableOn_of_subset_isCompact (isCompact_closedBall y r)
        isOpen_ball.measurableSet Metric.ball_subset_closedBall hballfin
    have hsplit : (∫ x in Metric.ball y r, (φ x - φ y))
        = (∫ x in Metric.ball y r, φ x) - c * φ y := by
      rw [integral_sub hφib (integrableOn_const hballfin), setIntegral_const, hc y, smul_eq_mul]
    have key : (⨍ x in Metric.ball y r, (φ x - φ y))
        = c⁻¹ * ((∫ x in Metric.ball y r, φ x) - c * φ y) := by
      rw [setAverage_eq, hc y, hsplit, smul_eq_mul]
    rw [key]
    have h1 : c⁻¹ * ((∫ x in Metric.ball y r, φ x) - c * φ y)
        = c⁻¹ * (∫ x in Metric.ball y r, φ x) - φ y := by
      rw [mul_sub, ← mul_assoc, hcinv, one_mul]
    rw [h1, mul_sub]; ring
  have hRah : Integrable (fun y => c⁻¹ * (u y * (∫ x in Metric.ball y r, φ x))) :=
    (Commons.Analysis.Harmonic.integrable_mul_ballIntegral hr hKc hφcont hφsupp huc).const_mul c⁻¹
  have hKprint : IntegrableOn (fun y => u y * φ y) K :=
    (huc.mono hKsubC).mul hφcont.continuousOn |>.integrableOn_compact hKc
  have hRuh : Integrable (fun y => u y * φ y) := by
    refine (hKprint.integrable_indicator hKc.measurableSet).congr ?_
    filter_upwards with y
    by_cases hy : y ∈ K
    · simp only [Set.indicator_of_mem hy]
    · have hφy : φ y = 0 := image_eq_zero_of_notMem_tsupport (fun hc => hy (hφsupp hc))
      simp only [Set.indicator_of_notMem hy, hφy, mul_zero]
  have hRHS : (∫ y, u y * (⨍ x in Metric.ball y r, (φ x - φ y)))
      = c⁻¹ * (∫ y, u y * (∫ x in Metric.ball y r, φ x)) - (∫ y, u y * φ y) := by
    rw [integral_congr_ae (Eventually.of_forall hR1)]
    rw [integral_sub hRah hRuh, integral_const_mul]
  -- ===== the two diagonal terms coincide =====
  have hdiag : (∫ x in K, φ x * u x) = ∫ y, u y * φ y := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun hc => hx (hφsupp hc)), zero_mul])]
    exact integral_congr_ae (Eventually.of_forall (fun x => mul_comm _ _))
  rw [hLHS, hRHS, hdiag,
    Commons.Analysis.Harmonic.integral_mul_integral_ball_comm hr hKc hφcont hφsupp huc]

end Commons.Analysis.Harmonic