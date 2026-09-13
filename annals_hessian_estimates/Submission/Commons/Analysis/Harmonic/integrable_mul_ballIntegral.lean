import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace Commons.Analysis.Harmonic

open MeasureTheory Metric Set Filter Function in
open scoped Topology RealInnerProductSpace InnerProductSpace ENNReal BigOperators in
theorem integrable_mul_ballIntegral {n : ℕ} {u φ : EuclideanSpace ℝ (Fin n) → ℝ}
    {K : Set (EuclideanSpace ℝ (Fin n))} {r : ℝ} (hr : 0 < r) (hKc : IsCompact K)
    (hφcont : Continuous φ) (hφsupp : tsupport φ ⊆ K)
    (huc : ContinuousOn u (Metric.cthickening r K)) :
    Integrable (fun y => u y * (∫ x in Metric.ball y r, φ x)) := by
  classical
  let S : Set (EuclideanSpace ℝ (Fin n)) := Metric.cthickening r K
  have hSmeas : MeasurableSet S := isClosed_cthickening.measurableSet
  have hSc : IsCompact S := hKc.cthickening
  -- The ball integral as a function of the center is continuous.
  let g : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => ∫ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r, φ (y + z)
  have hgc : Continuous g := by
    have huncurry : Continuous
        (Function.uncurry (fun (y z : EuclideanSpace ℝ (Fin n)) => φ (y + z))) := by
      have : Function.uncurry (fun (y z : EuclideanSpace ℝ (Fin n)) => φ (y + z))
          = fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => φ (p.1 + p.2) := rfl
      rw [this]
      exact hφcont.comp (continuous_fst.add continuous_snd)
    exact continuous_parametric_integral_of_continuous huncurry
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) r)
  -- Almost everywhere equality of open and closed balls.
  have hball_closed : ∀ y : EuclideanSpace ℝ (Fin n),
      (Metric.ball y r : Set (EuclideanSpace ℝ (Fin n))) =ᵐ[volume] Metric.closedBall y r := by
    intro y
    have hsphere : volume (Metric.sphere y r) = 0 :=
      MeasureTheory.Measure.addHaar_sphere_of_ne_zero volume y (ne_of_gt hr)
    refine ae_eq_of_subset_of_measure_ge ball_subset_closedBall ?_
      measurableSet_ball.nullMeasurableSet (isCompact_closedBall y r).measure_lt_top.ne
    calc volume (Metric.closedBall y r) ≤ volume (Metric.ball y r ∪ Metric.sphere y r) := by
          apply measure_mono
          intro x hx
          rw [Metric.mem_closedBall] at hx
          rcases lt_or_eq_of_le hx with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [Metric.mem_sphere]; exact h)
      _ ≤ volume (Metric.ball y r) + volume (Metric.sphere y r) := measure_union_le _ _
      _ = volume (Metric.ball y r) := by rw [hsphere, add_zero]
  -- The ball integral equals `g`.
  have hg_ball : ∀ y : EuclideanSpace ℝ (Fin n),
      (∫ x in Metric.ball y r, φ x) = g y := by
    intro y
    have hpoint : ∀ x : EuclideanSpace ℝ (Fin n),
        (Metric.closedBall y r).indicator φ x
          = (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r).indicator
              (fun w => φ (y + w)) (x - y) := by
      intro x
      by_cases hx : x ∈ Metric.closedBall y r
      · rw [Set.indicator_of_mem hx]
        have hxy : x - y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r := by
          rw [Metric.mem_closedBall] at hx ⊢
          rw [dist_eq_norm] at hx ⊢
          simpa using hx
        rw [Set.indicator_of_mem hxy]
        have hsum : y + (x - y) = x := by abel
        rw [hsum]
      · rw [Set.indicator_of_notMem hx]
        have hxy : x - y ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r := by
          intro h
          apply hx
          rw [Metric.mem_closedBall] at h ⊢
          rw [dist_eq_norm] at h ⊢
          simpa using h
        rw [Set.indicator_of_notMem hxy]
    have hmid : ∫ x, (Metric.closedBall y r).indicator φ x
        = ∫ x, (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r).indicator
            (fun w => φ (y + w)) x := by
      have h1 : ∫ x, (Metric.closedBall y r).indicator φ x
          = ∫ x, (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r).indicator
              (fun w => φ (y + w)) (x - y) := by
        apply integral_congr_ae
        filter_upwards with x
        exact hpoint x
      have h2 : ∫ x, (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r).indicator
              (fun w => φ (y + w)) (x - y)
          = ∫ x, (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r).indicator
              (fun w => φ (y + w)) x := by
        have := integral_add_right_eq_self (μ := volume)
          (fun x : EuclideanSpace ℝ (Fin n) =>
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r).indicator (fun w => φ (y + w)) x)
          (-y)
        simpa only [sub_eq_add_neg] using this
      rw [h1, h2]
    have hCB : ∫ x in Metric.closedBall y r, φ x
        = ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r, φ (y + x) := by
      calc ∫ x in Metric.closedBall y r, φ x
          = ∫ x, (Metric.closedBall y r).indicator φ x :=
            (integral_indicator measurableSet_closedBall).symm
        _ = ∫ x, (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r).indicator
              (fun w => φ (y + w)) x := hmid
        _ = ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r, φ (y + x) :=
            integral_indicator measurableSet_closedBall
    have hball : (∫ x in Metric.ball y r, φ x) = ∫ x in Metric.closedBall y r, φ x :=
      setIntegral_congr_set (hball_closed y)
    rw [hball, hCB]
  -- The ball integral vanishes off `S`.
  have hg_zero : ∀ y : EuclideanSpace ℝ (Fin n), y ∉ S → g y = 0 := by
    intro y hy
    rw [← hg_ball y]
    have hφzero : ∀ x ∈ Metric.ball y r, φ x = 0 := by
      intro x hx
      by_contra hne
      have hxK : x ∈ K := hφsupp (subset_closure (Function.mem_support.mpr hne))
      have : y ∈ Metric.thickening r K := by
        rw [Metric.mem_thickening_iff]
        exact ⟨x, hxK, by rw [dist_comm]; exact hx⟩
      exact hy (Metric.thickening_subset_cthickening r K this)
    have : ∫ x in Metric.ball y r, φ x = ∫ x in Metric.ball y r, (0 : ℝ) :=
      setIntegral_congr_fun measurableSet_ball (fun x hx => hφzero x hx)
    rw [this]; simp
  have hcont : ContinuousOn (fun y => u y * g y) S := huc.mul hgc.continuousOn
  have hintOn : IntegrableOn (fun y => u y * g y) S := hcont.integrableOn_compact hSc
  have hint_ind : Integrable (S.indicator (fun y => u y * g y)) :=
    hintOn.integrable_indicator hSmeas
  have hfun_eq : (fun y => u y * g y) = S.indicator (fun y => u y * g y) := by
    funext y
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, hg_zero y hy, mul_zero]
  have hint : Integrable (fun y => u y * g y) := by
    rw [hfun_eq]; exact hint_ind
  refine hint.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [hg_ball y]

end Commons.Analysis.Harmonic