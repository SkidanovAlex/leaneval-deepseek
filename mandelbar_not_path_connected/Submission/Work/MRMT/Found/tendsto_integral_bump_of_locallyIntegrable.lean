/-
# Approximate identities converge a.e. to a locally integrable function

For `g : ℂ → ℂ` locally integrable with respect to Lebesgue measure `volume`, and a family
`η i` of `L¹`-normalised bump kernels

* `η i` continuous,
* `∫ u, η i u = 1`,
* `‖η i u‖ ≤ C / (r i)²` (i.e. `η i` is bounded by a constant times the reciprocal of the area
  of the ball in which it lives),
* `support (η i) ⊆ closedBall 0 (r i)` with `0 < r i` and `r i → 0`,

the convolution `z ↦ ∫ u, g (z + u) * η i u` converges to `g z` for almost every `z`.

This is the "Lebesgue point" statement behind the standard fact that a mollification of an
`L¹_loc` function converges to it almost everywhere.  The proof restricts to the full measure set
of Lebesgue points of `g` (supplied by Mathlib's Lebesgue differentiation theorem for the
Besicovitch Vitali family), and then applies the general approximate-identity estimate
`Work.MRMT.Found.tendsto_integral_mul_of_tendsto_average_norm_sub` to the kernel
`y ↦ η i (y - z)`.
-/
import Mathlib
import Submission.Work.MRMT.Found.tendsto_integral_mul_of_tendsto_average_norm_sub

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter
open scoped Topology ENNReal

/-- The Lebesgue volume of the unit ball of `ℂ` is positive. -/
theorem volume_real_ball_one_pos :
    0 < (MeasureTheory.volume : MeasureTheory.Measure ℂ).real (Metric.ball 0 1) := by
  rw [MeasureTheory.measureReal_def]
  exact ENNReal.toReal_pos
    (ne_of_gt (Metric.measure_ball_pos (MeasureTheory.volume : MeasureTheory.Measure ℂ) 0 one_pos))
    measure_ball_lt_top.ne

set_option maxHeartbeats 800000 in
set_option linter.unusedVariables false in
theorem tendsto_integral_bump_of_locallyIntegrable {g : ℂ → ℂ}
    (hg : MeasureTheory.LocallyIntegrable g (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    {η : ℕ → ℂ → ℂ} {r : ℕ → ℝ} (hcont : ∀ i, Continuous (η i))
    (hpos : ∀ i, 0 < r i) (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hint : ∀ i, ∫ u, η i u = 1)
    (hbd : ∃ C : ℝ, ∀ i u, ‖η i u‖ ≤ C / r i ^ 2)
    (hsupp : ∀ i, Function.support (η i) ⊆ Metric.closedBall 0 (r i)) :
    ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), Filter.Tendsto (fun i => ∫ u, g (z + u) * η i u) Filter.atTop (nhds (g z)) := by
  obtain ⟨C, hC⟩ := hbd
  set v : ℝ := (MeasureTheory.volume : MeasureTheory.Measure ℂ).real (Metric.ball 0 1) with hv_def
  have hvpos : 0 < v := by
    rw [hv_def]
    exact volume_real_ball_one_pos
  -- Almost every point is a Lebesgue point of `g`.
  filter_upwards [(Besicovitch.vitaliFamily (MeasureTheory.volume : MeasureTheory.Measure ℂ)).ae_tendsto_average_norm_sub hg]
    with z hz
  have hrz : Filter.Tendsto r Filter.atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hr, Eventually.of_forall hpos⟩
  have havg : Filter.Tendsto
      (fun i => ⨍ y in Metric.closedBall z (r i),
        ‖g y - g z‖ ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ))
      Filter.atTop (nhds 0) :=
    (hz.comp (Besicovitch.tendsto_filterAt (MeasureTheory.volume : MeasureTheory.Measure ℂ) z)).comp hrz
  -- The approximate identity estimate, applied to the shifted kernel `y ↦ η i (y - z)`.
  have hmain : Filter.Tendsto
      (fun i => ∫ y, η i (y - z) * g y ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ))
      Filter.atTop (nhds (g z)) :=
    tendsto_integral_mul_of_tendsto_average_norm_sub (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ))
      (a := fun i => Metric.closedBall z (r i)) (l := Filter.atTop)
      (f := g) (c := g z) (w := fun i y => η i (y - z)) (max C 0 * v)
      havg
      (by filter_upwards with i; exact hg.integrableOn_isCompact (isCompact_closedBall z (r i)))
      (by
        have hfun : (fun i : ℕ => ∫ y, η i (y - z) ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ))
            = fun _ => (1 : ℂ) := by
          funext i
          rw [MeasureTheory.integral_sub_right_eq_self (fun u : ℂ => η i u) z]
          exact hint i
        rw [hfun]
        exact tendsto_const_nhds)
      (by
        filter_upwards with i y hy
        have hball : y - z ∈ Metric.closedBall (0 : ℂ) (r i) := hsupp i hy
        rw [Metric.mem_closedBall] at hball ⊢
        simpa [dist_eq_norm] using hball)
      (by
        filter_upwards with i x
        have hV : (MeasureTheory.volume : MeasureTheory.Measure ℂ).real (Metric.closedBall z (r i))
            = (r i) ^ 2 * v := by
          rw [hv_def,
            MeasureTheory.Measure.addHaar_real_closedBall
              (MeasureTheory.volume : MeasureTheory.Measure ℂ) z (hpos i).le,
            Complex.finrank_real_complex]
        calc ‖η i (x - z)‖ ≤ C / (r i) ^ 2 := hC i (x - z)
          _ ≤ max C 0 / (r i) ^ 2 := div_le_div_of_nonneg_right (le_max_left C 0) (sq_nonneg _)
          _ = (max C 0 * v) / ((r i) ^ 2 * v) :=
              (mul_div_mul_right (max C 0) ((r i) ^ 2) (ne_of_gt hvpos)).symm
          _ = (max C 0 * v) /
                (MeasureTheory.volume : MeasureTheory.Measure ℂ).real (Metric.closedBall z (r i)) := by
              rw [hV])
  -- Rewrite `∫ y, η i (y - z) * g y` as `∫ u, g (z + u) * η i u` by the substitution `y = z + u`.
  refine hmain.congr' (Eventually.of_forall fun i => ?_)
  rw [show (∫ y : ℂ, η i (y - z) * g y ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ))
      = ∫ y : ℂ, (fun t : ℂ => η i t * g (z + t)) (y - z)
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ) from
    MeasureTheory.integral_congr_ae (Eventually.of_forall fun y => by
      simp only
      rw [show z + (y - z) = y by ring])]
  rw [MeasureTheory.integral_sub_right_eq_self (fun t : ℂ => η i t * g (z + t)) z]
  exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun t => by simp only [mul_comm])

end Work.MRMT.Found
