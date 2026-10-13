/-
# The cutoff integral `∫ fcut(‖z‖/ε)/‖z‖ · g z` converges to `∫ ‖z‖⁻¹ · g z`

For a continuous compactly supported `g : ℝ³ → ℝ`,

  `∫ z, fcut (‖z‖/ε) / ‖z‖ * g z  →  ∫ z, ‖z‖⁻¹ * g z`   as `ε → 0⁺`,

where `fcut` is the smooth step of `Work.FTS.BSSwirl.inv_norm_cut` (equal to `0` on `(-∞,1]`
and to `1` on `[2,∞)`).

This is the elementary truncation step of the `BSSwirl` area: the singular kernel `‖z‖⁻¹` is
*locally integrable* in dimension `3` (`∫_{‖z‖<1} ‖z‖⁻¹ = 4π/2 < ∞`), so cutting the kernel off
near the origin does not change the integral in the limit.  The proof is the dominated
convergence theorem with dominating function
`z ↦ max C 1 * ‖z‖⁻¹ · 1_{B(0,R)}`, where `B(0,R)` contains the support of `g` and `max C 1`
bounds `|g|`.

The pointwise limit is `1/‖z‖ * g z` for every `z ≠ 0` (where `fcut (‖z‖/ε) → 1` because
`‖z‖/ε → ∞`), and the exceptional set `{0}` is null.
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Submission.Work.FTS.BSSwirl.inv_norm_cut
import Submission.Work.FTS.BSSwirl.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-- `‖·‖⁻¹` is locally integrable on `ℝ³`: it is a Riesz kernel of order `1` in dimension `3`,
so it is dominated by `‖·‖ ^ (-1)` with `1 < 3`. -/
private lemma locallyIntegrable_inv_norm_fts :
    LocallyIntegrable (fun z : R3 => (‖z‖)⁻¹) volume := by
  refine MeasureTheory.locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) ?_ ?_ ?_ ?_
  · simp
  · simp
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)), Real.rpow_neg_one,
      one_mul]
  · exact (Measurable.inv measurable_norm).aestronglyMeasurable

/-- **The truncation of the singular kernel `‖z‖⁻¹` converges to the kernel itself.**

`∫ z, fcut(‖z‖/ε)/‖z‖ · g z  →  ∫ z, ‖z‖⁻¹ · g z` as `ε → 0⁺`, for `g` continuous with compact
support.  Dominated convergence: pointwise `fcut(‖z‖/ε) → 1` for `z ≠ 0`, and the integrand is
dominated by `‖z‖⁻¹ |g z|`, integrable because `g` is supported in a ball and `‖·‖⁻¹` is locally
integrable. -/
theorem tendsto_fcut_div_mul {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) :
    Filter.Tendsto (fun ε : ℝ => ∫ z, Work.FTS.BSSwirl.fcut (‖z‖ / ε) / ‖z‖ * g z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ z, ‖z‖⁻¹ * g z)) := by
  -- A ball containing the support of `g`, and a bound for `|g|`.
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : R3)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : R3) R).exists_bound_of_continuousOn hg.continuousOn
  have hM0 : (0 : ℝ) ≤ max C 1 := le_trans zero_le_one (le_max_right _ _)
  have hbdd : ∀ z : R3, |g z| ≤ max C 1 := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : R3) R
    · have h := hC z hz
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_max_left _ _)
    · have hz0 : g z = 0 := by
        by_contra h
        exact hz (hR (subset_tsupport g h))
      rw [hz0, abs_zero]
      exact le_trans zero_le_one (le_max_right _ _)
  -- The dominating function.
  set bound : R3 → ℝ :=
    (Metric.closedBall (0 : R3) R).indicator (fun z => max C 1 * (‖z‖)⁻¹) with hbounddef
  have hbound_int : Integrable bound := by
    rw [hbounddef, MeasureTheory.integrable_indicator_iff measurableSet_closedBall]
    exact (locallyIntegrable_inv_norm_fts.integrableOn_isCompact
      (isCompact_closedBall (0 : R3) R)).const_mul _
  -- Measurability of the integrand.
  have hF_meas : ∀ᶠ ε : ℝ in (𝓝[>] (0 : ℝ)),
      AEStronglyMeasurable (fun z : R3 => fcut (‖z‖ / ε) / ‖z‖ * g z) volume := by
    refine Filter.Eventually.of_forall (fun ε => ?_)
    have h1 : Measurable (fun z : R3 => fcut (‖z‖ / ε)) :=
      (contDiff_fcut 0).continuous.measurable.comp ((continuous_norm.div_const ε).measurable)
    exact ((h1.div measurable_norm).mul hg.measurable).aestronglyMeasurable
  -- Pointwise domination by `bound`.
  have h_bound : ∀ᶠ ε : ℝ in (𝓝[>] (0 : ℝ)),
      ∀ᵐ z ∂(volume : Measure (R3)), ‖fcut (‖z‖ / ε) / ‖z‖ * g z‖ ≤ bound z := by
    refine Filter.Eventually.of_forall
      (fun ε => Filter.Eventually.of_forall (fun z => ?_))
    have hnorm : ‖fcut (‖z‖ / ε) / ‖z‖ * g z‖ = |fcut (‖z‖ / ε)| * (‖z‖)⁻¹ * |g z| := by
      simp only [norm_mul, norm_div, Real.norm_eq_abs]
      rw [abs_of_nonneg (norm_nonneg z), div_eq_mul_inv]
    rw [hnorm]
    by_cases hz : z ∈ Metric.closedBall (0 : R3) R
    · rw [hbounddef, Set.indicator_of_mem hz]
      have ha : |fcut (‖z‖ / ε)| ≤ 1 :=
        abs_le.mpr ⟨by linarith [fcut_nonneg (‖z‖ / ε)], fcut_le_one _⟩
      have hc0 : (0 : ℝ) ≤ (‖z‖)⁻¹ := inv_nonneg.mpr (norm_nonneg z)
      have hmain : |fcut (‖z‖ / ε)| * (‖z‖)⁻¹ * |g z| ≤ max C 1 * (‖z‖)⁻¹ := by
        calc |fcut (‖z‖ / ε)| * (‖z‖)⁻¹ * |g z|
            = (|fcut (‖z‖ / ε)| * (‖z‖)⁻¹) * |g z| := by ring
          _ ≤ (1 * (‖z‖)⁻¹) * max C 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_right ha hc0) (hbdd z) (abs_nonneg _)
                (mul_nonneg zero_le_one hc0)
          _ = max C 1 * (‖z‖)⁻¹ := by ring
      exact hmain
    · rw [hbounddef, Set.indicator_of_notMem hz]
      have hz0 : g z = 0 := by
        by_contra h
        exact hz (hR (subset_tsupport g h))
      simp [hz0]
  -- The pointwise limit (for *every* `z`, including `z = 0`).
  have h_lim : ∀ᵐ z ∂(volume : Measure (R3)),
      Tendsto (fun ε : ℝ => fcut (‖z‖ / ε) / ‖z‖ * g z) (𝓝[>] (0 : ℝ))
        (𝓝 ((‖z‖)⁻¹ * g z)) := by
    refine Filter.Eventually.of_forall (fun z => ?_)
    by_cases hz : z = 0
    · subst hz
      simp only [norm_zero, zero_div, fcut_zero, inv_zero]
      exact tendsto_const_nhds
    · have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have htend : Tendsto (fun ε : ℝ => ‖z‖ / ε) (𝓝[>] (0 : ℝ)) atTop := by
        have h2 := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hpos
        simpa [div_eq_mul_inv] using h2
      have hfcut : Tendsto fcut atTop (𝓝 (1 : ℝ)) :=
        tendsto_nhds_of_eventually_eq
          ((Filter.eventually_ge_atTop (2 : ℝ)).mono (fun t ht => fcut_of_two_le ht))
      have h1 : Tendsto (fun ε : ℝ => fcut (‖z‖ / ε)) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
        hfcut.comp htend
      have h2 := (h1.div_const ‖z‖).mul_const (g z)
      simpa [div_eq_mul_inv, one_mul] using h2
  exact tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (R3)))
    bound hF_meas h_bound hbound_int h_lim

end

end Work.FTS.BSSwirl
