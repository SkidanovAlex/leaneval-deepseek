/-
# Cubic decay of the derivative of the regularised Beurling kernel

`W w = (1 - bumpC w) * w⁻²` is the smooth kernel of the Beurling transform
(see `Submission/Work/Beltrami/Wkernel.lean`).  Here we prove the estimate
needed to differentiate under the integral sign in the Cauchy/Beurling theory:

  `∃ M > 0, ∀ v : ℂ, ‖fderiv ℝ W v‖ ≤ M * (1 + ‖v‖)⁻³`.

The mathematics is three observations.

* `‖v‖ ≤ 1`:  the derivative is bounded on the (compact) closed unit ball by
  continuity of `v ↦ fderiv ℝ W v`, which follows from smoothness of `W`.
* `‖v‖ > 1`:  `W` agrees with `w ↦ w⁻²` on a neighbourhood of `v`, and the real
  differential of `w ↦ w⁻²` at `v` is multiplication by `-2 v⁻³`, of norm
  `2 ‖v‖⁻³` — cubic decay.
* The two regions are glued by the elementary estimates
  `(1 + r)⁻¹ ≥ 1/2` for `r ≤ 1` and `(1 + r)⁻¹ ≥ r⁻¹/2` for `r ≥ 1`.
-/
import Mathlib
import Submission.Work.Beltrami.Wkernel

noncomputable section

namespace Work.Beltrami

open Filter Metric
open scoped Topology
open scoped ContDiff

/-- For `0 ≤ r ≤ 1` one has `(1 + r)⁻³ ≥ 1/8`. -/
lemma Wfdb_aux_le_one {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1) : (1/8 : ℝ) ≤ ((1+r)⁻¹)^3 := by
  have h1 : (0:ℝ) < 1 + r := by linarith
  have h2 : (2:ℝ)⁻¹ ≤ (1+r)⁻¹ := by
    rw [inv_le_inv₀ (by norm_num) h1]
    linarith
  have h3 : ((2:ℝ)⁻¹)^3 ≤ ((1+r)⁻¹)^3 := by gcongr
  norm_num at h3
  simpa [inv_pow] using h3

/-- For `r ≥ 1` one has `(1 + r)⁻³ ≥ (1/8) r⁻³`. -/
lemma Wfdb_aux_ge_one {r : ℝ} (hr : 1 ≤ r) : (1/8) * (r⁻¹)^3 ≤ ((1+r)⁻¹)^3 := by
  have hr0 : (0:ℝ) < r := by linarith
  have h1 : (0:ℝ) < 1 + r := by linarith
  have h2 : (2*r)⁻¹ ≤ (1+r)⁻¹ := by
    rw [inv_le_inv₀ (by positivity) h1]
    linarith
  have h4 : (2*r)⁻¹ = (1/2) * r⁻¹ := by rw [mul_inv]; norm_num
  rw [h4] at h2
  have h3 : ((1/2) * r⁻¹)^3 ≤ ((1+r)⁻¹)^3 := by gcongr
  have h5 : ((1/2:ℝ) * r⁻¹)^3 = (1/8) * (r⁻¹)^3 := by ring
  rwa [h5] at h3

/-- The real differential of `w ↦ (w ^ 2)⁻¹` at `v ≠ 0` is complex multiplication
by `-2 v⁻³`, hence has operator norm `2 ‖v‖⁻³`. -/
lemma Wfdb_norm_fderiv_inv_sq (v : ℂ) (hv : v ≠ 0) :
    ‖fderiv ℝ (fun w : ℂ => (w ^ 2)⁻¹) v‖ ≤ 2 * (‖v‖⁻¹)^3 := by
  have hg : HasDerivAt (fun w : ℂ => w ^ 2) (2 * v) v := by
    simpa using hasDerivAt_pow 2 v
  have hh : HasDerivAt (fun w : ℂ => (w ^ 2)⁻¹) (-(2 * v) / (v ^ 2) ^ 2) v :=
    hg.inv (by simpa using pow_ne_zero 2 hv)
  have hF : HasFDerivAt (𝕜 := ℝ) (fun w : ℂ => (w ^ 2)⁻¹)
      (ContinuousLinearMap.restrictScalars ℝ
        (ContinuousLinearMap.toSpanSingleton ℂ (-(2 * v) / (v ^ 2) ^ 2) : ℂ →L[ℂ] ℂ)) v :=
    HasFDerivAt.restrictScalars ℝ hh.hasFDerivAt
  rw [hF.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun u => ?_)
  rw [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    norm_smul]
  have hfv : ‖-(2 * v) / (v ^ 2) ^ 2‖ = 2 * (‖v‖⁻¹)^3 := by
    have hv' : ‖v‖ ≠ 0 := by simpa [norm_eq_zero] using hv
    rw [norm_div, norm_neg, norm_mul, Complex.norm_ofNat, norm_pow, norm_pow]
    field_simp
  rw [hfv]
  exact le_of_eq (mul_comm _ _)

theorem W_fderiv_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ v : ℂ, ‖fderiv ℝ W v‖ ≤ M * ((1 + ‖v‖)⁻¹) ^ 3 := by
  -- On the closed unit ball the derivative is bounded, by smoothness of `W`.
  have hcont : Continuous (fun v : ℂ => fderiv ℝ W v) :=
    W_contDiff.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hcont.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (by simp [Metric.mem_closedBall]))
  refine ⟨8 * C + 16, by linarith, fun v => ?_⟩
  have hr0 : (0:ℝ) ≤ ‖v‖ := norm_nonneg v
  have h3 : (0:ℝ) ≤ 8 * C + 16 := by linarith
  by_cases hr : ‖v‖ ≤ 1
  · -- Inside the unit ball: use the compactness bound and `(1 + ‖v‖)⁻³ ≥ 1/8`.
    have h1 : ‖fderiv ℝ W v‖ ≤ C :=
      hC v (by simpa [Metric.mem_closedBall, dist_eq_norm] using hr)
    have h2 : (1/8 : ℝ) ≤ ((1 + ‖v‖)⁻¹)^3 := Wfdb_aux_le_one hr0 hr
    have h4 : (8*C+16) * (1/8) ≤ (8*C+16) * ((1 + ‖v‖)⁻¹)^3 :=
      mul_le_mul_of_nonneg_left h2 h3
    nlinarith [h1, h4]
  · -- Outside: `W` agrees locally with `w ↦ w⁻²`, whose differential decays cubically.
    rw [not_le] at hr
    have hv : v ≠ 0 := by
      intro h
      rw [h] at hr
      exact absurd hr (by norm_num)
    have heq : fderiv ℝ W v = fderiv ℝ (fun z : ℂ => (z^2)⁻¹) v :=
      (W_eventuallyEq_inv_sq hr).fderiv_eq
    have h1 : ‖fderiv ℝ (fun z : ℂ => (z^2)⁻¹) v‖ ≤ 2 * (‖v‖⁻¹)^3 :=
      Wfdb_norm_fderiv_inv_sq v hv
    have h2 : (1/8) * (‖v‖⁻¹)^3 ≤ ((1 + ‖v‖)⁻¹)^3 := Wfdb_aux_ge_one hr.le
    have h4 : (8*C+16) * ((1/8) * (‖v‖⁻¹)^3) ≤ (8*C+16) * ((1 + ‖v‖)⁻¹)^3 :=
      mul_le_mul_of_nonneg_left h2 h3
    have hr3 : (0:ℝ) ≤ (‖v‖⁻¹)^3 := by positivity
    rw [heq]
    nlinarith [h1, h4, hC0, hr3]

end Work.Beltrami
