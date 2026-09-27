import Mathlib
import Submission.Work.Mostow.Hyper

/-!
# `hdistIsCompact`

The metric balls of the hyperbolic distance `hdist` on the chart `E n = ℝⁿ` are compact:
for every centre `u` and radius `r`, `{v | hdist u v ≤ r}` is closed (continuity of `hdist`)
and bounded, hence compact, since `E n` is finite dimensional.

The bound is the elementary one coming from the chart: writing `s = tpart u`, `a = ‖u‖`,
`b = ‖v‖`, `C = cosh (max r 0)`, we have `cosh (hdist u v) = cc u v` while
`cc u v ≥ s·tpart v − ‖u‖·‖v‖ ≥ (s − a)·b`, and `s − a = 1/(s + a) ≥ 1/(1 + 2a) > 0`
(since `a ≤ s ≤ 1 + a`). Hence `b ≤ C·(1 + 2a)`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open Submission.Mostow.Hyper

/-- The `cosh`-kernel is at least `1`, so that `hdist u v = arcosh (cc u v)` with
the argument in the domain of `arcosh`. -/
private lemma cc_one_le {n : ℕ} (u v : E n) : 1 ≤ cc u v := by
  have h1 : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
  have hnn : 0 ≤ 1 + ‖u‖ * ‖v‖ := by positivity
  have ht : 0 ≤ tpart u * tpart v := le_of_lt (mul_pos (tpart_pos u) (tpart_pos v))
  have hb : (1 + ‖u‖ * ‖v‖)^2 ≤ (tpart u * tpart v)^2 := by
    rw [mul_pow, sq_tpart, sq_tpart]
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  have h2 : 1 + ‖u‖ * ‖v‖ ≤ tpart u * tpart v := by
    have := Real.sqrt_le_sqrt hb
    rwa [Real.sqrt_sq hnn, Real.sqrt_sq ht] at this
  simp only [cc]
  linarith

/-- `‖u‖ ≤ tpart u`. -/
private lemma norm_le_tpart {n : ℕ} (u : E n) : ‖u‖ ≤ tpart u := by
  rw [tpart]
  calc ‖u‖ = Real.sqrt (‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg u)).symm
    _ ≤ Real.sqrt (1 + ‖u‖ ^ 2) := Real.sqrt_le_sqrt (by linarith)

/-- `tpart u ≤ 1 + ‖u‖`. -/
private lemma tpart_le_one_add_norm {n : ℕ} (u : E n) : tpart u ≤ 1 + ‖u‖ := by
  rw [tpart]
  calc Real.sqrt (1 + ‖u‖ ^ 2) ≤ Real.sqrt ((1 + ‖u‖) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [norm_nonneg u])
    _ = 1 + ‖u‖ := Real.sqrt_sq (by positivity)

/-- `v ↦ hdist u v` is continuous. -/
private lemma continuous_hdist_left {n : ℕ} (u : E n) :
    Continuous (fun v : E n => hdist u v) := by
  have hcont : Continuous (fun v : E n => cc u v) := by
    simp only [cc, tpart]
    fun_prop
  have h := ContinuousOn.comp_continuous (g := Real.arcosh) (f := fun v : E n => cc u v)
    (s := Set.Ici 1) Real.continuousOn_arcosh hcont (fun v => cc_one_le u v)
  simpa [Function.comp_def, hdist_eq_cc] using h

theorem hdistIsCompact (n : ℕ) (u : E n) (r : ℝ) : IsCompact {v : E n | hdist u v ≤ r} := by
  have hcont : Continuous (fun v : E n => hdist u v) := continuous_hdist_left u
  have hclosed : IsClosed {v : E n | hdist u v ≤ r} := isClosed_le hcont continuous_const
  refine IsCompact.of_isClosed_subset
    (isCompact_closedBall u (Real.cosh (max r 0) * (1 + 2 * ‖u‖) + ‖u‖)) hclosed ?_
  intro v hv
  simp only [Set.mem_ofPred_eq] at hv
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hcc1 : 1 ≤ cc u v := cc_one_le u v
  have harcc_nonneg : 0 ≤ Real.arcosh (cc u v) := Real.arcosh_nonneg hcc1
  have hle : Real.arcosh (cc u v) ≤ max r 0 := le_trans hv (le_max_left r 0)
  have hmaxnn : 0 ≤ max r 0 := le_max_right r 0
  -- the cosh-kernel stays below `cosh (max r 0)`
  have hcc_le : cc u v ≤ Real.cosh (max r 0) := by
    have h := Real.cosh_le_cosh.mpr (show |Real.arcosh (cc u v)| ≤ |max r 0| by
      rw [abs_of_nonneg harcc_nonneg, abs_of_nonneg hmaxnn]
      exact hle)
    rwa [Real.cosh_arcosh hcc1] at h
  have hinner : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
  have htv : ‖v‖ ≤ tpart v := norm_le_tpart v
  have hsa_nonneg : 0 ≤ tpart u - ‖u‖ := by linarith [norm_le_tpart u]
  -- `cc u v ≥ (tpart u - ‖u‖) * ‖v‖`
  have hkey : (tpart u - ‖u‖) * ‖v‖ ≤ cc u v := by
    have h1 : 0 ≤ tpart u * (tpart v - ‖v‖) :=
      mul_nonneg (le_of_lt (tpart_pos u)) (by linarith)
    have h2 : 0 ≤ ‖u‖ * ‖v‖ - inner ℝ u v := sub_nonneg.mpr hinner
    simp only [cc]
    nlinarith [h1, h2]
  -- `(tpart u - ‖u‖) * (1 + 2‖u‖) ≥ 1`
  have hs_eq : (tpart u - ‖u‖) * (tpart u + ‖u‖) = 1 := by
    have h := sq_tpart u
    nlinarith [h]
  have h1a : 0 ≤ 1 + ‖u‖ - tpart u := by linarith [tpart_le_one_add_norm u]
  have hsa : 1 ≤ (tpart u - ‖u‖) * (1 + 2 * ‖u‖) := by
    have hprod : 0 ≤ (tpart u - ‖u‖) * (1 + ‖u‖ - tpart u) := mul_nonneg hsa_nonneg h1a
    nlinarith [hs_eq, hprod]
  have hnn1 : (0 : ℝ) ≤ 1 + 2 * ‖u‖ := by linarith [norm_nonneg u]
  have hb1 : ‖v‖ ≤ ‖v‖ * ((tpart u - ‖u‖) * (1 + 2 * ‖u‖)) :=
    le_mul_of_one_le_right (norm_nonneg v) hsa
  have hb2 : ‖v‖ * ((tpart u - ‖u‖) * (1 + 2 * ‖u‖)) ≤
      Real.cosh (max r 0) * (1 + 2 * ‖u‖) := by
    have h := mul_le_mul_of_nonneg_right hkey hnn1
    have h2 := mul_le_mul_of_nonneg_right hcc_le hnn1
    nlinarith [h, h2]
  have hbnd : ‖v‖ ≤ Real.cosh (max r 0) * (1 + 2 * ‖u‖) := le_trans hb1 hb2
  have := norm_sub_le v u
  linarith

end Work.Mostow
