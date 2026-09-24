import Mathlib
import Submission.Work.Analysis.Complex.DbarCauchy.Defs
import Submission.Work.Analysis.Complex.DbarCauchy.weyl_plane
import Submission.Work.Analysis.Complex.DbarCauchy.integral_mul_dbar_eq_neg_dbar_mul
import Submission.Work.Analysis.Complex.DbarCauchy.weak_zero

/-!
# Weyl's lemma, weak form: a weak `∂̄`-solution is holomorphic

A locally integrable function `u` on an open set `U ⊆ ℂ` whose `∂̄`-pairings against all compactly
supported `C¹` test functions supported in `U` vanish is (a.e. equal to) a function analytic on `U`.

This file contains the two *algebraic* bricks of the proof:

* `eq_zero_of_forall_integral_mul_eq_zero` — **(S3)**: a continuous function on an open set whose
  pairings against all test functions vanish is zero.  (`weak_zero.lean` supplies the witness.)
* `dbar_eq_zero_of_weak` — **(S-C)**: a `C¹` function whose weak `∂̄` vanishes has `∂̄ = 0`
  *pointwise*.  (Integration by parts `integral_mul_dbar_eq_neg_dbar_mul` + a compactly supported
  bump ≡ 1 near the point, + (S3).)

The remaining steps (mollification, the `L²` bound, Montel) are recorded in
`analysisOnNhd_of_weak_dbar_zero`'s docstring / the chapter notes.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace Work.Analysis.Complex.DbarCauchy

/-- **(S3) Vanishing pairings force vanishing.**  A continuous function on an open `U ⊆ ℂ` whose
pairings `∫_U g ψ` against every compactly supported `C¹` test function supported in `U` vanish is
zero on `U`. -/
theorem eq_zero_of_forall_integral_mul_eq_zero {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (hg : ContinuousOn g U)
    (h : ∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ z in U, g z * ψ z = 0) :
    ∀ z ∈ U, g z = 0 := by
  intro z₀ hz₀
  by_contra hne
  obtain ⟨Φ, hΦcd, hΦc, hΦsupp, hΦint⟩ := exists_testFunction_integral_ne_zero hU hg hz₀ hne
  exact hΦint (h Φ hΦcd hΦc hΦsupp)

/-- **(S-C) The `∂̄` of a weak `∂̄`-solution vanishes pointwise.**  If a globally `C¹` function `f`
has vanishing `∂̄`-pairings against all test functions supported in the open set `U`, then
`∂̄f = 0` at every point of `U`. -/
theorem dbar_eq_zero_of_weak {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (h : ∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ z in U, f z * dbar ψ z = 0) :
    ∀ z ∈ U, dbar f z = 0 := by
  intro z₀ hz₀
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
  have hrU' : ∀ z ∈ Metric.closedBall z₀ (r / 4), z ∈ U := fun z hz =>
    hrU (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)))
  -- a smooth bump supported in `U`, equal to `1` on a smaller ball
  let χ : ContDiffBump z₀ := ⟨r / 4, r / 2, by linarith, by linarith⟩
  have hχout : χ.rOut = r / 2 := rfl
  have hχin : χ.rIn = r / 4 := rfl
  have hχcd : ContDiff ℝ 1 χ := χ.contDiff
  have hχone : ∀ z ∈ Metric.closedBall z₀ (r / 4), χ z = 1 := fun z hz =>
    χ.one_of_mem_closedBall (by rwa [hχin])
  -- the `ℂ`-valued bump: compact support, and `∂̄ = 0` near `z₀`
  have hsupp_eq : Function.support (fun z : ℂ => (χ z : ℂ)) = Function.support χ := by
    ext z
    simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
  have htsC : tsupport (fun z : ℂ => (χ z : ℂ)) = Metric.closedBall z₀ (r / 2) := by
    have h1 : tsupport (fun z : ℂ => (χ z : ℂ)) = tsupport χ := by
      simp only [tsupport, hsupp_eq]
    rw [h1, ContDiffBump.tsupport_eq, hχout]
  have hχcsC : HasCompactSupport (fun z : ℂ => (χ z : ℂ)) := by
    rw [HasCompactSupport, htsC]
    exact isCompact_closedBall z₀ (r / 2)
  have hχℂ : ContDiff ℝ 1 (fun z : ℂ => (χ z : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp hχcd
  have hχdbar : ∀ z ∈ Metric.ball z₀ (r / 4), dbar (fun w : ℂ => (χ w : ℂ)) z = 0 := by
    intro z hz
    have hev : (fun w : ℂ => (χ w : ℂ)) =ᶠ[𝓝 z] (fun _ => 1) := by
      filter_upwards [χ.eventuallyEq_one_of_mem_ball (by rwa [hχin])] with w hw
      show (χ w : ℂ) = 1
      rw [hw]
      norm_num
    rw [dbar_congr hev]
    exact dbar_const 1 z
  -- the key computation: `∫ ∂̄f · ψ = 0` for every test function supported in the inner ball
  have hkey : ∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball z₀ (r / 4) → ∫ z, dbar f z * ψ z = 0 := by
    intro ψ hψcd hψcs hψsupp
    have hψU : tsupport ψ ⊆ U :=
      hψsupp.trans (fun z hz => hrU' z (Metric.ball_subset_closedBall hz))
    let Fχ : ℂ → ℂ := fun z => f z * (χ z : ℂ)
    have hAcd : ContDiff ℝ 1 Fχ := hf.mul hχℂ
    have hAcs : HasCompactSupport Fχ := hχcsC.mul_left
    have hibp := integral_mul_dbar_eq_neg_dbar_mul hAcd hAcs hψcd hψcs
    -- left-hand side: the bump is `1` on the support of `ψ`
    have hL : ∫ z, Fχ z * dbar ψ z = ∫ z, f z * dbar ψ z := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      change f z * (χ z : ℂ) * dbar ψ z = f z * dbar ψ z
      by_cases hz : z ∈ tsupport ψ
      · rw [hχone z (Metric.ball_subset_closedBall (hψsupp hz))]
        norm_num
      · have h0 : dbar ψ z = 0 := by
          rw [dbar_congr (notMem_tsupport_iff_eventuallyEq.mp hz)]
          exact dbar_zero z
        rw [h0, mul_zero, mul_zero]
    -- the hypothesis, transported from `U` to all of `ℂ`
    have hLz : ∫ z, f z * dbar ψ z = 0 := by
      have hoff : ∀ z : ℂ, z ∉ U → f z * dbar ψ z = 0 := by
        intro z hz
        have h0 : dbar ψ z = 0 := by
          rw [dbar_congr (notMem_tsupport_iff_eventuallyEq.mp (fun hmem => hz (hψU hmem)))]
          exact dbar_zero z
        rw [h0, mul_zero]
      rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)
        (f := fun z => f z * dbar ψ z) hoff]
      exact h ψ hψcd hψcs hψU
    -- right-hand side: only the first summand survives
    have hR : ∫ z, dbar Fχ z * ψ z = ∫ z, dbar f z * ψ z := by
      have hsplit : (fun z : ℂ => dbar Fχ z * ψ z)
          = fun z : ℂ => (χ z : ℂ) * dbar f z * ψ z := by
        funext z
        change dbar (fun w : ℂ => f w * (χ w : ℂ)) z * ψ z
          = (χ z : ℂ) * dbar f z * ψ z
        rw [dbar_mul f (fun w : ℂ => (χ w : ℂ)) z
          ((hf.differentiable (by norm_num)).differentiableAt)
          ((hχℂ.differentiable (by norm_num)).differentiableAt)]
        by_cases hz : z ∈ tsupport ψ
        · rw [hχdbar z (hψsupp hz), hχone z (Metric.ball_subset_closedBall (hψsupp hz))]
          ring
        · have h0 : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
          rw [h0]
          ring
      rw [hsplit]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      change (χ z : ℂ) * dbar f z * ψ z = dbar f z * ψ z
      by_cases hz : z ∈ tsupport ψ
      · rw [hχone z (Metric.ball_subset_closedBall (hψsupp hz))]
        norm_num
      · have h0 : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
        rw [h0, mul_zero, mul_zero]
    have h4 : (∫ z, f z * dbar ψ z) = -(∫ z, dbar f z * ψ z) := by
      rw [← hL, ← hR]
      exact hibp
    rw [hLz, zero_eq_neg] at h4
    exact h4
  -- (S3) on the small ball
  have hS3 : ∀ z ∈ Metric.ball z₀ (r / 4), dbar f z = 0 := by
    refine eq_zero_of_forall_integral_mul_eq_zero Metric.isOpen_ball
      (continuous_dbar f hf).continuousOn fun ψ hψcd hψcs hψsupp => ?_
    have hoff : ∀ z : ℂ, z ∉ Metric.ball z₀ (r / 4) → dbar f z * ψ z = 0 := by
      intro z hz
      have h0 : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun hmem => hz (hψsupp hmem))
      rw [h0, mul_zero]
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hoff]
    exact hkey ψ hψcd hψcs hψsupp
  exact hS3 z₀ (Metric.mem_ball_self (by linarith))

end Work.Analysis.Complex.DbarCauchy
