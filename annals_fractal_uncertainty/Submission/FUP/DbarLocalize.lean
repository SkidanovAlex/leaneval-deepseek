import Submission.FUP.DbarDbarPos
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

open MeasureTheory
open scoped BigOperators ContDiff
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {d : ℕ}

/-!
# Localisation of Hoe rmander's distributional positivity condition

For a `C²` weight the distributional condition `DbarDbarPos φ κ` (i.e. `∂∂̄φ ≥ κ` against all
smooth compactly supported `(1,0)`-forms) implies its pointwise form
`4 κ(z) ∑_j |w_j|² ≤ (D²φ(z))[w,w] + (D²φ(z))[I w, I w]`.
The proof tests the distributional inequality with the forms `α = ψ · w`, `ψ` a bump
concentrating at `z`, and uses `integral_mul_dbarDbarTest` and `realHessian_eq_dbarDbarHess`.

This makes the pointwise hypothesis of
`Submission.FUP.KohnMorrey.kohn_morrey_estimate_of_hessian` (and hence
`Submission.FUP.Hormander.HormanderStatementPointwise`) *equivalent* to the distributional one for
`C²` weights.
-/

namespace Submission.FUP

lemma formNormSq_of_smul (ψ : (Fin d → ℂ) → ℝ) (hψ : ∀ z, 0 ≤ ψ z) (w : Fin d → ℂ)
    (z : (Fin d → ℂ)) :
    formNormSq (fun z j => (ψ z : ℂ) * w j) z = ψ z ^ 2 * ∑ j, ‖w j‖ ^ 2 := by
  simp only [formNormSq]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : ‖((ψ z : ℂ) * w j)‖ = ψ z * ‖w j‖ := by
    rw [norm_mul]
    simp [abs_of_nonneg (hψ z)]
  rw [h]
  ring

lemma formTest_of_smul (ψ : (Fin d → ℂ) → ℝ) (hψ : ∀ z, 0 ≤ ψ z) (w : Fin d → ℂ)
    (j k : Fin d) (z : (Fin d → ℂ)) :
    formTest (fun z j => (ψ z : ℂ) * w j) j k z
      = ψ z ^ 2 * formTest (fun _ j => w j) j k z := by
  have hstar : star ((ψ z : ℂ)) = (ψ z : ℂ) := by simp
  have h1 : ((ψ z : ℂ) * w j) * star ((ψ z : ℂ) * w k)
      = ((ψ z ^ 2 : ℝ) : ℂ) * (w j * star (w k)) := by
    rw [star_mul, hstar]
    push_cast
    ring
  simp only [formTest]
  rw [h1, Complex.re_ofReal_mul]

lemma formImag_of_smul (ψ : (Fin d → ℂ) → ℝ) (hψ : ∀ z, 0 ≤ ψ z) (w : Fin d → ℂ)
    (j k : Fin d) (z : (Fin d → ℂ)) :
    formImag (fun z j => (ψ z : ℂ) * w j) j k z
      = ψ z ^ 2 * formImag (fun _ j => w j) j k z := by
  have hstar : star ((ψ z : ℂ)) = (ψ z : ℂ) := by simp
  have h1 : ((ψ z : ℂ) * w j) * star ((ψ z : ℂ) * w k)
      = ((ψ z ^ 2 : ℝ) : ℂ) * (w j * star (w k)) := by
    rw [star_mul, hstar]
    push_cast
    ring
  simp only [formImag]
  rw [h1, Complex.im_ofReal_mul]

lemma dbarDbarHess_of_smul (φ : (Fin d → ℂ) → ℝ) (ψ : (Fin d → ℂ) → ℝ)
    (hψ : ∀ z, 0 ≤ ψ z) (w : Fin d → ℂ) (z : (Fin d → ℂ)) :
    dbarDbarHess φ (fun z j => (ψ z : ℂ) * w j) z
      = ψ z ^ 2 * dbarDbarHess φ (fun _ j => w j) z := by
  simp only [dbarDbarHess, dbarDbarTermH, formTest_of_smul ψ hψ w, formImag_of_smul ψ hψ w]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Localisation of the distributional condition.**
For a `C²` weight the distributional inequality `∂∂̄φ ≥ κ` implies its pointwise form. -/
theorem pointwise_bound_of_dbarDbarPos {φ κ : (Fin d → ℂ) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκc : Continuous κ) (h : DbarDbarPos φ κ) :
    ∀ z (w : Fin d → ℂ), 4 * (κ z * ∑ j, ‖w j‖ ^ 2)
      ≤ (iteratedFDeriv ℝ 2 φ z) ![w, w]
        + (iteratedFDeriv ℝ 2 φ z) ![Complex.I • w, Complex.I • w] := by
  intro z₀ w
  by_contra hcon
  rw [not_le] at hcon
  set H : (Fin d → ℂ) → ℝ := fun y => dbarDbarHess φ (fun _ j => w j) y with hHdef
  set G : (Fin d → ℂ) → ℝ := fun y => 4 * (κ y * ∑ j, ‖w j‖ ^ 2) - H y with hGdef
  have hHz₀ : H z₀ = (iteratedFDeriv ℝ 2 φ z₀) ![w, w]
      + (iteratedFDeriv ℝ 2 φ z₀) ![Complex.I • w, Complex.I • w] := by
    rw [hHdef]
    exact (realHessian_eq_dbarDbarHess φ (fun _ j => w j) z₀).symm
  have hGz₀ : 0 < G z₀ := by
    have h1 := hcon
    rw [← hHz₀] at h1
    rw [hGdef]
    linarith
  have hHcont : Continuous H := by
    rw [hHdef]
    have hfun : dbarDbarHess φ (fun _ j => w j)
        = fun y => ∑ j, ∑ k, ((w j * star (w k)).re * (dxx j k φ y + dyy j k φ y)
            - (w j * star (w k)).im * (dxy j k φ y - dyx j k φ y)) := by
      funext y
      simp only [dbarDbarHess, dbarDbarTermH, formTest, formImag]
    rw [hfun]
    refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_
    exact (continuous_const.mul ((continuous_dxx_of_contDiff_two hφ j k).add
      (continuous_dyy_of_contDiff_two hφ j k))).sub
      (continuous_const.mul ((continuous_dxy_of_contDiff_two hφ j k).sub
        (continuous_dyx_of_contDiff_two hφ j k)))
  have hGcont : Continuous G := by
    rw [hGdef]
    exact (continuous_const.mul (hκc.mul continuous_const)).sub hHcont
  have hcont : ContinuousAt G z₀ := hGcont.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont (G z₀ / 2) (by linarith)
  have hδg : ∀ y, dist y z₀ < δ → G z₀ / 2 < G y := by
    intro y hy
    have h1 := hδ hy
    rw [Real.dist_eq] at h1
    have h2 := (abs_lt.mp h1).1
    linarith
  set bump : ContDiffBump z₀ := ⟨δ / 4, δ / 2, by linarith, by linarith⟩ with hbumpdef
  set α : (Fin d → ℂ) → (Fin d → ℂ) := fun y j => (bump y : ℂ) * w j with hαdef
  have hbumpnn : ∀ y, 0 ≤ bump y := fun y => bump.nonneg
  have hbump1 : ∀ y ∈ Metric.closedBall z₀ (δ / 4), bump y = 1 :=
    fun y hy => bump.one_of_mem_closedBall hy
  have hbumpsupp : ∀ y, bump y ≠ 0 → y ∈ Metric.ball z₀ (δ / 2) := by
    intro y hy
    have h1 : y ∈ Function.support bump := Function.mem_support.mpr hy
    rwa [bump.support_eq] at h1
  have hαsm : ContDiff ℝ ∞ α := by
    rw [hαdef]
    refine contDiff_pi.mpr fun j => ?_
    exact ((Complex.ofRealCLM.contDiff (n := ∞)).comp (bump.contDiff (n := ⊤))).mul
      contDiff_const
  have hbump2cs : HasCompactSupport (fun y => bump y ^ 2) := by
    apply HasCompactSupport.mono' bump.hasCompactSupport
    intro y hy
    by_contra hyb
    have hzero : bump y = 0 := image_eq_zero_of_notMem_tsupport hyb
    exact hy (by simp [hzero])
  have hαcs : HasCompactSupport α := by
    rw [hαdef]
    apply HasCompactSupport.mono' bump.hasCompactSupport
    intro y hy
    by_contra hyb
    have hzero : bump y = 0 := image_eq_zero_of_notMem_tsupport hyb
    exact hy (by funext j; simp [hzero])
  obtain ⟨hint1, hint2, hineq⟩ := h α hαsm hαcs
  have hIBP := integral_mul_dbarDbarTest hφ hαsm hαcs
  have hpt1 : ∀ y, κ y * formNormSq α y = bump y ^ 2 * (κ y * ∑ j, ‖w j‖ ^ 2) := by
    intro y
    rw [hαdef]
    rw [formNormSq_of_smul (fun y => bump y) hbumpnn w y]
    ring
  have hpt2 : ∀ y, dbarDbarHess φ α y = bump y ^ 2 * H y := by
    intro y
    rw [hαdef, hHdef]
    exact dbarDbarHess_of_smul φ (fun y => bump y) hbumpnn w y
  have hL : (∫ y, κ y * formNormSq α y)
      = ∫ y, bump y ^ 2 * (κ y * ∑ j, ‖w j‖ ^ 2) :=
    integral_congr_ae (Filter.Eventually.of_forall hpt1)
  have hR : (∫ y, φ y * dbarDbarTest α y) = (1 / 4) * ∫ y, bump y ^ 2 * H y := by
    rw [hIBP]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall hpt2)
  rw [hL, hR] at hineq
  have hineq' : (∫ y, bump y ^ 2 * (4 * (κ y * ∑ j, ‖w j‖ ^ 2)))
      ≤ ∫ y, bump y ^ 2 * H y := by
    have h2 : (∫ y, bump y ^ 2 * (κ y * ∑ j, ‖w j‖ ^ 2)) * 4
        = ∫ y, bump y ^ 2 * (4 * (κ y * ∑ j, ‖w j‖ ^ 2)) := by
      rw [← integral_mul_const]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    have h3 : ((1 / 4) * ∫ y, bump y ^ 2 * H y) * 4 = ∫ y, bump y ^ 2 * H y := by ring
    calc (∫ y, bump y ^ 2 * (4 * (κ y * ∑ j, ‖w j‖ ^ 2)))
        = (∫ y, bump y ^ 2 * (κ y * ∑ j, ‖w j‖ ^ 2)) * 4 := h2.symm
      _ ≤ ((1 / 4) * ∫ y, bump y ^ 2 * H y) * 4 := by
          exact mul_le_mul_of_nonneg_right hineq (by norm_num)
      _ = ∫ y, bump y ^ 2 * H y := h3
  have hG2 : (fun y => bump y ^ 2 * (4 * (κ y * ∑ j, ‖w j‖ ^ 2)) - bump y ^ 2 * H y)
      = fun y => bump y ^ 2 * G y := by
    funext y
    rw [hGdef]
    ring
  have hint3 : Integrable (fun y => bump y ^ 2 * (4 * (κ y * ∑ j, ‖w j‖ ^ 2))) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact ((bump.contDiff (n := ⊤).continuous.pow 2).mul (continuous_const.mul (hκc.mul
        continuous_const)))
    · exact hbump2cs.mul_right
        (f' := fun y => 4 * (κ y * ∑ j, ‖w j‖ ^ 2))
  have hint4 : Integrable (fun y => bump y ^ 2 * H y) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (bump.contDiff (n := ⊤).continuous.pow 2).mul hHcont
    · exact hbump2cs.mul_right (f' := H)
  have hle0 : (∫ y, bump y ^ 2 * G y) ≤ 0 := by
    have hsplit : (∫ y, bump y ^ 2 * G y)
        = (∫ y, bump y ^ 2 * (4 * (κ y * ∑ j, ‖w j‖ ^ 2))) - ∫ y, bump y ^ 2 * H y := by
      rw [← integral_sub hint3 hint4]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
        rw [hGdef]; ring)
    rw [hsplit]
    linarith
  have hmono : (∫ y, bump y ^ 2 * (G z₀ / 2)) ≤ ∫ y, bump y ^ 2 * G y := by
    apply integral_mono _ _ (fun y => ?_)
    · apply Continuous.integrable_of_hasCompactSupport
      · exact (bump.contDiff (n := ⊤).continuous.pow 2).mul continuous_const
      · exact hbump2cs.mul_right (f' := fun _ => G z₀ / 2)
    · apply Continuous.integrable_of_hasCompactSupport
      · exact (bump.contDiff (n := ⊤).continuous.pow 2).mul hGcont
      · exact hbump2cs.mul_right (f' := G)
    · by_cases hb : bump y = 0
      · rw [hb]; ring_nf; positivity
      · have hy : G z₀ / 2 < G y := by
          apply hδg
          have h1 := hbumpsupp y hb
          rw [Metric.mem_ball] at h1
          linarith
        exact mul_le_mul_of_nonneg_left hy.le (sq_nonneg _)
  have hposint : 0 < ∫ y, bump y ^ 2 := by
    rw [integral_pos_iff_support_of_nonneg (fun y => sq_nonneg _)
      (bump.contDiff (n := ⊤).continuous.pow 2 |>.integrable_of_hasCompactSupport hbump2cs)]
    rw [show Function.support (fun y => bump y ^ 2) = Metric.ball z₀ (δ / 2) from by
      have h1 : Function.support (fun y => bump y ^ 2) = Function.support bump := by
        ext y
        simp only [Function.mem_support]
        exact pow_ne_zero_iff (by norm_num : (2 : ℕ) ≠ 0)
      rw [h1, bump.support_eq]]
    exact Metric.measure_ball_pos (μ := volume) z₀ (by linarith)
  have hfinal : 0 < ∫ y, bump y ^ 2 * G y := by
    have := mul_lt_mul_of_pos_right hposint (by linarith : (0:ℝ) < G z₀ / 2)
    have heq : (∫ y, bump y ^ 2) * (G z₀ / 2) = ∫ y, bump y ^ 2 * (G z₀ / 2) := by
      rw [integral_mul_const]
    linarith [hmono, heq ▸ this]
  linarith

end Submission.FUP
