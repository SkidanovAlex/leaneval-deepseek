/-
Copyright: Work.MRMT (mandelbar) subproject.

# The energy identity `∫ ‖∂φ‖² = ∫ ‖∂̄φ‖²` for compactly supported `C¹` functions

For `φ : ℂ → ℂ` of class `C¹` with compact support the `L²` norms of the two Wirtinger
derivatives agree.  Equivalently the integral of the Jacobian `|∂φ|² - |∂̄φ|²` vanishes,
which is the classical fact that the Jacobian of a compactly supported `C¹` map has zero
integral (the map extends to `S²` fixing `∞`, hence has degree `0`).

The proof has two steps.

* **Smooth case** (`energy_identity_of_contDiff_two`): for `ψ` of class `C²` with compact
  support, the fundamental identity `∫ ∂̄G = 0` (`integral_dzbar_eq_zero_of_contDiff`,
  integration by parts against the constant test function `1`) applied to the `C¹` functions
  `G = conj ψ · ∂ψ` and `H = conj ψ · ∂̄ψ` gives
  `∫ ‖∂ψ‖² = -∫ conj ψ · ∂̄∂ψ` and `∫ ‖∂̄ψ‖² = -∫ conj ψ · ∂∂̄ψ`, and the mixed Wirtinger
  derivatives commute (`dzbar_dz_commute`, from the symmetry of the second Fréchet derivative).

* **Reduction to the smooth case** (`energy_identity_of_contDiff_one`, proved separately):
  mollify `φ` and pass to the limit.
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.QC.WirtingerCalc
import Submission.Work.MRMT.Sobolev.dzbar_mul
import Submission.Work.MRMT.Sobolev.integral_dzbar_eq_zero_of_contDiff
import Submission.Work.MRMT.Sobolev.is_dbar_deriv_of_contDiff_of_ne_zero_hasCompactSupport
import Submission.Work.MRMT.Beltrami.energy_identity_of_contDiff_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section
open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

namespace Work.MRMT.Beltrami
open Work.MRMT

def dzCLM : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ) (2 : ℂ)⁻¹).comp
    (ContinuousLinearMap.apply ℝ ℂ (1:ℂ) -
      ((ContinuousLinearMap.mul ℝ ℂ) Complex.I).comp (ContinuousLinearMap.apply ℝ ℂ Complex.I))

def dzbarCLM : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ) (2 : ℂ)⁻¹).comp
    (ContinuousLinearMap.apply ℝ ℂ (1:ℂ) +
      ((ContinuousLinearMap.mul ℝ ℂ) Complex.I).comp (ContinuousLinearMap.apply ℝ ℂ Complex.I))

lemma dzCLM_apply (L : ℂ →L[ℝ] ℂ) : dzCLM L = (L 1 - Complex.I * L Complex.I) / 2 := by
  simp only [dzCLM, ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.apply_apply]
  simp only [map_sub]; simp; ring

lemma dzbarCLM_apply (L : ℂ →L[ℝ] ℂ) : dzbarCLM L = (L 1 + Complex.I * L Complex.I) / 2 := by
  simp only [dzbarCLM, ContinuousLinearMap.comp_apply, add_apply, ContinuousLinearMap.apply_apply]
  simp only [map_add]; simp; ring

lemma dz_eq_dzCLM (f : ℂ → ℂ) (z : ℂ) : dz f z = dzCLM (fderiv ℝ f z) := by rw [dzCLM_apply]; rfl
lemma dzbar_eq_dzbarCLM (f : ℂ → ℂ) (z : ℂ) : dzbar f z = dzbarCLM (fderiv ℝ f z) := by
  rw [dzbarCLM_apply]; rfl

lemma hasFDerivAt_dz {ψ : ℂ → ℂ} {Q : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ)} {z : ℂ}
    (h : HasFDerivAt (fderiv ℝ ψ) Q z) : HasFDerivAt (dz ψ) (dzCLM.comp Q) z := by
  have hfun : dz ψ = dzCLM ∘ (fderiv ℝ ψ) := by funext w; exact dz_eq_dzCLM ψ w
  rw [hfun]; exact dzCLM.hasFDerivAt.comp z h

lemma hasFDerivAt_dzbar {ψ : ℂ → ℂ} {Q : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ)} {z : ℂ}
    (h : HasFDerivAt (fderiv ℝ ψ) Q z) : HasFDerivAt (dzbar ψ) (dzbarCLM.comp Q) z := by
  have hfun : dzbar ψ = dzbarCLM ∘ (fderiv ℝ ψ) := by funext w; exact dzbar_eq_dzbarCLM ψ w
  rw [hfun]; exact dzbarCLM.hasFDerivAt.comp z h

lemma dzbarCLM_comp_dzCLM (Q : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ))
    (hQ : Q 1 Complex.I = Q Complex.I 1) :
    dzbarCLM (dzCLM.comp Q) = dzCLM (dzbarCLM.comp Q) := by
  have h1 : (dzCLM.comp Q) 1 = (Q 1 1 - Complex.I * Q 1 Complex.I) / 2 := by
    rw [ContinuousLinearMap.comp_apply, dzCLM_apply]
  have h2 : (dzCLM.comp Q) Complex.I = (Q Complex.I 1 - Complex.I * Q Complex.I Complex.I) / 2 := by
    rw [ContinuousLinearMap.comp_apply, dzCLM_apply]
  have h3 : (dzbarCLM.comp Q) 1 = (Q 1 1 + Complex.I * Q 1 Complex.I) / 2 := by
    rw [ContinuousLinearMap.comp_apply, dzbarCLM_apply]
  have h4 : (dzbarCLM.comp Q) Complex.I = (Q Complex.I 1 + Complex.I * Q Complex.I Complex.I) / 2 := by
    rw [ContinuousLinearMap.comp_apply, dzbarCLM_apply]
  rw [dzbarCLM_apply, dzCLM_apply, h1, h2, h3, h4, hQ]; ring


lemma continuous_dz_of_contDiff (f : ℂ → ℂ) {n : WithTop ℕ∞} (hn : n ≠ 0)
    (hc : ContDiff ℝ n f) : Continuous (dz f) := by
  have hd : Continuous (fderiv ℝ f) := hc.continuous_fderiv hn
  unfold dz
  exact ((hd.clm_apply continuous_const).sub
    (continuous_const.mul (hd.clm_apply continuous_const))).div_const 2

lemma contDiff_starRingEnd_comp {G : ℂ → ℂ} {n : WithTop ℕ∞} (hc : ContDiff ℝ n G) :
    ContDiff ℝ n (fun z => (starRingEnd ℂ) (G z)) := by
  have hstar : ContDiff ℝ n ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ → ℂ) :=
    ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).contDiff
  have hcomp : ContDiff ℝ n (((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ → ℂ) ∘ G) := hstar.comp hc
  rw [contDiff_iff_contDiffAt] at hcomp ⊢
  intro x
  refine (hcomp x).congr_of_eventuallyEq ?_
  filter_upwards with y
  simp only [Function.comp_apply, starL'_apply, star_def]

lemma hasCompactSupport_starRingEnd_comp {G : ℂ → ℂ} (hs : HasCompactSupport G) :
    HasCompactSupport (fun z => (starRingEnd ℂ) (G z)) :=
  hs.comp_left (g := (starRingEnd ℂ)) (by simp)

theorem dzbar_dz_commute {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 2 ψ) (z : ℂ) :
    dzbar (dz ψ) z = dz (dzbar ψ) z := by
  have hΦ : DifferentiableAt ℝ (fderiv ℝ ψ) z := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ.fderiv_right (by norm_num)
    exact h1.differentiable (by norm_num) z
  have hsym : ∀ v w : ℂ, fderiv ℝ (fderiv ℝ ψ) z v w = fderiv ℝ (fderiv ℝ ψ) z w v :=
    second_derivative_symmetric (f := ψ) (f' := fderiv ℝ ψ)
      (f'' := fderiv ℝ (fderiv ℝ ψ) z)
      (fun y => (hψ.differentiable (by norm_num) y).hasFDerivAt) hΦ.hasFDerivAt
  have hdzdz : fderiv ℝ (dz ψ) z = dzCLM.comp (fderiv ℝ (fderiv ℝ ψ) z) :=
    (hasFDerivAt_dz hΦ.hasFDerivAt).fderiv
  have hdzdzbar : fderiv ℝ (dzbar ψ) z = dzbarCLM.comp (fderiv ℝ (fderiv ℝ ψ) z) :=
    (hasFDerivAt_dzbar hΦ.hasFDerivAt).fderiv
  rw [dzbar_eq_dzbarCLM, dz_eq_dzCLM, hdzdz, hdzdzbar]
  exact dzbarCLM_comp_dzCLM (fderiv ℝ (fderiv ℝ ψ) z) (hsym 1 Complex.I)

theorem integral_dz_eq_zero_of_contDiff (G : ℂ → ℂ) {n : WithTop ℕ∞} (hn : n ≠ 0)
    (hc : ContDiff ℝ n G) (hs : HasCompactSupport G) : ∫ z, dz G z = 0 := by
  have hconj : ContDiff ℝ n (fun z => (starRingEnd ℂ) (G z)) := by
    have hstar : ContDiff ℝ n ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ → ℂ) :=
      ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).contDiff
    have hcomp : ContDiff ℝ n (((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ → ℂ) ∘ G) := hstar.comp hc
    rw [contDiff_iff_contDiffAt] at hcomp ⊢
    intro x
    refine (hcomp x).congr_of_eventuallyEq ?_
    filter_upwards with y
    simp only [Function.comp_apply, starL'_apply, star_def]
  have hcs : HasCompactSupport (fun z => (starRingEnd ℂ) (G z)) :=
    hs.comp_left (g := (starRingEnd ℂ)) (by simp)
  have hzero : ∫ z, dzbar (fun z => (starRingEnd ℂ) (G z)) z = 0 :=
    Work.MRMT.Sobolev.integral_dzbar_eq_zero_of_contDiff _ hn hconj hcs
  have hpt : ∀ z, dz G z = (starRingEnd ℂ) (dzbar (fun z => (starRingEnd ℂ) (G z)) z) := by
    intro z
    rw [Work.MRMT.QC.dzbar_conj (hc.differentiable hn z)]
    simp
  calc ∫ z, dz G z
      = ∫ z, (starRingEnd ℂ) (dzbar (fun z => (starRingEnd ℂ) (G z)) z) :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = (starRingEnd ℂ) (∫ z, dzbar (fun z => (starRingEnd ℂ) (G z)) z) := integral_conj
    _ = 0 := by rw [hzero]; simp



theorem energy_identity_of_contDiff_two (ψ : ℂ → ℂ) (hψ : ContDiff ℝ 2 ψ)
    (hs : HasCompactSupport ψ) :
    ∫ z, ‖dz ψ z‖ ^ 2 ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ)
      = ∫ z, ‖dzbar ψ z‖ ^ 2 ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hcw : ContDiff ℝ 2 (fun z => (starRingEnd ℂ) (ψ z)) := contDiff_starRingEnd_comp hψ
  have hcs_cw : HasCompactSupport (fun z => (starRingEnd ℂ) (ψ z)) :=
    hasCompactSupport_starRingEnd_comp hs
  have hcs_fderiv : HasCompactSupport (fderiv ℝ ψ) := hs.fderiv ℝ
  have hA : ContDiff ℝ 1 (dz ψ) := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ.fderiv_right (by norm_num)
    have h2 : ContDiff ℝ 1 (dzCLM ∘ (fderiv ℝ ψ)) := (dzCLM.contDiff (n := 1)).comp h1
    have hfun : dz ψ = dzCLM ∘ (fderiv ℝ ψ) := funext (fun w => dz_eq_dzCLM ψ w)
    rwa [← hfun] at h2
  have hB : ContDiff ℝ 1 (dzbar ψ) := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ.fderiv_right (by norm_num)
    have h2 : ContDiff ℝ 1 (dzbarCLM ∘ (fderiv ℝ ψ)) := (dzbarCLM.contDiff (n := 1)).comp h1
    have hfun : dzbar ψ = dzbarCLM ∘ (fderiv ℝ ψ) := funext (fun w => dzbar_eq_dzbarCLM ψ w)
    rwa [← hfun] at h2
  have hcs_A : HasCompactSupport (dz ψ) := by
    have h := hcs_fderiv.comp_left (g := dzCLM) (by rw [dzCLM_apply]; simp)
    have hfun : dz ψ = dzCLM ∘ (fderiv ℝ ψ) := funext (fun w => dz_eq_dzCLM ψ w)
    rwa [← hfun] at h
  have hcs_B : HasCompactSupport (dzbar ψ) := by
    have h := hcs_fderiv.comp_left (g := dzbarCLM) (by rw [dzbarCLM_apply]; simp)
    have hfun : dzbar ψ = dzbarCLM ∘ (fderiv ℝ ψ) := funext (fun w => dzbar_eq_dzbarCLM ψ w)
    rwa [← hfun] at h
  have hcont_cw : Continuous (fun z => (starRingEnd ℂ) (ψ z)) := hcw.continuous
  -- ===== G1 = conj psi * dz psi =====
  have hG1cd : ContDiff ℝ 1 (fun z => (starRingEnd ℂ) (ψ z) * dz ψ z) :=
    (hcw.of_le (by norm_num : (1:WithTop ℕ∞) ≤ 2)).mul hA
  have hG1cs : HasCompactSupport (fun z => (starRingEnd ℂ) (ψ z) * dz ψ z) :=
    hcs_A.mul_left (f := fun z => (starRingEnd ℂ) (ψ z))
  have hz1 : ∫ z, dzbar (fun z => (starRingEnd ℂ) (ψ z) * dz ψ z) z = 0 :=
    Work.MRMT.Sobolev.integral_dzbar_eq_zero_of_contDiff _ (n := 1) (by norm_num) hG1cd hG1cs
  have hpt1 : ∀ z, dzbar (fun z => (starRingEnd ℂ) (ψ z) * dz ψ z) z
      = (starRingEnd ℂ) (ψ z) * dzbar (dz ψ) z + dz ψ z * (starRingEnd ℂ) (dz ψ z) := by
    intro z
    have h1 : DifferentiableAt ℝ (fun z => (starRingEnd ℂ) (ψ z)) z :=
      hcw.differentiable (by norm_num) z
    have h2 : DifferentiableAt ℝ (dz ψ) z := hA.differentiable (by norm_num) z
    rw [Work.MRMT.Sobolev.dzbar_mul h1 h2, Work.MRMT.QC.dzbar_conj (hψd z)]
  have hcs_dzbarA : HasCompactSupport (dzbar (dz ψ)) := by
    have h := hcs_A.fderiv ℝ
    have h2 := h.comp_left (g := dzbarCLM) (by rw [dzbarCLM_apply]; simp)
    have hfun : dzbar (dz ψ) = dzbarCLM ∘ (fderiv ℝ (dz ψ)) :=
      funext (fun w => dzbar_eq_dzbarCLM (dz ψ) w)
    rwa [← hfun] at h2
  have hcont_dzbarA : Continuous (dzbar (dz ψ)) :=
    Work.MRMT.Sobolev.continuous_dzbar_of_contDiff (dz ψ) (n := 1) (by norm_num) hA
  have hInt_cA : Integrable (fun z => (starRingEnd ℂ) (ψ z) * dzbar (dz ψ) z) :=
    Continuous.integrable_of_hasCompactSupport (hcont_cw.mul hcont_dzbarA)
      (hcs_dzbarA.mul_left (f := fun z => (starRingEnd ℂ) (ψ z)))
  have hInt_AA : Integrable (fun z => dz ψ z * (starRingEnd ℂ) (dz ψ z)) :=
    Continuous.integrable_of_hasCompactSupport
      (hA.continuous.mul (contDiff_starRingEnd_comp hA).continuous) hcs_A.mul_right
  have hexp1 : ∫ z, dzbar (fun z => (starRingEnd ℂ) (ψ z) * dz ψ z) z
      = (∫ z, (starRingEnd ℂ) (ψ z) * dzbar (dz ψ) z)
        + ∫ z, dz ψ z * (starRingEnd ℂ) (dz ψ z) := by
    rw [integral_congr_ae (Eventually.of_forall hpt1), integral_add hInt_cA hInt_AA]
  have hcast1 : ∫ z, dz ψ z * (starRingEnd ℂ) (dz ψ z)
      = ((∫ z, ‖dz ψ z‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : ∫ z, dz ψ z * (starRingEnd ℂ) (dz ψ z)
        = ∫ z, (((‖dz ψ z‖ ^ 2 : ℝ)) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h1]; exact integral_ofReal
  have hE1 : ((∫ z, ‖dz ψ z‖ ^ 2 : ℝ) : ℂ)
      = -(∫ z, (starRingEnd ℂ) (ψ z) * dzbar (dz ψ) z) := by
    have hsum : (∫ z, (starRingEnd ℂ) (ψ z) * dzbar (dz ψ) z)
        + ((∫ z, ‖dz ψ z‖ ^ 2 : ℝ) : ℂ) = 0 := by
      rw [← hcast1, ← hexp1]; exact hz1
    exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using hsum)
  -- ===== G2 = conj psi * dzbar psi =====
  have hG2cd : ContDiff ℝ 1 (fun z => (starRingEnd ℂ) (ψ z) * dzbar ψ z) :=
    (hcw.of_le (by norm_num : (1:WithTop ℕ∞) ≤ 2)).mul hB
  have hG2cs : HasCompactSupport (fun z => (starRingEnd ℂ) (ψ z) * dzbar ψ z) :=
    hcs_B.mul_left (f := fun z => (starRingEnd ℂ) (ψ z))
  have hz2 : ∫ z, dz (fun z => (starRingEnd ℂ) (ψ z) * dzbar ψ z) z = 0 :=
    integral_dz_eq_zero_of_contDiff _ (n := 1) (by norm_num) hG2cd hG2cs
  have hpt2 : ∀ z, dz (fun z => (starRingEnd ℂ) (ψ z) * dzbar ψ z) z
      = (starRingEnd ℂ) (dzbar ψ z) * dzbar ψ z + (starRingEnd ℂ) (ψ z) * dz (dzbar ψ) z := by
    intro z
    have h1 : DifferentiableAt ℝ (fun z => (starRingEnd ℂ) (ψ z)) z :=
      hcw.differentiable (by norm_num) z
    have h2 : DifferentiableAt ℝ (dzbar ψ) z := hB.differentiable (by norm_num) z
    rw [Work.MRMT.QC.dz_mul h1 h2, Work.MRMT.QC.dz_conj (hψd z)]
  have hcs_dB : HasCompactSupport (dz (dzbar ψ)) := by
    have h := hcs_B.fderiv ℝ
    have h2 := h.comp_left (g := dzCLM) (by rw [dzCLM_apply]; simp)
    have hfun : dz (dzbar ψ) = dzCLM ∘ (fderiv ℝ (dzbar ψ)) :=
      funext (fun w => dz_eq_dzCLM (dzbar ψ) w)
    rwa [← hfun] at h2
  have hcont_dB : Continuous (dz (dzbar ψ)) :=
    continuous_dz_of_contDiff (dzbar ψ) (n := 1) (by norm_num) hB
  have hInt_cB : Integrable (fun z => (starRingEnd ℂ) (ψ z) * dz (dzbar ψ) z) :=
    Continuous.integrable_of_hasCompactSupport (hcont_cw.mul hcont_dB)
      (hcs_dB.mul_left (f := fun z => (starRingEnd ℂ) (ψ z)))
  have hInt_BB : Integrable (fun z => (starRingEnd ℂ) (dzbar ψ z) * dzbar ψ z) :=
    Continuous.integrable_of_hasCompactSupport
      ((contDiff_starRingEnd_comp hB).continuous.mul hB.continuous)
      (hasCompactSupport_starRingEnd_comp hcs_B).mul_right
  have hexp2 : ∫ z, dz (fun z => (starRingEnd ℂ) (ψ z) * dzbar ψ z) z
      = (∫ z, (starRingEnd ℂ) (dzbar ψ z) * dzbar ψ z)
        + ∫ z, (starRingEnd ℂ) (ψ z) * dz (dzbar ψ) z := by
    rw [integral_congr_ae (Eventually.of_forall hpt2), integral_add hInt_BB hInt_cB]
  have hcast2 : ∫ z, (starRingEnd ℂ) (dzbar ψ z) * dzbar ψ z
      = ((∫ z, ‖dzbar ψ z‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : ∫ z, (starRingEnd ℂ) (dzbar ψ z) * dzbar ψ z
        = ∫ z, (((‖dzbar ψ z‖ ^ 2 : ℝ)) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [mul_comm (starRingEnd ℂ (dzbar ψ z)) (dzbar ψ z), Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
    rw [h1]; exact integral_ofReal
  have hE2 : ((∫ z, ‖dzbar ψ z‖ ^ 2 : ℝ) : ℂ)
      = -(∫ z, (starRingEnd ℂ) (ψ z) * dz (dzbar ψ) z) := by
    have hsum : (∫ z, (starRingEnd ℂ) (ψ z) * dz (dzbar ψ) z)
        + ((∫ z, ‖dzbar ψ z‖ ^ 2 : ℝ) : ℂ) = 0 := by
      rw [← hcast2, add_comm, ← hexp2]; exact hz2
    exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using hsum)
  have hcomm : ∫ z, (starRingEnd ℂ) (ψ z) * dzbar (dz ψ) z
      = ∫ z, (starRingEnd ℂ) (ψ z) * dz (dzbar ψ) z := by
    apply integral_congr_ae
    filter_upwards with z
    rw [dzbar_dz_commute hψ z]
  have hfin : ((∫ z, ‖dz ψ z‖ ^ 2 : ℝ) : ℂ) = ((∫ z, ‖dzbar ψ z‖ ^ 2 : ℝ) : ℂ) := by
    rw [hE1, hE2, hcomm]
  exact Complex.ofReal_injective hfin

/-- The energy identity for compactly supported `C¹` functions. -/
theorem energy_identity (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) :
    ∫ z, ‖Work.MRMT.dz φ z‖ ^ 2 ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ)
      = ∫ z, ‖Work.MRMT.dzbar φ z‖ ^ 2 ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
  Work.MRMT.Beltrami.energy_identity_of_contDiff_one φ hφ hs
    (fun ψ hψ hcs => energy_identity_of_contDiff_two ψ hψ hcs)

end Work.MRMT.Beltrami
