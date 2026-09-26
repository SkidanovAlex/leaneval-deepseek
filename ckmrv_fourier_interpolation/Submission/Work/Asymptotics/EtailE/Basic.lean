/-
# The `E`-region (`KEpsilon`): elementary geometry

`E = KEpsilon = {w ∈ 𝒟 : 2 ≤ Im (S • w)} = S(𝔽)` is the cusp-`0` neighbourhood of `𝒟`.  This
file collects the elementary geometry of `E` used by the tail analysis on `E`.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.MFix.KXiDefs
import Submission.Work.Asymptotics.psi_InP
import Submission.Work.Kernels.KernelFacts.KPlusCoeff_slash_S
import Submission.Work.Kernels.KernelFacts.KMinus_Sopm
import Submission.Work.Kernels.KernelFacts.psi2_Sopm
import Submission.Work.Kernels.KernelFacts.psi4_Sopm

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm

namespace Work.Asymptotics.EtailE

open Work.Kernels

lemma E_S_smul_S_smul (w : ℍ) : ModularGroup.S • (ModularGroup.S • w) = w :=
  Work.Asymptotics.S_smul_S_smul w

/-- `S • w ∈ 𝔽` for `w ∈ E`. -/
lemma E_S_mem_Funnel {w : ℍ} (hw : w ∈ KEpsilon) :
    Work.Asymptotics.Funnel (ModularGroup.S • w) :=
  ⟨Work.Asymptotics.S_smul_mem_DomainD hw.1, hw.2⟩

/-- `S • w ∈ 𝒟` for `w ∈ E`. -/
lemma E_S_mem_DomainD {w : ℍ} (hw : w ∈ KEpsilon) :
    ModularGroup.S • w ∈ Work.Asymptotics.DomainD :=
  Work.Asymptotics.S_smul_mem_DomainD hw.1

/-- `Im (S • w) = Im w / ‖w‖²`. -/
lemma E_im_S (w : ℍ) :
    (ModularGroup.S • w).im = w.im / ‖(w : ℂ)‖ ^ 2 := by
  rw [Work.Kernels.im_smul_eq]
  have hj : Work.Kernels.jFun ModularGroup.S (w : ℂ) = (w : ℂ) := by
    rw [Work.Kernels.jFun_apply]; simp
  rw [hj]

lemma im_sq_le_normSq (w : ℍ) : w.im ^ 2 ≤ ‖(w : ℂ)‖ ^ 2 := by
  have h : ‖(w : ℂ)‖ ^ 2 = ((w : ℂ).re) ^ 2 + ((w : ℂ).im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [h, UpperHalfPlane.coe_im]
  nlinarith [sq_nonneg ((w : ℂ).re)]

/-- On `E`, the disk condition `‖w‖² ≤ Im w / 2`. -/
lemma E_normSq_le {w : ℍ} (hw : w ∈ KEpsilon) : ‖(w : ℂ)‖ ^ 2 ≤ w.im / 2 := by
  have h : 2 ≤ w.im / ‖(w : ℂ)‖ ^ 2 := by rw [← E_im_S]; exact hw.2
  have hpos : 0 < ‖(w : ℂ)‖ ^ 2 := by
    have h0 : 0 < ‖(w : ℂ)‖ := norm_pos_iff.mpr w.ne_zero
    positivity
  rw [le_div_iff₀ hpos] at h
  linarith

/-- `‖w‖ ≤ 1/2` on `E`. -/
lemma E_norm_le_half {w : ℍ} (hw : w ∈ KEpsilon) : ‖(w : ℂ)‖ ≤ 1 / 2 := by
  have h := E_normSq_le hw
  have h2 := im_sq_le_normSq w
  have him : w.im ≤ 1 / 2 := by nlinarith [w.im_pos]
  have h3 : ‖(w : ℂ)‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    have : w.im / 2 ≤ 1 / 4 := by linarith
    linarith
  nlinarith [norm_nonneg (w : ℂ)]

/-- `Im w ≤ 1/2` on `E`. -/
lemma E_im_le_half {w : ℍ} (hw : w ∈ KEpsilon) : w.im ≤ 1 / 2 := by
  have h := E_normSq_le hw
  have h2 := im_sq_le_normSq w
  nlinarith [w.im_pos]

/-- `‖S • w‖ = ‖w‖⁻¹`. -/
lemma E_norm_S (w : ℍ) : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ = (‖(w : ℂ)‖)⁻¹ := by
  have hcoe : ((ModularGroup.S • w : ℍ) : ℂ) = -((w : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  rw [hcoe, norm_neg, norm_inv]

/-- `‖S • w‖ ≤ scale w`. -/
lemma E_norm_S_le_scale (w : ℍ) : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ scale w := by
  rw [E_norm_S]
  have h1 : w.im ≤ ‖(w : ℂ)‖ := Work.Kernels.im_le_coe_norm w
  have h2 : (‖(w : ℂ)‖)⁻¹ ≤ (w.im)⁻¹ := inv_anti₀ w.im_pos h1
  exact le_trans h2 (Work.Kernels.inv_im_le_scale w)

/-- `Im (S • w) ≤ scale w`. -/
lemma E_im_S_le_scale (w : ℍ) : (ModularGroup.S • w).im ≤ scale w := by
  have hpos : 0 < ‖(w : ℂ)‖ ^ 2 := by
    have h0 : 0 < ‖(w : ℂ)‖ := norm_pos_iff.mpr w.ne_zero
    positivity
  have h1 : (ModularGroup.S • w).im ≤ (w.im)⁻¹ := by
    rw [E_im_S, div_le_iff₀ hpos, inv_mul_eq_div, le_div_iff₀ w.im_pos]
    nlinarith [im_sq_le_normSq w]
  exact le_trans h1 (Work.Kernels.inv_im_le_scale w)

/-- `2 ≤ Im (S • w)` on `E`. -/
lemma E_im_S_ge_two {w : ℍ} (hw : w ∈ KEpsilon) : 2 ≤ (ModularGroup.S • w).im := hw.2

/-- `((S • w).im)⁻¹ ≤ 1/2` on `E`. -/
lemma E_inv_im_S_le {w : ℍ} (hw : w ∈ KEpsilon) : ((ModularGroup.S • w).im)⁻¹ ≤ 1 / 2 := by
  rw [inv_le_comm₀ (by linarith [hw.2]) (by norm_num)]
  linarith [hw.2]

/-- `scale (S • w) ≤ 3 * scale w` for `w ∈ E`. -/
lemma E_scale_S_le {w : ℍ} (hw : w ∈ KEpsilon) :
    scale (ModularGroup.S • w) ≤ 3 * scale w := by
  have h1 : (1:ℝ) ≤ scale w := Work.Kernels.one_le_scale w
  have h2 : ((ModularGroup.S • w).im)⁻¹ ≤ 1 / 2 := E_inv_im_S_le hw
  have h3 : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ scale w := E_norm_S_le_scale w
  have h4 : scale (ModularGroup.S • w)
      = 1 + ((ModularGroup.S • w).im)⁻¹ + ‖((ModularGroup.S • w : ℍ) : ℂ)‖ := rfl
  rw [h4]
  linarith

/-- `1 ≤ scale w` (restated). -/
lemma E_one_le_scale (w : ℍ) : 1 ≤ scale w := Work.Kernels.one_le_scale w

end Work.Asymptotics.EtailE

end
