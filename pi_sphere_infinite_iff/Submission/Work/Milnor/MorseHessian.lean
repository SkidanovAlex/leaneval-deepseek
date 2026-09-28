import Mathlib
import Submission.Work.Milnor.ChartDefs
import Submission.Work.Milnor.ChartFDeriv
import Submission.Work.Milnor.eta_facts
import Submission.Work.Milnor.hfun_facts
import Submission.Work.Milnor.stereo_chart_re
import Submission.Work.Morse.Basic

set_option synthInstance.maxHeartbeats 400000

/-!
# The Hessian of the chart expression of `morseChart2`

In the product chart at `(0, y₀)` (with `y₀ = ±1`), the function `morseChart2` becomes
`x ↦ c · (hfun x.2 · eta x.1)` with `c = (y₀ : Quaternion ℝ).re = ±1`.  We compute its Hessian
at the origin and show it is nondegenerate.
-/

open scoped Manifold ContDiff Topology RealInnerProductSpace
open TopologicalSpace Set Metric
open Submission.Milnor

namespace Work.Milnor
noncomputable section

/-- The chart expression of `morseChart2` up to the constant `c`: `Φ x = eta x.1 * hfun x.2`. -/
def Phi (x : ME) : ℝ := eta x.1 * hfun x.2

/-- The Hessian of `eta ∘ fst` at `0`, as a continuous linear map. -/
def Lf : ME →L[ℝ] ME →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ ME E4 ℝ).flip (ContinuousLinearMap.fst ℝ E4 E3)
    ∘L ((- (innerSL ℝ : E4 →L[ℝ] E4 →L[ℝ] ℝ)) ∘L (ContinuousLinearMap.fst ℝ E4 E3))

/-- The Hessian of `hfun ∘ snd` at `0`, as a continuous linear map. -/
def Lg : ME →L[ℝ] ME →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ ME E3 ℝ).flip (ContinuousLinearMap.snd ℝ E4 E3)
    ∘L ((- (innerSL ℝ : E3 →L[ℝ] E3 →L[ℝ] ℝ)) ∘L (ContinuousLinearMap.snd ℝ E4 E3))

lemma hasFDerivAt_fderiv_eta :
    HasFDerivAt (fderiv ℝ eta) (- (innerSL ℝ : E4 →L[ℝ] E4 →L[ℝ] ℝ)) 0 := by
  have hfun : fderiv ℝ eta
      = fun u : E4 => ceta u • (innerSL ℝ : E4 →L[ℝ] E4 →L[ℝ] ℝ) u :=
    funext eta_facts.2.1
  rw [hfun]
  have hsm := (hasFDerivAt_ceta 0).smul (𝕜' := ℝ) (F := E4 →L[ℝ] ℝ)
    (ContinuousLinearMap.hasFDerivAt (innerSL ℝ : E4 →L[ℝ] E4 →L[ℝ] ℝ))
  convert hsm using 1
  all_goals first | rfl | (ext x y; simp [ceta]) | simp [ceta]

lemma hasFDerivAt_fderiv_hfun :
    HasFDerivAt (fderiv ℝ hfun) (- (innerSL ℝ : E3 →L[ℝ] E3 →L[ℝ] ℝ)) 0 := by
  have hfun : fderiv ℝ hfun
      = fun u : E3 => cgam u • (innerSL ℝ : E3 →L[ℝ] E3 →L[ℝ] ℝ) u :=
    funext hfun_facts.2.2.1
  rw [hfun]
  have hsm := (cgam_hasFDerivAt_zero).smul (𝕜' := ℝ) (F := E3 →L[ℝ] ℝ)
    (ContinuousLinearMap.hasFDerivAt (innerSL ℝ : E3 →L[ℝ] E3 →L[ℝ] ℝ))
  convert hsm using 1
  all_goals first | rfl | (ext x y; simp [cgam_zero]) | simp [cgam_zero]

lemma differentiable_eta : Differentiable ℝ eta :=
  fun u => (hasFDerivAt_eta u).differentiableAt

lemma differentiable_hfun : Differentiable ℝ hfun :=
  fun u => (hasFDerivAt_hfun u).differentiableAt

lemma differentiable_eta_fst : Differentiable ℝ (fun x : ME => eta x.1) :=
  differentiable_eta.comp differentiable_fst

lemma differentiable_hfun_snd : Differentiable ℝ (fun x : ME => hfun x.2) :=
  differentiable_hfun.comp differentiable_snd

lemma hasFDerivAt_fderiv_eta_fst :
    HasFDerivAt (fderiv ℝ (fun x : ME => eta x.1)) Lf 0 :=
  hasFDerivAt_fderiv_comp_fst (f := eta) (L := - (innerSL ℝ : E4 →L[ℝ] E4 →L[ℝ] ℝ))
    hasFDerivAt_fderiv_eta differentiable_eta

lemma hasFDerivAt_fderiv_hfun_snd :
    HasFDerivAt (fderiv ℝ (fun x : ME => hfun x.2)) Lg 0 :=
  hasFDerivAt_fderiv_comp_snd (f := hfun) (L := - (innerSL ℝ : E3 →L[ℝ] E3 →L[ℝ] ℝ))
    hasFDerivAt_fderiv_hfun differentiable_hfun

lemma fderiv_eta_fst_zero : fderiv ℝ (fun x : ME => eta x.1) 0 = 0 := by
  rw [fderiv_comp_fst differentiable_eta 0,
    show (0 : ME).1 = (0 : E4) from rfl, eta_facts.1]
  simp

lemma fderiv_hfun_snd_zero : fderiv ℝ (fun x : ME => hfun x.2) 0 = 0 := by
  rw [fderiv_comp_snd differentiable_hfun 0,
    show (0 : ME).2 = (0 : E3) from rfl, hfun_facts.2.1]
  simp

lemma hasFDerivAt_eta_fst_zero :
    HasFDerivAt (fun x : ME => eta x.1) (0 : ME →L[ℝ] ℝ) 0 := by
  rw [← fderiv_eta_fst_zero]
  exact (differentiable_eta_fst 0).hasFDerivAt

lemma hasFDerivAt_hfun_snd_zero :
    HasFDerivAt (fun x : ME => hfun x.2) (0 : ME →L[ℝ] ℝ) 0 := by
  rw [← fderiv_hfun_snd_zero]
  exact (differentiable_hfun_snd 0).hasFDerivAt

lemma eta_zero : eta 0 = 1 := by simp [eta]

lemma eta_fst_zero : eta ((0 : ME).1) = 1 := by
  rw [show (0 : ME).1 = (0 : E4) from rfl, eta_zero]

lemma hfun_snd_zero : hfun ((0 : ME).2) = 1 := by
  rw [show (0 : ME).2 = (0 : E3) from rfl, hfun_facts.1]

lemma hasFDerivAt_Phi_zero : HasFDerivAt Phi (0 : ME →L[ℝ] ℝ) 0 := by
  have hPhi : Phi = fun x : ME => eta x.1 * hfun x.2 := rfl
  rw [hPhi]
  have h := hasFDerivAt_eta_fst_zero.mul hasFDerivAt_hfun_snd_zero
  rw [eta_fst_zero, hfun_snd_zero, one_smul, add_zero] at h
  exact h

lemma hasFDerivAt_fderiv_Phi : HasFDerivAt (fderiv ℝ Phi) (Lg + Lf) 0 := by
  have hPhi : Phi = fun x : ME => eta x.1 * hfun x.2 := rfl
  rw [hPhi]
  have h := hasFDerivAt_fderiv_mul_zero
    (f := fun x : ME => eta x.1) (g := fun x : ME => hfun x.2)
    (Lf := Lf) (Lg := Lg) hasFDerivAt_eta_fst_zero hasFDerivAt_hfun_snd_zero
    hasFDerivAt_fderiv_eta_fst hasFDerivAt_fderiv_hfun_snd
    differentiable_eta_fst differentiable_hfun_snd
  rw [eta_fst_zero, hfun_snd_zero, one_smul, one_smul] at h
  exact h

lemma differentiable_Phi : Differentiable ℝ Phi :=
  differentiable_eta_fst.mul differentiable_hfun_snd

lemma Lf_apply (v w : ME) : Lf v w = - inner ℝ v.1 w.1 := by
  simp only [Lf, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.neg_apply]
  rw [show (ContinuousLinearMap.fst ℝ E4 E3) v = v.1 from rfl,
    show (ContinuousLinearMap.fst ℝ E4 E3) w = w.1 from rfl,
    innerSL_apply_apply]

lemma Lg_apply (v w : ME) : Lg v w = - inner ℝ v.2 w.2 := by
  simp only [Lg, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.neg_apply]
  rw [show (ContinuousLinearMap.snd ℝ E4 E3) v = v.2 from rfl,
    show (ContinuousLinearMap.snd ℝ E4 E3) w = w.2 from rfl,
    innerSL_apply_apply]

lemma fderiv_Phi_zero : fderiv ℝ Phi 0 = 0 := hasFDerivAt_Phi_zero.fderiv

lemma fderiv_fderiv_Phi : fderiv ℝ (fderiv ℝ Phi) 0 = Lg + Lf :=
  hasFDerivAt_fderiv_Phi.fderiv

lemma morseChart2_chart_symm (y₀ : QS3)
    (hy : (y₀ : Quaternion ℝ) = 1 ∨ (y₀ : Quaternion ℝ) = -1) :
    (fun x : ME => morseChart2 ((chartAt (ModelProd E4 E3) ((0:E4), y₀)).symm
        (((𝓡 4).prod (𝓡 3)).symm x)))
      = fun x : ME => (y₀ : Quaternion ℝ).re * Phi x := by
  have hI : ((𝓡 4).prod (𝓡 3)) = modelWithCornersSelf ℝ ME := modelWithCornersSelf_prod.symm
  have hIsymm : ∀ x : ME, (((𝓡 4).prod (𝓡 3)).symm x : ModelProd E4 E3) = x := by
    intro x
    rw [hI]
    simp only [modelWithCornersSelf_coe_symm]
    rfl
  have hsymm : ∀ x : ME,
      (chartAt (ModelProd E4 E3) ((0:E4), y₀)).symm x
        = (x.1, (chartAt E3 y₀).symm x.2) := by
    intro x
    rw [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_symm,
      OpenPartialHomeomorph.prod_apply]
    simp [chartAt_self_eq]
  funext x
  rw [hIsymm x, hsymm x]
  simp only [morseChart2, Phi, Hfun, eta, div_eq_mul_inv]
  rw [(stereo_chart_re y₀ hy).2 x.2]
  ring

lemma chartAt_prod_apply_self (y₀ : QS3)
    (hy : (y₀ : Quaternion ℝ) = 1 ∨ (y₀ : Quaternion ℝ) = -1) :
    (chartAt (ModelProd E4 E3) ((0:E4), y₀)) ((0:E4), y₀) = (0 : E4 × E3) := by
  rw [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_apply]
  simp only [chartAt_self_eq]
  rw [OpenPartialHomeomorph.refl_apply, (stereo_chart_re y₀ hy).1]
  rfl

theorem hasNondegHessian_chart2 (y₀ : QS3)
    (hy : (y₀ : Quaternion ℝ) = 1 ∨ (y₀ : Quaternion ℝ) = -1) :
    HasNondegHessian (I := (𝓡 4).prod (𝓡 3)) (n := ∞) morseChart2 ((0 : E4), y₀) := by
  have hc_ne : (y₀ : Quaternion ℝ).re ≠ 0 := by
    rcases hy with h | h
    · rw [h]; exact one_ne_zero
    · rw [h]; simp only [Quaternion.re_neg, Quaternion.re_one]; norm_num
  have hI : ((𝓡 4).prod (𝓡 3)) = modelWithCornersSelf ℝ ME := modelWithCornersSelf_prod.symm
  have hIcoe : ∀ y : ME, (((𝓡 4).prod (𝓡 3)) y : ModelProd E4 E3) = y := by
    intro y
    rw [hI]
    simp [modelWithCornersSelf_coe]
  have hep : (chartAt (ModelProd E4 E3) ((0:E4), y₀)) ((0:E4), y₀) = (0 : E4 × E3) :=
    chartAt_prod_apply_self y₀ hy
  have hpt : ((𝓡 4).prod (𝓡 3)) ((chartAt (ModelProd E4 E3) ((0:E4), y₀)) ((0:E4), y₀))
      = (0 : ME) := by rw [hep, hIcoe]
  refine ⟨chartAt (ModelProd E4 E3) ((0:E4), y₀), IsManifold.chart_mem_maximalAtlas _,
    mem_chart_source _ _, ?_, ?_⟩
  · rw [hpt, morseChart2_chart_symm y₀ hy]
    rw [show (fun x : ME => (y₀ : Quaternion ℝ).re * Phi x)
        = (y₀ : Quaternion ℝ).re • Phi from funext (fun x => by simp [smul_eq_mul])]
    rw [fderiv_const_smul (differentiable_Phi 0) (y₀ : Quaternion ℝ).re, fderiv_Phi_zero,
      smul_zero]
  · rw [hpt]
    have h2 : fderiv ℝ (fderiv ℝ (fun x : ME =>
          (y₀ : Quaternion ℝ).re * Phi x)) 0
        = (y₀ : Quaternion ℝ).re • (Lg + Lf) := by
      have h := hasFDerivAt_fderiv_Phi.const_smul (y₀ : Quaternion ℝ).re
      have heq : ((y₀ : Quaternion ℝ).re • fderiv ℝ Phi)
          = fderiv ℝ ((y₀ : Quaternion ℝ).re • Phi) := by
        funext x
        rw [Pi.smul_apply, fderiv_const_smul (differentiable_Phi x) (y₀ : Quaternion ℝ).re]
      rw [heq] at h
      exact h.fderiv
    rw [morseChart2_chart_symm y₀ hy, h2]
    intro v hv
    have hvv := hv v
    have heval : (((y₀ : Quaternion ℝ).re • (Lg + Lf)) v) v
        = (y₀ : Quaternion ℝ).re * (-inner ℝ v.2 v.2 + -inner ℝ v.1 v.1) := by
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, Lg_apply,
        Lf_apply, smul_eq_mul]
    rw [heval] at hvv
    have hsum : inner ℝ v.1 v.1 + inner ℝ v.2 v.2 = 0 := by
      rcases mul_eq_zero.mp hvv with h | h
      · exact absurd h hc_ne
      · linarith
    have h1 : ‖v.1‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      linarith [real_inner_self_nonneg (x := v.1), real_inner_self_nonneg (x := v.2)]
    have h3 : ‖v.2‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      linarith [real_inner_self_nonneg (x := v.1), real_inner_self_nonneg (x := v.2)]
    exact Prod.ext (norm_eq_zero.mp (sq_eq_zero_iff.mp h1))
      (norm_eq_zero.mp (sq_eq_zero_iff.mp h3))

end
end Work.Milnor
