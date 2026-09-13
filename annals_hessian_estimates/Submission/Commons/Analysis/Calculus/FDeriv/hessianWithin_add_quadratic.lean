import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_eq_hessian

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasFDerivAt_norm_sq_sub (x₀ y : E) :
    HasFDerivAt (fun z : E => ‖z - x₀‖ ^ 2) ((2 : ℕ) • innerSL ℝ (y - x₀)) y := by
  have h : HasFDerivAt (fun z : E => z - x₀) (ContinuousLinearMap.id ℝ E) y := by
    simpa using (hasFDerivAt_id y).sub_const x₀
  simpa [ContinuousLinearMap.comp_id] using h.norm_sq

lemma fderiv_norm_sq_sub (x₀ y : E) :
    fderiv ℝ (fun z : E => ‖z - x₀‖ ^ 2) y = (2 : ℕ) • innerSL ℝ (y - x₀) :=
  (hasFDerivAt_norm_sq_sub x₀ y).fderiv

lemma fderiv_mul_norm_sq_sub (ε : ℝ) (x₀ y : E) :
    fderiv ℝ (fun z : E => ε * ‖z - x₀‖ ^ 2) y = (2 * ε) • innerSL ℝ (y - x₀) := by
  rw [show (fun z : E => ε * ‖z - x₀‖ ^ 2) = ε • (fun z : E => ‖z - x₀‖ ^ 2) by
        ext z; rw [Pi.smul_apply, smul_eq_mul]]
  have hd : DifferentiableAt ℝ (fun z : E => ‖z - x₀‖ ^ 2) y :=
    (hasFDerivAt_norm_sq_sub x₀ y).differentiableAt
  rw [fderiv_const_smul hd ε, fderiv_norm_sq_sub]
  rw [← Nat.cast_smul_eq_nsmul ℝ 2, smul_smul]
  congr 1
  ring

lemma hasFDerivAt_clm_comp_sub (L : E →L[ℝ] (E →L[ℝ] ℝ)) (x₀ y : E) :
    HasFDerivAt (fun z : E => L (z - x₀)) L y := by
  have hL : HasFDerivAt (fun z : E => L z) L (y - x₀) :=
    ContinuousLinearMap.hasFDerivAt L (x := y - x₀)
  have hg : HasFDerivAt (fun z : E => z - x₀) (ContinuousLinearMap.id ℝ E) y := by
    simpa using (hasFDerivAt_id y).sub_const x₀
  have h := hL.comp y hg
  simpa [ContinuousLinearMap.comp_id, Function.comp_def] using h

lemma fderiv_fderiv_mul_norm_sq_sub (ε : ℝ) (x₀ y : E) :
    fderiv ℝ (fderiv ℝ (fun z : E => ε * ‖z - x₀‖ ^ 2)) y = (2 * ε) • innerSL ℝ := by
  have hf : fderiv ℝ (fun z : E => ε * ‖z - x₀‖ ^ 2)
      = fun z => (2 * ε) • innerSL ℝ (z - x₀) := funext fun z => fderiv_mul_norm_sq_sub ε x₀ z
  rw [hf]
  have h := hasFDerivAt_clm_comp_sub ((2 * ε) • innerSL ℝ) x₀ y
  simpa [smul_apply] using h.fderiv

theorem fderiv_fderiv_add_of_contDiffAt {φ q : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ 2 φ x) (hq : ContDiffAt ℝ 2 q x) :
    fderiv ℝ (fderiv ℝ (fun y => φ y + q y)) x
      = fderiv ℝ (fderiv ℝ φ) x + fderiv ℝ (fderiv ℝ q) x := by
  have hφ_ev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ φ y :=
    (hφ.eventually (by norm_num)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hq_ev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ q y :=
    (hq.eventually (by norm_num)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hd : fderiv ℝ (fun y => φ y + q y) =ᶠ[𝓝 x] fun y => fderiv ℝ φ y + fderiv ℝ q y := by
    filter_upwards [hφ_ev, hq_ev] with y h1 h2
    exact fderiv_fun_add h1 h2
  have h1 : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have h2 : DifferentiableAt ℝ (fderiv ℝ q) x :=
    (hq.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  rw [hd.fderiv_eq, fderiv_fun_add h1 h2]

theorem hessianWithin_add_quadratic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {φ : E → ℝ} {s : Set E} (hs : IsOpen s) {x₀ : E} {x : E} (hx : x ∈ s) {ε : ℝ}
    (hφ : ContDiffWithinAt ℝ 2 φ s x) :
    InnerProductSpace.continuousLinearMapOfBilin
        (fderivWithin ℝ (fderivWithin ℝ (fun y => φ y + ε * ‖y - x₀‖ ^ 2) s) s x)
      = InnerProductSpace.continuousLinearMapOfBilin
          (fderivWithin ℝ (fderivWithin ℝ φ s) s x)
        + (2 * ε) • (1 : E →L[ℝ] E) := by
  have hsx : s ∈ 𝓝 x := hs.mem_nhds hx
  rw [hessianWithin_eq_hessian (E := E) (u := fun y => φ y + ε * ‖y - x₀‖ ^ 2) hsx,
      hessianWithin_eq_hessian (E := E) (u := φ) hsx]
  have hφ_at : ContDiffAt ℝ 2 φ x := hφ.contDiffAt hsx
  have hq_at : ContDiffAt ℝ 2 (fun y : E => ε * ‖y - x₀‖ ^ 2) x := by
    have hsub : ContDiffAt ℝ 2 (fun y : E => y - x₀) x := by
      simpa using contDiffAt_id.sub contDiffAt_const
    have hsq : ContDiffAt ℝ 2 (fun y : E => ‖y - x₀‖ ^ 2) x := ContDiffAt.norm_sq ℝ hsub
    have hc : ContDiffAt ℝ 2 (fun _ : E => ε) x := contDiffAt_const
    simpa using hc.mul hsq
  apply ContinuousLinearMap.ext
  intro v
  refine ext_inner_right ℝ fun w => ?_
  rw [fderiv_fderiv_add_of_contDiffAt hφ_at hq_at, fderiv_fderiv_mul_norm_sq_sub]
  simp only [InnerProductSpace.continuousLinearMapOfBilin_apply, add_apply, smul_apply,
    inner_add_left, real_inner_smul_left, one_apply_eq_self, smul_eq_mul, coe_innerSL_apply]

end Commons.Analysis.Calculus.FDeriv