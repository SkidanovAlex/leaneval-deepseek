import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Submission.Commons.Analysis.InnerProductSpace.fderiv_norm_single
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonneg_of_localMin

open scoped Topology RealInnerProductSpace
open Filter

namespace Commons.Analysis.Calculus

set_option autoImplicit false

theorem iteratedFDeriv_two_norm_apply {d : ℕ} (y W : EuclideanSpace ℝ (Fin d)) (hy : y ≠ 0) :
    (iteratedFDeriv ℝ 2 (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖) y) ![W, W]
      = ‖W‖ ^ 2 / ‖y‖ - (inner ℝ y W) ^ 2 / ‖y‖ ^ 3 := by
  have hcont : ContDiffAt ℝ 2 (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖) y :=
    contDiffAt_norm ℝ hy
  have hψ0 : HasDerivAt (fun t : ℝ => y + t • W) W 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • W) ((1:ℝ) • W) 0 :=
      (hasDerivAt_id (0:ℝ)).smul_const W
    have h2 : HasDerivAt (fun t : ℝ => y + t • W) ((1:ℝ) • W) 0 := h1.const_add y
    simpa using h2
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), y + t • W ≠ 0 := by
    have hc : ContinuousAt (fun t : ℝ => y + t • W) 0 := by fun_prop
    exact hc.eventually (isOpen_compl_singleton.mem_nhds (by simpa using hy))
  have hyne : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hFG : deriv (fun t : ℝ => ‖y + t • W‖)
      =ᶠ[𝓝 (0:ℝ)] ((fun t : ℝ => inner ℝ (y + t • W) W) / fun t : ℝ => ‖y + t • W‖) := by
    filter_upwards [hev] with t ht
    have hψt : HasDerivAt (fun s : ℝ => y + s • W) W t := by
      have h1 : HasDerivAt (fun s : ℝ => s • W) ((1:ℝ) • W) t :=
        (hasDerivAt_id t).smul_const W
      have h2 : HasDerivAt (fun s : ℝ => y + s • W) ((1:ℝ) • W) t := h1.const_add y
      simpa using h2
    have hN : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖)
        ((‖y + t • W‖)⁻¹ • innerSL ℝ (y + t • W)) (y + t • W) :=
      Commons.Analysis.InnerProductSpace.hasFDerivAt_norm_ne_zero ht
    have hcomp := hN.comp_hasDerivAt t hψt
    have hderiv : deriv (fun t : ℝ => ‖y + t • W‖) t
        = ((‖y + t • W‖)⁻¹ • innerSL ℝ (y + t • W)) W := hcomp.deriv
    rw [hderiv]
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, Pi.div_apply]
    rw [div_eq_inv_mul]
  have hu : HasDerivAt (fun t : ℝ => inner ℝ (y + t • W) W) (inner ℝ W W) 0 := by
    have hfun : (fun t : ℝ => inner ℝ (y + t • W) W)
        = fun t : ℝ => inner ℝ y W + t * inner ℝ W W := by
      funext t
      rw [inner_add_left, real_inner_smul_left]
    rw [hfun]
    have h1 : HasDerivAt (fun t : ℝ => t * inner ℝ W W) (inner ℝ W W) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).mul_const (inner ℝ W W)
    simpa using h1.const_add (inner ℝ y W)
  have hv : HasDerivAt (fun t : ℝ => ‖y + t • W‖) (inner ℝ y W / ‖y‖) 0 := by
    have hN : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖)
        ((‖y‖)⁻¹ • innerSL ℝ y) y :=
      Commons.Analysis.InnerProductSpace.hasFDerivAt_norm_ne_zero hy
    have hN' : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖)
        ((‖y‖)⁻¹ • innerSL ℝ y) (y + (0:ℝ) • W) := by simpa using hN
    have hcomp := hN'.comp_hasDerivAt 0 hψ0
    have hcomp' : HasDerivAt (fun t : ℝ => ‖y + t • W‖) (((‖y‖)⁻¹ • innerSL ℝ y) W) 0 :=
      hcomp
    have hval : (((‖y‖)⁻¹ • innerSL ℝ y) W) = inner ℝ y W / ‖y‖ := by
      simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
      rw [div_eq_inv_mul]
    simpa only [hval] using hcomp'
  have hF : deriv ((fun t : ℝ => inner ℝ (y + t • W) W) / fun t : ℝ => ‖y + t • W‖) 0
      = ‖W‖ ^ 2 / ‖y‖ - (inner ℝ y W) ^ 2 / ‖y‖ ^ 3 := by
    have hdiv := HasDerivAt.div hu hv (by simpa using hyne)
    rw [hdiv.deriv]
    rw [real_inner_self_eq_norm_sq]
    simp only [zero_smul, add_zero]
    field_simp
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Commons.Analysis.Calculus.FDeriv.deriv_deriv_comp_line hcont W]
  rw [hFG.deriv_eq, hF]

end Commons.Analysis.Calculus
