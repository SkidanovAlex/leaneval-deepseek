import Mathlib.Analysis.InnerProductSpace.Calculus
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonneg_of_localMin
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_add_quadratic

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace

open scoped RealInnerProductSpace in
theorem quadform_neg_le_of_localMin_paraboloid {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {φ : E → ℝ} {x y : E} {a : ℝ}
    (hφ : ContDiffAt ℝ 2 φ x)
    (hmin : IsLocalMin (fun z : E => φ z + a / 2 * ‖z - y‖ ^ 2) x) (v : E) :
    -a * ‖v‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ φ) x) v v := by
  -- The function `g := φ + (a/2)‖·-y‖²` is `C²` at `x` and has a local min there.
  have hq_cont : ContDiffAt ℝ 2 (fun z : E => a / 2 * ‖z - y‖ ^ 2) x := by
    have hsub : ContDiffAt ℝ 2 (fun z : E => z - y) x := by
      simpa using contDiffAt_id.sub contDiffAt_const
    have hsq : ContDiffAt ℝ 2 (fun z : E => ‖z - y‖ ^ 2) x := ContDiffAt.norm_sq ℝ hsub
    exact contDiffAt_const.mul hsq
  have hg_cont : ContDiffAt ℝ 2 (fun z : E => φ z + a / 2 * ‖z - y‖ ^ 2) x :=
    hφ.add hq_cont
  -- Positivity of the Hessian of `g` at the local minimum.
  have h1 : 0 ≤ (fderiv ℝ (fderiv ℝ (fun z : E => φ z + a / 2 * ‖z - y‖ ^ 2)) x) v v :=
    fderiv_fderiv_nonneg_of_localMin hg_cont hmin v
  -- Compute the Hessian of `g`: it is the Hessian of `φ` plus `a • ⟪·,·⟫`.
  rw [fderiv_fderiv_add_of_contDiffAt hφ hq_cont] at h1
  rw [fderiv_fderiv_mul_norm_sq_sub (E := E) (a / 2) y x] at h1
  simp only [add_apply, smul_apply,
    smul_eq_mul] at h1
  have hc : 2 * (a / 2) = a := by ring
  rw [hc] at h1
  have hinner : ((innerSL ℝ) v) v = ‖v‖ ^ 2 := by
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  rw [hinner] at h1
  linarith

end Commons.Analysis.Calculus.FDeriv
