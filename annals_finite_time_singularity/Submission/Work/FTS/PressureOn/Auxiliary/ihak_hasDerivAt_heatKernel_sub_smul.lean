import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

theorem ihak_hasDerivAt_heatKernel_sub_smul (t : ℝ) (ht : 0 < t) (z h : Work.FTS.PressureOn.R3)
    (s : ℝ) :
    HasDerivAt (fun r : ℝ => Work.FTS.PressureOn.Auxiliary.heatKernel t (z - r • h))
      (Work.FTS.PressureOn.Auxiliary.heatKernel t (z - s • h) * (inner ℝ (z - s • h) h) / (2 * t))
      s := by
  -- The heat kernel along the affine line `r ↦ z - r • h` is a constant times the exponential of
  -- a quadratic polynomial in `r`; we differentiate that explicitly.
  have ht4 : (4 * t) ≠ 0 := by positivity
  -- expansion of the squared norm along the line
  have hnorm : ∀ r : ℝ, ‖z - r • h‖ ^ 2 = r^2 * ‖h‖^2 - 2*r*(inner ℝ z h) + ‖z‖^2 := by
    intro r
    rw [norm_sub_sq (𝕜 := ℝ), real_inner_smul_right, norm_smul]
    simp only [RCLike.re_to_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  -- the derivative of that quadratic
  have hpoly : HasDerivAt (fun r : ℝ => r^2 * ‖h‖^2 - 2*r*(inner ℝ z h) + ‖z‖^2)
      (2*s*‖h‖^2 - 2*(inner ℝ z h)) s := by
    have hA' : HasDerivAt (fun r : ℝ => r ^ 2 * ‖h‖^2) (2 * s * ‖h‖^2) s := by
      simpa using ((hasDerivAt_id s).pow 2).mul_const (‖h‖^2)
    have hB' : HasDerivAt (fun r : ℝ => 2 * r * (inner ℝ z h)) (2 * (inner ℝ z h)) s := by
      simpa using (((hasDerivAt_id s).const_mul 2).mul_const (inner ℝ z h))
    have hC' : HasDerivAt (fun r : ℝ => ‖z‖^2) 0 s := hasDerivAt_const s (‖z‖^2)
    have h := (hA'.sub hB').add hC'
    convert h using 2
    ring
  -- `⟪z - s • h, h⟫ / (2t) = -(2 s ‖h‖² - 2 ⟪z, h⟫) / (4t)`
  have hinner : (inner ℝ (z - s • h) h)/(2*t) = -(2*s*‖h‖^2 - 2*(inner ℝ z h))/(4*t) := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
    ring
  have hG : HasDerivAt (fun r : ℝ => -((r^2 * ‖h‖^2 - 2*r*(inner ℝ z h) + ‖z‖^2)/(4*t)))
      ((inner ℝ (z - s • h) h)/(2*t)) s := by
    have h := (hpoly.div_const (4*t)).neg
    convert h using 1
    rw [← neg_div]
    exact hinner
  have hexp := hG.exp
  have hfin := hexp.const_mul ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)))
  convert hfin using 1
  · funext r
    rw [heatKernel, hnorm r]
  · rw [heatKernel, hnorm s]
    ring

end Work.FTS.PressureOn.Auxiliary
