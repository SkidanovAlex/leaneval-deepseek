import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.R1G.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-!
# The cut-off's radial logarithmic derivative is nonzero inside the annulus `(L, 2L)`

`Work.Stability.chi` is the `ContDiffBump 0` with `rIn = 1`, `rOut = 2`: `chi = 1` on `[-1,1]`
and `chi = 0` for `|x| ≥ 2`.  Hence `chi 1 = 1 ≠ 0 = chi 2`, and by the mean value theorem the
derivative of `chi` does not vanish identically on `(1,2)`.  Scaling back, the radial logarithmic
derivative `chiRad P r z = deriv chi (ρ(r,z)/L)/L` of the cut-off `χ(ρ/L)` is nonzero somewhere in
the annulus `L < ρ < 2L` — i.e. the cut-off deficit `cutDeficit` is a genuinely non-trivial object
on that annulus.
-/

/-- **The cut-off `chi` is not locally constant on `(1,2)`**: there is a point of the open interval
where its derivative does not vanish.  This is the mean value theorem applied to the two endpoint
values `chi 1 = 1` and `chi 2 = 0`. -/
theorem exists_deriv_chi_ne_zero :
    ∃ s ∈ Set.Ioo (1 : ℝ) 2, deriv Work.Stability.chi s ≠ 0 := by
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope Work.Stability.chi (a := 1) (b := 2)
    (by norm_num) Work.Stability.chi_contDiff.continuous.continuousOn
    ((Work.Stability.chi_contDiff.differentiable (by simp)).differentiableOn)
  refine ⟨c, hc, ?_⟩
  have h2 : Work.Stability.chi 2 = 0 := Work.Stability.chi_eq_zero (by norm_num)
  have h1 : Work.Stability.chi 1 = 1 := Work.Stability.chi_eq_one (by norm_num)
  rw [hcd, h2, h1]
  norm_num

/-- The meridian point `(s·L, 0)` has `rhoP = s·L` for `s > 0` and `L > 0`. -/
private theorem rhoP_mul_L_zero {s L : ℝ} (hs : 0 < s) (hL : 0 < L) :
    Work.Cyl.rhoP (s * L) 0 = s * L := by
  rw [Work.Cyl.rhoP, mul_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, ← mul_pow,
    Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hs hL)]

/-- **There is a point of the annulus `L < ρ < 2L` where `chiRad` does not vanish.**  This is the
statement that the radial cut-off `χ(ρ/L)` is not locally constant on the annulus, i.e. that the
cut-off deficit of the meridian residual is genuinely present there. -/
theorem exists_chiRad_ne_zero_of_annulus {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) :
    ∃ r z : ℝ, P.L < Work.Cyl.rhoP r z ∧ Work.Cyl.rhoP r z < 2 * P.L
      ∧ Work.R1G.chiRad P r z ≠ 0 := by
  obtain ⟨s, hs, hsd⟩ := exists_deriv_chi_ne_zero
  have hL := P.hL
  have hs1 : 1 < s := hs.1
  have hs2 : s < 2 := hs.2
  have hs0 : 0 < s := lt_trans one_pos hs1
  have hrho : Work.Cyl.rhoP (s * P.L) 0 = s * P.L := rhoP_mul_L_zero hs0 hL
  refine ⟨s * P.L, 0, ?_, ?_, ?_⟩
  · rw [hrho]; nlinarith
  · rw [hrho]; nlinarith
  · rw [chiRad, hrho, mul_div_cancel_right₀ s (ne_of_gt hL)]
    exact div_ne_zero hsd (ne_of_gt hL)

end Work.R1G
