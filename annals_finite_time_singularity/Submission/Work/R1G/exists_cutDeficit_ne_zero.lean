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

open Set

/-- **The explicit cut-off deficit does not vanish identically.**

The cut-off bump `χ` of `Work.Stability` equals `1` at `x = 1` and `0` at `x = 2`, so by the mean
value theorem there is a point `s ∈ (1,2)` at which `χ'(s) = -1 ≠ 0`.  Since

  `chiRad P r z = χ'(ρ(r,z)/L)/L`

depends on `(r,z)` only through `ρ = √(r²+z²)`, any meridian point with `ρ = s·L` has `chiRad ≠ 0`;
taking `(r,z) = (s·L, 0)` (so `ρ = s·L`) and the meridian profiles `ψ = z`, `W = 1` (both independent
of `t`) the bracket of `cutDeficit` is `(∂_zψ)·(r/ρ) - (ψ/r + ∂_rψ)·(z/ρ) = 1`, which gives

  `cutDeficit P (fun r z _ => z) (fun _ _ _ => 1) (s·L) 0 t = χ'(s)/L = -1/L ≠ 0`.

Hence `cutDeficit` is not the zero function: the interface genuinely carries the deficit. -/
theorem exists_cutDeficit_ne_zero {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (t : ℝ) :
    ∃ r z : ℝ, Work.R1G.cutDeficit P (fun r z _ => z) (fun _ _ _ => 1) r z t ≠ 0 := by
  have hL : 0 < P.L := P.hL
  -- The mean value theorem: some `s ∈ (1,2)` has `χ'(s) = (χ 2 - χ 1)/(2 - 1) = -1 ≠ 0`.
  obtain ⟨s, hs, hsd⟩ := exists_deriv_eq_slope Work.Stability.chi
    (by norm_num : (1 : ℝ) < 2)
    Work.Stability.chi_contDiff.continuous.continuousOn
    (Work.Stability.chi_contDiff.differentiable (by simp)).differentiableOn
  have hchi2 : Work.Stability.chi 2 = 0 := Work.Stability.chi_eq_zero (by norm_num)
  have hchi1 : Work.Stability.chi 1 = 1 := Work.Stability.chi_eq_one (by norm_num)
  have hsderiv : deriv Work.Stability.chi s = -1 := by
    rw [hsd, hchi2, hchi1]; norm_num
  -- The candidate point: `r = s·L > 0`, `z = 0`, so that `ρ = s·L` and `ρ/L = s`.
  refine ⟨s * P.L, 0, ?_⟩
  have hs1 : 0 < s := by linarith [hs.1]
  have hr : 0 < s * P.L := mul_pos hs1 hL
  have hrho : Work.Cyl.rhoP (s * P.L) 0 = s * P.L := by
    rw [Work.Cyl.rhoP, zero_pow (by norm_num), add_zero, Real.sqrt_sq_eq_abs, abs_of_pos hr]
  have hdivL : Work.Cyl.rhoP (s * P.L) 0 / P.L = s := by
    rw [hrho]; field_simp
  rw [Work.R1G.cutDeficit_apply, Work.R1G.chiRad, hdivL, hsderiv, hrho]
  have hpdZ : Work.Cyl.pdZ (fun r z : ℝ => z) (s * P.L) 0 = 1 := by
    simp [Work.Cyl.pdZ]
  have hpdR : Work.Cyl.pdR (fun r z : ℝ => z) (s * P.L) 0 = 0 := by
    simp [Work.Cyl.pdR]
  rw [hpdZ, hpdR, div_self (ne_of_gt hr)]
  simp only [zero_div, add_zero, mul_zero, sub_zero, mul_one]
  exact div_ne_zero (by norm_num) (ne_of_gt hL)

end Work.R1G
