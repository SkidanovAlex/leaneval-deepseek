import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.RCLike.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT

theorem pzIter_two_bound_of_DzIter_two {F : ℝ → ℝ → ℝ} {C z₀ z θ : ℝ}
    (hz₀ : 0 < z₀) (hz : z₀ / 2 < z) (hC : 0 ≤ C)
    (hd : DifferentiableAt ℝ (fun t => Work.Spaces.pzIter 1 F t θ) z)
    (h1 : |Work.Spaces.Dz F z θ| ≤ C) (h2 : |Work.Spaces.DzIter 2 F z θ| ≤ C) :
    |Work.Spaces.pzIter 2 F z θ| ≤ 8 * C / z₀ ^ 2 := by
  have hz0 : 0 < z := by linarith
  have hzsq : 0 < z ^ 2 := pow_pos hz0 2
  -- `∂_z` of the `z`-slice of `pz F` is `pzIter 2 F`
  have hdg : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pz F t θ) z := by
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz] using hd
  -- the one-variable product rule for `t ↦ t * ∂_z F t θ`
  have hderiv : deriv (fun t : ℝ => t * Work.Spaces.pz F t θ) z
      = Work.Spaces.pz F z θ + z * Work.Spaces.pzIter 2 F z θ := by
    have h1' : deriv ((fun t : ℝ => t) * fun t : ℝ => Work.Spaces.pz F t θ) z
        = deriv (fun t : ℝ => t) z * Work.Spaces.pz F z θ
          + z * deriv (fun t : ℝ => Work.Spaces.pz F t θ) z :=
      deriv_mul (c := fun t : ℝ => t) (d := fun t : ℝ => Work.Spaces.pz F t θ)
        differentiableAt_id hdg
    rw [show (fun t : ℝ => t * Work.Spaces.pz F t θ)
          = ((fun t : ℝ => t) * fun t : ℝ => Work.Spaces.pz F t θ) from rfl,
        h1', deriv_id'', one_mul]
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
  -- hence `D_z² F = D_z F + z² ∂_z²F` at the point
  have hexp : Work.Spaces.DzIter 2 F z θ
      = Work.Spaces.Dz F z θ + z ^ 2 * Work.Spaces.pzIter 2 F z θ := by
    rw [show Work.Spaces.DzIter 2 F z θ
          = z * deriv (fun t : ℝ => t * Work.Spaces.pz F t θ) z from rfl, hderiv]
    show z * (Work.Spaces.pz F z θ + z * Work.Spaces.pzIter 2 F z θ)
        = z * Work.Spaces.pz F z θ + z ^ 2 * Work.Spaces.pzIter 2 F z θ
    ring
  have hsplit : z ^ 2 * Work.Spaces.pzIter 2 F z θ
      = Work.Spaces.DzIter 2 F z θ - Work.Spaces.Dz F z θ := by linarith
  have hkey0 : |z ^ 2 * Work.Spaces.pzIter 2 F z θ| ≤ 2 * C := by
    rw [hsplit]
    calc |Work.Spaces.DzIter 2 F z θ - Work.Spaces.Dz F z θ|
        ≤ |Work.Spaces.DzIter 2 F z θ| + |Work.Spaces.Dz F z θ| := abs_sub _ _
      _ ≤ C + C := add_le_add h2 h1
      _ = 2 * C := by ring
  have hkey : z ^ 2 * |Work.Spaces.pzIter 2 F z θ| ≤ 2 * C := by
    have h := hkey0
    rwa [abs_mul, abs_of_nonneg (sq_nonneg z)] at h
  have hbound : |Work.Spaces.pzIter 2 F z θ| ≤ 2 * C / z ^ 2 := by
    rw [le_div_iff₀ hzsq]
    simpa [mul_comm] using hkey
  have hstep : (2 * C) / z ^ 2 ≤ (2 * C) / (z₀ ^ 2 / 4) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) (by nlinarith [hz, hz₀])
  have hcoe : (2 * C) / (z₀ ^ 2 / 4) = 8 * C / z₀ ^ 2 := by
    field_simp
    ring
  calc |Work.Spaces.pzIter 2 F z θ| ≤ 2 * C / z ^ 2 := hbound
    _ ≤ (2 * C) / (z₀ ^ 2 / 4) := hstep
    _ = 8 * C / z₀ ^ 2 := hcoe

end Work.FTS_RegExport.RXT
