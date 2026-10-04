import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

/-- **Every unit vector of `ℝ²` is `(cos c, sin c)`.** -/
theorem exists_cos_sin (v : EuclideanSpace ℝ (Fin 2)) (hv : ‖v‖ = 1) :
    ∃ c : ℝ, Real.cos c = v 0 ∧ Real.sin c = v 1 := by
  -- `v 0` and `v 1` are the two coordinates of a unit vector of the plane, so
  -- `v 0 ^ 2 + v 1 ^ 2 = 1`; the complex number `z = v 0 + v 1 * I` therefore has
  -- norm one, and its argument is the required angle.
  have hsq : v 0 ^ 2 + v 1 ^ 2 = 1 := by
    have h := EuclideanSpace.norm_sq_eq v
    rw [hv, one_pow, Fin.sum_univ_two] at h
    simp only [Real.norm_eq_abs, sq_abs] at h
    linarith
  set z : ℂ := (v 0 : ℂ) + (v 1 : ℂ) * Complex.I with hz_def
  have hre : z.re = v 0 := by simp [z]
  have him : z.im = v 1 := by simp [z]
  have hns : Complex.normSq z = 1 := by
    rw [Complex.normSq_apply, hre, him]
    linarith
  have hnorm : ‖z‖ = 1 := by
    have h : ‖z‖ ^ 2 = 1 := by rw [Complex.sq_norm]; exact hns
    nlinarith [norm_nonneg z]
  have hz : z ≠ 0 := by
    intro h; rw [h] at hns; norm_num at hns
  exact ⟨Complex.arg z, by rw [Complex.cos_arg hz, hnorm, hre, div_one],
    by rw [Complex.sin_arg, hnorm, him, div_one]⟩

end Work.Diff.Dim2
