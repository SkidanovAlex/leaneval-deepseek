import Mathlib
import Submission.Work.Parab.leftCoord.coordError_sector

/-!
# The logarithmic shift bound `log (-z) - log (-(z+1)) + 1/z = O(1/‖z‖²)`

For `‖z‖ ≥ 2` with `z` off the real axis, the difference of the two principal logarithms
`log (-z) - log (-(z+1))` is `-log (1 + 1/z)`: indeed `-(z+1) = (-z) · (1 + 1/z)`, and since
`-z` and `-(z+1)` have the same (non-zero) imaginary part they lie strictly on the same side of
the branch cut, so `log` is multiplicative on this product
(`Work.Parab.leftCoord.log_mul_of_im_same`, applicable because `Re (1 + 1/z) ≥ 1/2 > 0`).

Hence the quantity in the statement equals `u - log (1 + u)` with `u = 1/z`, which is bounded by
`‖u‖²` through the Taylor remainder estimate `Complex.norm_log_one_add_sub_self_le` and
`‖u‖ ≤ 1/2`.  Since `‖u‖ = 1/‖z‖`, the claim follows.
-/

namespace Work.Parab.coordData

theorem log_shift_bound {z : ℂ} (hz : 2 ≤ ‖z‖) (him : z.im ≠ 0) :
    ‖Complex.log (-z) - Complex.log (-(z + 1)) + 1 / z‖ ≤ 1 / ‖z‖ ^ 2 := by
  have hz_ne : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; norm_num at hz
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
  set u : ℂ := 1 / z with hu
  -- `‖u‖ ≤ 1/2`
  have hnorm_u_eq : ‖u‖ = 1 / ‖z‖ := by rw [hu, norm_div, norm_one]
  have hnorm_u : ‖u‖ ≤ 1 / 2 := by
    rw [hnorm_u_eq]
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hz
  -- `1 + u` lies in the open right half plane
  have h1u_re : 0 < (1 + u).re := by
    have h1 : -‖u‖ ≤ u.re := (abs_le.mp (Complex.abs_re_le_norm u)).1
    have hre : (1 + u).re = 1 + u.re := by simp
    rw [hre]; linarith
  -- the algebraic identity `(-z) * (1 + u) = -(z + 1)`
  have hfact : (-z) * (1 + u) = -(z + 1) := by
    rw [hu]; field_simp
  -- `-z` and `-(z+1)` lie strictly on the same side of the real axis
  have hbranch : (0 < (-z).im ∧ 0 < ((-z) * (1 + u)).im) ∨
      (((-z).im < 0) ∧ ((-z) * (1 + u)).im < 0) := by
    rw [hfact]
    have h1 : (-z).im = -z.im := by simp
    have h2 : (-(z + 1)).im = -z.im := by simp
    rw [h1, h2]
    rcases lt_or_gt_of_ne him with h | h
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  -- therefore `log` is multiplicative and `log (-(z+1)) = log (-z) + log (1 + u)`
  have hlog : Complex.log (-(z + 1)) = Complex.log (-z) + Complex.log (1 + u) := by
    have h := Work.Parab.leftCoord.log_mul_of_im_same h1u_re hbranch
    rwa [hfact] at h
  -- the whole expression collapses to `u - log (1 + u)`
  have hmain : Complex.log (-z) - Complex.log (-(z + 1)) + 1 / z =
      u - Complex.log (1 + u) := by
    rw [hlog]; rw [hu]; ring
  rw [hmain]
  -- Taylor remainder estimate for `log` at `1`
  have hlogbound := Complex.norm_log_one_add_sub_self_le (z := u) (by linarith : ‖u‖ < 1)
  have hfrac : (1 - ‖u‖)⁻¹ / 2 ≤ 1 := by
    have h2 : (1 - ‖u‖)⁻¹ ≤ 2 := by
      have hpos : 0 < 1 - ‖u‖ := by linarith
      have := (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 1 / 2)).mpr
        (by linarith : (1 / 2 : ℝ) ≤ 1 - ‖u‖)
      simpa using this
    linarith
  calc ‖u - Complex.log (1 + u)‖
      = ‖Complex.log (1 + u) - u‖ := norm_sub_rev _ _
    _ ≤ ‖u‖ ^ 2 * (1 - ‖u‖)⁻¹ / 2 := hlogbound
    _ = ‖u‖ ^ 2 * ((1 - ‖u‖)⁻¹ / 2) := by ring
    _ ≤ ‖u‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left hfrac (sq_nonneg _)
    _ = ‖u‖ ^ 2 := by rw [mul_one]
    _ = 1 / ‖z‖ ^ 2 := by rw [hnorm_u_eq, div_pow, one_pow]

end Work.Parab.coordData
