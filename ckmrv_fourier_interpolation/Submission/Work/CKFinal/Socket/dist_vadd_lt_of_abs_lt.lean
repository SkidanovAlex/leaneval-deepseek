import Mathlib

namespace Work.CKFinal.Socket

open UpperHalfPlane Complex

/-- Real translation by `s` moves `u` by less than `ε` in the hyperbolic metric, provided
`|s| < ε * u.im`. -/
theorem dist_vadd_lt_of_abs_lt {u : UpperHalfPlane} {s ε : ℝ} (hε : 0 < ε)
    (hs : |s| < ε * u.im) : dist (s +ᵥ u) u < ε := by
  have hu : 0 < u.im := u.im_pos
  -- The complex distance between `s +ᵥ u` and `u` is `|s|`.
  have hdist_coe : dist (((s +ᵥ u : UpperHalfPlane)) : ℂ) (u : ℂ) = |s| := by
    rw [UpperHalfPlane.coe_vadd, dist_eq_norm, add_sub_cancel_right]
    simp
  -- The imaginary parts agree, so the normalising factor is `u.im`.
  have hsqrt : Real.sqrt ((s +ᵥ u : UpperHalfPlane).im * u.im) = u.im := by
    rw [UpperHalfPlane.vadd_im]
    rw [← sq]
    exact Real.sqrt_sq hu.le
  -- Hence `sinh (dist / 2) = |s| / (2 * u.im)`.
  have hsinh : Real.sinh (dist (s +ᵥ u) u / 2) = |s| / (2 * u.im) := by
    rw [UpperHalfPlane.sinh_half_dist, hdist_coe, hsqrt]
  -- And the latter is `< sinh (ε / 2)`, since `|s| < ε * u.im` and `ε / 2 < sinh (ε / 2)`.
  have hbound : |s| / (2 * u.im) < Real.sinh (ε / 2) := by
    have h2u : 0 < 2 * u.im := by positivity
    have h1 : |s| / (2 * u.im) < ε * u.im / (2 * u.im) :=
      div_lt_div_of_pos_right hs h2u
    have h2 : ε * u.im / (2 * u.im) = ε / 2 := by
      rw [mul_div_mul_right _ _ hu.ne']
    rw [h2] at h1
    have h3 : ε / 2 < Real.sinh (ε / 2) := Real.self_lt_sinh_iff.mpr (by linarith)
    linarith
  have hsinhlt : Real.sinh (dist (s +ᵥ u) u / 2) < Real.sinh (ε / 2) := by
    rw [hsinh]; exact hbound
  rw [Real.sinh_lt_sinh] at hsinhlt
  linarith

end Work.CKFinal.Socket
