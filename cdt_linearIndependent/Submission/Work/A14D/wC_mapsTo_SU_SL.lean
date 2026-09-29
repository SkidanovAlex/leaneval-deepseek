import Mathlib
import Submission.Work.A14D.LC_A_defs

namespace Work.A14D

/-- The deck involution `w(z) = z/(z−1)` maps the upper half-plane `SU` into the lower `SL`.

If `z = a + bi` and `N = normSq (z − 1) = (a−1)² + b² > 0`, then
`w(z) = z/(z−1)` has `Im = −b/N` and `Re − 1 = (a−1)/N`, so
`w(z) ∈ SL` ("`Im < (Re − 1)/8`") is equivalent to `−8b < a − 1`, i.e. to
`(1−a)/8 < b`, which is `z ∈ SU`. -/
theorem wC_mapsTo_SU_SL : Set.MapsTo Work.A14D.wC Work.A14D.SU Work.A14D.SL := by
  intro z hz
  change (1 - z.re) / 8 < z.im at hz
  change (Work.A14D.wC z).im < ((Work.A14D.wC z).re - 1) / 8
  have hz1 : z - 1 ≠ 0 := by
    intro h
    have hz1' : z = 1 := sub_eq_zero.mp h
    rw [hz1'] at hz
    norm_num at hz
  rw [Work.A14D.wC, Complex.div_im, Complex.div_re, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, sub_zero]
  set N := Complex.normSq (z - 1) with hNdef
  have hN : 0 < N := by rw [hNdef]; exact Complex.normSq_pos.mpr hz1
  have hkey : -8 * z.im < z.re - 1 := by linarith
  conv_lhs => rw [← sub_div]
  conv_rhs => rw [← add_div]
  rw [div_sub_one (ne_of_gt hN), div_div, div_lt_div_iff₀ hN (by positivity)]
  rw [show (z.im * (z.re - 1) - z.re * z.im) * (N * 8)
        = ((z.im * (z.re - 1) - z.re * z.im) * 8) * N by ring]
  rw [mul_lt_mul_iff_of_pos_right hN]
  rw [hNdef, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    sub_zero]
  nlinarith [hkey]

end Work.A14D
