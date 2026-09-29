import Mathlib
import Submission.Work.A14.defs

namespace Work.A14D

/-- For `z = x + iy` with `y > 0`, `w(z) = z/(z-1)` has
`Im w = -y/‖z-1‖² < 0`.  The basic computation is
`z/(z-1) = z·conj(z-1)/‖z-1‖²` whose numerator `|z|² - z` has imaginary part `-y`. -/
theorem wC_im_neg {z : ℂ} (hz : 0 < z.im) : (wC z).im < 0 := by
  rw [wC, Complex.div_im]
  have h1 : (z - 1).im = z.im := by simp
  have h2 : (z - 1).re = z.re - 1 := by simp
  rw [h1, h2]
  have hN : 0 < Complex.normSq (z - 1) := by
    rw [Complex.normSq_pos]
    intro hc
    have : (z - 1).im = 0 := by rw [hc]; simp
    simp at this
    linarith
  have hnum : z.im * (z.re - 1) - z.re * z.im = -z.im := by ring
  rw [← sub_div, hnum]
  exact div_neg_of_neg_of_pos (by linarith) hN

end Work.A14D
