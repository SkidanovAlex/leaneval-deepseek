import Mathlib
import Submission.Work.FIPlan.Interface

namespace Work.FIArea7.P231

/-- If the coordinates of a product `e * w` of Gaussian integers are coprime as integers,
then the coordinates of `w` are coprime. This holds because both coordinates of `e * w` are
integer combinations of `w.re` and `w.im`:
`(e*w).re = e.re * w.re - e.im * w.im` and `(e*w).im = e.re * w.im + e.im * w.re`. -/
theorem isCoprime_mul_factors {e w : GaussianInt}
    (h : IsCoprime (e * w).re (e * w).im) : IsCoprime w.re w.im := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨x * e.re + y * e.im, -x * e.im + y * e.re, ?_⟩
  rw [Zsqrtd.re_mul, Zsqrtd.im_mul] at hxy
  linear_combination hxy

end Work.FIArea7.P231
