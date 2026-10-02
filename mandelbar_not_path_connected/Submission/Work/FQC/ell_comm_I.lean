import Mathlib
import Submission.Work.FQC.Defs
import Submission.Work.FQC.saw_add_half

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FQC

/-- The real part of the MNS twist `ℓ_t` is the real part of the argument. -/
private theorem ell_re_aux (t : ℝ) (w : ℂ) : (ell t w).re = w.re := by
  simp only [ell, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- The imaginary part of the MNS twist `ℓ_t` is sheared by `t · saw w.re`. -/
private theorem ell_im_aux (t : ℝ) (w : ℂ) : (ell t w).im = w.im + t * saw w.re := by
  simp only [ell, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- `ℓ_t` commutes with the involution `ι w = star w + 1/2` of the Écalle cylinder. -/
theorem ell_comm_I (t : ℝ) (w : ℂ) :
    Work.FQC.ell t (star w + 1 / 2) = star (Work.FQC.ell t w) + 1 / 2 := by
  have hre : (star w + 1 / 2 : ℂ).re = w.re + 1 / 2 := by simp
  have hs : saw ((star w + 1 / 2 : ℂ).re) = -saw w.re := by rw [hre, saw_add_half]
  have him : (star w + 1 / 2 : ℂ).im = -w.im := by simp
  apply Complex.ext
  · rw [ell_re_aux, hre]
    show w.re + 1 / 2 = (star (ell t w) + 1 / 2).re
    rw [Complex.add_re, Complex.star_def, Complex.conj_re, ell_re_aux]
    simp
  · rw [ell_im_aux, hs, him]
    show -w.im + t * (-saw w.re) = (star (ell t w) + 1 / 2).im
    rw [Complex.add_im, Complex.star_def, Complex.conj_im, ell_im_aux]
    simp
    ring

end Work.FQC
