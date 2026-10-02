import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Complex

namespace Work.Implosion.Ecalle

/-- The imaginary part of the Écalle coordinate of the cut `ℓ = [−a,a]` for the
parameter `a = iλ` (`λ > 0`): the cut is the vertical line `Re u = π/(2λ)`, and
the imaginary part (the *Écalle height* of `t·a`) is
`−log((1+t)/(1−t))/(2λ)`.

This complements `ecalCoord_cutPt_re`, which computes the real part. -/
theorem ecalCoord_cutPt_im (lam : ℝ) (hlam : 0 < lam) (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    (ecalCoord ((lam : ℂ) * I) (cutPt ((lam : ℂ) * I) t)).im
      = -(Real.log ((1 + t) / (1 - t))) / (2 * lam) := by
  have ha : (lam : ℂ) * I ≠ 0 := by
    simp [Complex.I_ne_zero, ne_of_gt hlam]
  rw [ecalCoord_cutPt ((lam : ℂ) * I) t ha ht]
  have hD : 2 * ((lam : ℂ) * I) = ((2 * lam : ℝ) : ℂ) * I := by push_cast; ring
  rw [hD, Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.normSq_apply]
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  field_simp
  ring

end Work.Implosion.Ecalle
