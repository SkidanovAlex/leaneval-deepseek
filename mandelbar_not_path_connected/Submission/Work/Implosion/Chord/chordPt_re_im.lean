import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Geometry
import Submission.Work.Implosion.Geometry.normalForm_cutPt_re
import Submission.Work.Implosion.Chord

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The explicit chord formula in the "ideal" case `a = iλ`

In the geometrically natural case `a = i·λ` (`λ : ℝ`) and `h` **real-valued on the
cut** `ℓ`, the chord of the fundamental domain joining `t·a ∈ ℓ` to
`f(t·a) ∈ f(ℓ)` is the horizontal segment

  `chordPt a h t s = s·λ²(1−t²)·h(t·a) + i·t·λ`.

Here we record the two coordinate formulas: the real part is
`s·λ²(1−t²)·Re h(t·a)` (this is `Geometry.normalForm_cutPt_re`) and the imaginary
part is `t·λ` (the height is constant along the chord), the latter using that
`Im h(t·a) = 0`.
-/

namespace Work.Implosion.Chord

open Complex

/-- Real part of the chord as a convex combination of the real parts of its two
end points. -/
theorem chordPt_re_eq (a : ℂ) (h : ℂ → ℂ) (t s : ℝ) :
    (chordPt a h t s).re
      = (1 - s) * (cutPt a t).re + s * (normalForm a h (cutPt a t)).re := by
  simp [chordPt]

/-- Imaginary part of the chord as a convex combination of the imaginary parts of
its two end points. -/
theorem chordPt_im_eq (a : ℂ) (h : ℂ → ℂ) (t s : ℝ) :
    (chordPt a h t s).im
      = (1 - s) * (cutPt a t).im + s * (normalForm a h (cutPt a t)).im := by
  simp [chordPt]

/-- For `a = iλ` the cut point `t·a` is purely imaginary. -/
theorem cutPt_mul_I_re (lam t : ℝ) : (cutPt ((lam : ℂ) * I) t).re = 0 := by
  rw [Geometry.cutPt_mul_I]; simp

/-- The height of the cut point `t·a`, `a = iλ`. -/
theorem cutPt_mul_I_im (lam t : ℝ) : (cutPt ((lam : ℂ) * I) t).im = t * lam := by
  rw [Geometry.cutPt_mul_I]; simp

/-- Imaginary part of the normal form at a cut point, `a = iλ`:
`Im f(t·a) = t·λ + λ²(1−t²)·Im h(t·a)`. -/
theorem normalForm_cutPt_im (lam : ℝ) (h : ℂ → ℂ) (t : ℝ) :
    (normalForm ((lam : ℂ) * I) h (cutPt ((lam : ℂ) * I) t)).im
      = t * lam + lam ^ 2 * (1 - t ^ 2) * (h (cutPt ((lam : ℂ) * I) t)).im := by
  rw [normalForm_apply_cutPt, Geometry.cutPt_quad_factor, Geometry.cutPt_mul_I]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero]
  ring

theorem chordPt_re_im (lam : ℝ) (h : ℂ → ℂ) (t s : ℝ)
    (hreal : (h (cutPt ((lam : ℂ) * I) t)).im = 0) :
    (chordPt ((lam : ℂ) * I) h t s).re
        = s * lam ^ 2 * (1 - t ^ 2) * (h (cutPt ((lam : ℂ) * I) t)).re
      ∧ (chordPt ((lam : ℂ) * I) h t s).im = t * lam := by
  have hnf := Geometry.normalForm_cutPt_re lam h t
  have hnfim := normalForm_cutPt_im lam h t
  rw [hreal, mul_zero, add_zero] at hnfim
  constructor
  · rw [chordPt_re_eq, cutPt_mul_I_re, hnf]
    ring
  · rw [chordPt_im_eq, cutPt_mul_I_im, hnfim]
    ring

end Work.Implosion.Chord
