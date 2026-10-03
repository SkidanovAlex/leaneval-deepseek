/-
# `Work.FIArea6Hecke.CGD.EkernSwap`

The symmetry of the additive-character kernel `ekern M (M * star x) y` in `x` and `y`.

Since `ekern M w s = e^{2πi · gdot s w / N}`, the point is the integral identity

`gdot y (M * star x) = gdot x (M * star y)`,

which is `Re(y · conj(M · conj x)) = Re(x · conj(M · conj y))`, i.e. `Re(y · conj M · x)`
on both sides.  No hypothesis on `M` (in particular `M ≠ 0`) is needed.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.ConductorGaussSumDefs

set_option autoImplicit false

namespace Work.FIArea6Hecke.CGD

open scoped BigOperators

/-- The bilinear form `gdot` is transparently symmetric under the swap `(x, y) ↦ (y, x)` combined
with conjugating the *other* argument: `gdot y (M * star x) = gdot x (M * star y)`. -/
lemma gdot_mul_star_swap (M x y : GaussianInt) :
    Work.FIArea6Hecke.R.gdot y (M * star x) = Work.FIArea6Hecke.R.gdot x (M * star y) := by
  simp only [Work.FIArea6Hecke.R.gdot, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_star,
    Zsqrtd.im_star]
  ring

theorem EkernSwap (M x y : GaussianInt) :
    Work.FIArea6Hecke.R.ekern M (M * star x) y = Work.FIArea6Hecke.R.ekern M (M * star y) x := by
  rw [Work.FIArea6Hecke.R.ekern, Work.FIArea6Hecke.R.ekern, gdot_mul_star_swap]

end Work.FIArea6Hecke.CGD
