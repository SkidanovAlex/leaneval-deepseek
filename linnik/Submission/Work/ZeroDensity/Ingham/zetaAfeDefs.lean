import Mathlib
import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Vocabulary for the smoothed approximate functional equation for `ζ`

This module collects the definitions used in the proof of
`Work.ZeroDensity.Ingham.zetaAfeTruncation` (the truncated approximate functional
equation for `ζ` on the critical line).

* `zetaSmooth K` — the Gaussian smoothing `u ↦ exp(K²u²)` in the Mellin variable, of
  width `1/K` (it decays like `exp(-K² y²)` on vertical lines `Re u = const`, and grows
  like `exp(K² x²)` along the real axis: the sign is chosen so that the defining contour
  integral of the weight below converges).
* `zetaAfeWeight K z x` — the archimedean weight
  `W_z(x) = (1/2πi) ∫_{Re u = 1} x^{-u} (Γℝ(z+u)/Γℝ(z)) exp(K²u²) du/u`;
  this is the Mellin inverse `mellinInv 1` of the kernel.  CAUTION: this weight is *not* a
  bounded smoothed indicator of `x < √(|z|/2π)`: on the line `Re u = 1` the factor
  `Γℝ(z+u)/Γℝ(z)` grows like `exp(π|Im u|/4)`, which the Gaussian only overcomes for
  `|Im u| ≳ 1/K²`; for `K = T^{-1/4}` the weight therefore grows like `exp(c√T)` despite a
  very narrow transition.  (Cf. the refuted statement `Work.ZeroDensity.Ingham.weightProfile`.)
  The weight is still genuinely useful through the *exact* smoothed approximate functional
  equation `Work.ZeroDensity.Ingham.smoothedAFE`.
* `zetaAfeMain K z X`, `zetaAfeDual K z Y` — the two smoothed Dirichlet sums of the
  approximate functional equation.
* `zetaChi z` — the ratio `Γℝ(1-z)/Γℝ(z)`, the root-number factor of the functional
  equation `Λ(s) = Λ(1-s)`, of modulus one on the critical line.

Nothing here is proved; the statements live in the sibling modules.
-/

open Complex MeasureTheory Set
open scoped Topology BigOperators Real

noncomputable section

namespace Work.ZeroDensity.Ingham

/-- The Gaussian smoothing of the approximate functional equation, of width `1/K`. -/
def zetaSmooth (K : ℝ) (u : ℂ) : ℂ := cexp ((K : ℂ) ^ 2 * u ^ 2)

/-- The archimedean weight of the approximate functional equation for `ζ`. -/
def zetaAfeWeight (K : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  mellinInv 1 (fun u : ℂ => (Gammaℝ (z + u) / Gammaℝ z) * zetaSmooth K u / u) x

/-- The smoothed main sum `Σ_{n ≥ 1} n^{-z} W_z(n/X)`. -/
def zetaAfeMain (K : ℝ) (z : ℂ) (X : ℝ) : ℂ :=
  ∑' n : ℕ, (n : ℂ) ^ (-z) * zetaAfeWeight K z ((n : ℝ) / X)

/-- The smoothed dual sum `Σ_{n ≥ 1} n^{z-1} W_{1-z}(n/Y)`. -/
def zetaAfeDual (K : ℝ) (z : ℂ) (Y : ℝ) : ℂ :=
  ∑' n : ℕ, (n : ℂ) ^ (z - 1) * zetaAfeWeight K (1 - z) ((n : ℝ) / Y)

/-- The root-number factor `Γℝ(1-z)/Γℝ(z)` of the functional equation `Λ(s) = Λ(1-s)`. -/
def zetaChi (z : ℂ) : ℂ := Gammaℝ (1 - z) / Gammaℝ z

@[simp] lemma zetaSmooth_apply (K : ℝ) (u : ℂ) :
    zetaSmooth K u = cexp ((K : ℂ) ^ 2 * u ^ 2) := rfl

@[simp] lemma zetaAfeWeight_apply (K : ℝ) (z : ℂ) (x : ℝ) :
    zetaAfeWeight K z x =
      mellinInv 1 (fun u : ℂ => (Gammaℝ (z + u) / Gammaℝ z) * zetaSmooth K u / u) x := rfl

/-- The smoothing is even in `u`. -/
lemma zetaSmooth_neg (K : ℝ) (u : ℂ) : zetaSmooth K (-u) = zetaSmooth K u := by
  simp [zetaSmooth, sq]

/-- The smoothing takes the value `1` at `u = 0`. -/
@[simp] lemma zetaSmooth_zero (K : ℝ) : zetaSmooth K 0 = 1 := by simp [zetaSmooth]

/-- Explicit modulus of the smoothing on a vertical line:
`‖exp(K²u²)‖ = exp(K²((Re u)² - (Im u)²))`. -/
lemma norm_zetaSmooth (K : ℝ) (u : ℂ) :
    ‖zetaSmooth K u‖ = Real.exp (K ^ 2 * (u.re ^ 2 - u.im ^ 2)) := by
  rw [zetaSmooth, Complex.norm_exp]
  congr 1
  have h2 : (u ^ 2).re = u.re ^ 2 - u.im ^ 2 := by
    rw [pow_two, Complex.mul_re]; ring
  have hK2 : (((K : ℂ) ^ 2)).re = K ^ 2 := by
    rw [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hK2im : (((K : ℂ) ^ 2)).im = 0 := by
    rw [pow_two, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  rw [Complex.mul_re, h2, hK2, hK2im, zero_mul, sub_zero]

end Work.ZeroDensity.Ingham
