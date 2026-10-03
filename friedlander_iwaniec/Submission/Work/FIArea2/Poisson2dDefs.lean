/-
# Two-dimensional Poisson summation on a lattice coset: the vocabulary

*FI* §6 evaluates the lattice count (6.7)

  `C(z₁,z₂) = ∑_{c₁²z₂ ≡ c₂²z₁ (mod |Δ|)} f((c₁²z₂ − c₂²z₁)/Δ)`

by splitting the sum over `(c₁,c₂) ∈ ℤ²` into the residue classes modulo `m = |Δ|` and applying
**Poisson summation in two dimensions** to each class.  Mathlib has no two-dimensional Poisson
summation (it has the one-dimensional `Real.tsum_eq_tsum_fourier` and multivariate Fourier
inversion for Schwartz functions), so this file fixes the vocabulary for it: the coset lattice
point `cosetPt`, and the two Fourier integrals used by the statement —

* `ft2 φ h` — the two-dimensional Fourier transform at the integer frequency `h`,
* `ft2coset φ m γ h` — the same at the frequency `h/m` with the coset phase of the Poisson
  formula.

The statement to be proved (delegated as `Work.FIArea2.poisson_coset_2d`) is

  `∑' c, φ (cosetPt m γ c) = (m^2)⁻¹ · ∑' h, ft2coset φ m γ h`,

valid for `φ : ℝ × ℝ → ℂ` smooth of compact support (so that both sides converge absolutely and
the `'`-sums are the honest ones).  Its one-dimensional prototype is `Real.tsum_eq_tsum_fourier`.
-/
import Mathlib

set_option autoImplicit false

namespace Work.FIArea2

noncomputable section

open scoped BigOperators

/-- The point `(γ₁ + m c₁, γ₂ + m c₂)` of the coset `(γ₁,γ₂) + mℤ²` in `ℝ²`. -/
def cosetPt (m : ℕ) (γ c : ℤ × ℤ) : ℝ × ℝ :=
  ((γ.1 : ℝ) + (m : ℝ) * (c.1 : ℝ), (γ.2 : ℝ) + (m : ℝ) * (c.2 : ℝ))

/-- The two-dimensional Fourier transform of `φ` at the integer frequency `h`,
`𝓕φ(h) = ∫_{ℝ²} φ(t) e(−h·t) dt` with `e(x) = exp(2πix)`. -/
def ft2 (φ : ℝ × ℝ → ℂ) (h : ℤ × ℤ) : ℂ :=
  ∫ t : ℝ × ℝ, φ t *
    Complex.exp (-(2 * Real.pi * Complex.I) * ((h.1 : ℝ) * t.1 + (h.2 : ℝ) * t.2))

/-- The Fourier integral of the Poisson formula at the frequency `h/m` of the coset
`(γ₁,γ₂) + mℤ²`:  `∫_{ℝ²} φ(t) e(−h·(t−γ)/m) dt`. -/
def ft2coset (φ : ℝ × ℝ → ℂ) (m : ℕ) (γ h : ℤ × ℤ) : ℂ :=
  ∫ t : ℝ × ℝ, φ t *
    Complex.exp (-(2 * Real.pi * Complex.I)
      * (((h.1 : ℝ) * (t.1 - (γ.1 : ℝ)) + (h.2 : ℝ) * (t.2 - (γ.2 : ℝ))) / (m : ℝ)))

/-- The same at `γ = 0`, i.e. `∫ φ(t)e(−h·t/m)`. -/
def ft2scaled (φ : ℝ × ℝ → ℂ) (m : ℕ) (h : ℤ × ℤ) : ℂ := ft2coset φ m 0 h

end

end Work.FIArea2
