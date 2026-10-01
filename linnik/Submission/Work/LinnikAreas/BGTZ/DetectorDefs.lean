/-
# The zero-detector of BGTZ, Proposition 5.1 — vocabulary

`Work.LinnikAreas.BGTZ.detector` (in `BGTZSetup`) is the smoothed sum

`S = Σ_{n ≤ N} a(n)χ(n)(Σ_{d | n} θ_d)² n^{-ρ}(1 - n/N)`.

This file fixes the two analytic objects that the proof of the detector bound
(`Work.LinnikAreas.BGTZ.DetectorMain`) manipulates:

* `detCoeff χ₁ χ θw n = a(n)χ(n)(Σ_{d | n}θ_d)²` — the Dirichlet coefficient of `S`,
  whose Dirichlet series is `L(s,χ)L(s,χχ₁)G(s,χ)` (BGTZ (4.2)–(4.5));
* `detJ χ₁ χ R θw N ρ` — the contour integral on the line `Re s = 1/2 - Re ρ`, which is
  what the shifted Mellin inversion of `S` produces besides the residue at `s = 1 - ρ`.

Both are used by the pieces of the detector proof (`DetectorSeries`, `DetectorMellin`,
`DetectorContour`, `DetectorJBound`).
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ

variable {q : ℕ} [NeZero q]

/-- The Dirichlet coefficient `a(n)χ(n)(Σ_{d | n}θ_d)²` of the BGTZ detector sum. -/
def detCoeff (χ₁ χ : DirichletCharacter ℂ q) (θw : ℕ → ℝ) (n : ℕ) : ℂ :=
  (aCoeff χ₁ n : ℂ) * (χ n) * (∑ d ∈ n.divisors, (θw d : ℂ)) ^ 2

/-- The vertical line of the shifted contour: `1/2 - Re ρ`. -/
def detLine (ρ : ℂ) : ℂ := ((1 / 2 - ρ.re : ℝ) : ℂ)

/-- The shifted contour integral `J` produced by Mellin inversion of the detector sum:
`(1/2π) ∫_ℝ L(s+ρ,χ)L(s+ρ,χχ₁)G(s+ρ,χ)N^s/(s(s+1)) dt` along `s = 1/2 - Re ρ + it`. -/
def detJ (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ) : ℂ :=
  (1 / (2 * Real.pi)) *
    ∫ t : ℝ, (DirichletCharacter.LFunction χ (ρ + detLine ρ + (t : ℂ) * I)
        * DirichletCharacter.LFunction (χ * χ₁) (ρ + detLine ρ + (t : ℂ) * I)
        * sieveG χ₁ R θw (ρ + detLine ρ + (t : ℂ) * I) χ
        * (N : ℂ) ^ (detLine ρ + (t : ℂ) * I))
      / ((detLine ρ + (t : ℂ) * I) * (detLine ρ + (t : ℂ) * I + 1))

/-- The residue term of the shifted contour, bounded by the Graham input.  In the two cases where
`F(s,χ) = L(s,χ)L(s,χχ₁)` has a pole at `s = 1` (i.e. `χ = 1` or `χ = χ₁`) the residue of the
detector integrand at `s = 1 - ρ` equals
`(Res_{s=1}L(s,χ₀)) · L(1,χ₁) · G(1,χ₀) · N^{1-ρ}/((1-ρ)(2-ρ))` with `G(1,χ₁) = G(1,χ₀)`
(as `χ₁(n)a(n) = a(n)`), and `Res_{s=1}L(s,χ₀) = φ(q)/q`.  Hence it is bounded in modulus by
`‖L(1,χ₁)‖ · (φ(q)/q) · ‖G(1,χ₀)‖ · N^{1-Re ρ}/‖(1-ρ)(2-ρ)‖`: this is the factor `φ(q)/q`
that cancels the `q/φ(q)` of Graham's bound. -/
def detResBound (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ) : ℝ :=
  ‖DirichletCharacter.LFunction χ₁ 1‖ * ((q.totient : ℝ) / (q : ℝ))
    * ‖sieveG χ₁ R θw 1 (1 : DirichletCharacter ℂ q)‖
    * ((N : ℝ) ^ (1 - ρ.re)) / ‖(1 - ρ) * (2 - ρ)‖

end Work.LinnikAreas.BGTZ
