import Mathlib
import Submission.CDTPlan.InterfacesC
import Submission.CDT.LogMIdentities
import Submission.CDT.SympDescent
import Submission.CDT.RatFuncDeriv

/-!
# Setup for `Work.CDcl.c_dclosed`

Shared notation for the proof that the `ℚ(y)`-span of the seventeen functions of CDT Theorem C
is closed under `d/dy`.

We work with `K = ℚ(x)` (`RatFunc ℚ`), the variable `xK`, the involution `φ : x ↦ x/(x-1)`
(`phiK`), the descent coordinate `y = x²/(x-1)` (`yK`) and the `y`-derivation multiplier
`ρ = dx/dy = (x-1)²/(x(x-2))` (`rhoK`).

The paper's order-two operator `M = P₂∂² + P₁∂ + P₀` and its φ-pullback `M^w` are encoded at the
level of rational functions; the inhomogeneity of `M(logP)` is `p`.
-/

noncomputable section

namespace Work.CDcl

open Polynomial

/-- `ℚ(x)`, the field of rational functions in `x` over `ℚ`. -/
abbrev K : Type := RatFunc ℚ

/-- the variable `x` -/
def xK : K := RatFunc.X

/-- the involution `φ(x) = x/(x-1)` -/
def phiK : K := xK / (xK - 1)

/-- the descent coordinate `y = x²/(x-1) = x·φ(x)` -/
def yK : K := xK ^ 2 / (xK - 1)

/-- `ρ = dx/dy = (x-1)²/(x(x-2))` -/
def rhoK : K := (xK - 1) ^ 2 / (xK * (xK - 2))

/-! ## The paper's ODE data as polynomials -/

/-- the quartic `Q₄ = 1 - 4abx + (4a²+4b²-2)x² - 4abx³ + x⁴` -/
def q4poly (a b : ℚ) : Polynomial ℚ :=
  1 - C (4 * a * b) * X + C (4 * a ^ 2 + 4 * b ^ 2 - 2) * X ^ 2 - C (4 * a * b) * X ^ 3 + X ^ 4

/-- `P₂ = (x-1)x(x+1)Q₄` -/
def p2poly (a b : ℚ) : Polynomial ℚ := (X - 1) * X * (X + 1) * q4poly a b

/-- `P₁` -/
def p1poly (a b : ℚ) : Polynomial ℚ :=
  -1 + C (8 * a * b) * X + C (5 - 12 * a ^ 2 - 12 * b ^ 2) * X ^ 2 + C (16 * a * b) * X ^ 3
    + C (4 * a ^ 2 + 4 * b ^ 2 - 7) * X ^ 4 - C (8 * a * b) * X ^ 5 + 3 * X ^ 6

/-- `P₀` -/
def p0poly (a b : ℚ) : Polynomial ℚ :=
  C (a * b) + C (1 - 3 * a ^ 2 - 3 * b ^ 2) * X + C (8 * a * b) * X ^ 2
    - C (a ^ 2 + b ^ 2 + 2) * X ^ 3 - C (a * b) * X ^ 4 + X ^ 5

/-- the inhomogeneity `p = r_a(-b+3ax-3bx²+ax³) + r_b(-a+3bx-3ax²+bx³) + r_ab(-1+2x²-x⁴)` -/
def ppoly (a b : ℚ) (ra rb rab r0 : ℤ) : Polynomial ℚ :=
  C ((ra : ℚ) * (-b) + (rb : ℚ) * (-a) + (rab : ℚ) * (-1))
    + C ((ra : ℚ) * (3 * a) + (rb : ℚ) * (3 * b)) * X
    + C ((ra : ℚ) * (-(3 * b)) + (rb : ℚ) * (-(3 * a)) + (rab : ℚ) * 2) * X ^ 2
    + C ((ra : ℚ) * a + (rb : ℚ) * b) * X ^ 3
    + C (-(rab : ℚ)) * X ^ 4

/-! ## The ODE data at the level of `K = ℚ(x)` -/

/-- `P₂(x)` as a rational function -/
def p2K (a b : ℚ) : K := (p2poly a b).eval₂ (algebraMap ℚ K) xK
/-- `P₁(x)` as a rational function -/
def p1K (a b : ℚ) : K := (p1poly a b).eval₂ (algebraMap ℚ K) xK
/-- `P₀(x)` as a rational function -/
def p0K (a b : ℚ) : K := (p0poly a b).eval₂ (algebraMap ℚ K) xK
/-- `p(x)` as a rational function -/
def pK (a b : ℚ) (ra rb rab r0 : ℤ) : K := (ppoly a b ra rb rab r0).eval₂ (algebraMap ℚ K) xK

/-- `α = -P₁/P₂` -/
def alphaK (a b : ℚ) : K := -p1K a b / p2K a b
/-- `β = -P₀/P₂` -/
def betaK (a b : ℚ) : K := -p0K a b / p2K a b
/-- `γ = p/P₂` -/
def gammaK (a b : ℚ) (ra rb rab r0 : ℤ) : K := pK a b ra rb rab r0 / p2K a b

/-- `P₂∘φ` -/
def p2phiK (a b : ℚ) : K := (p2poly a b).eval₂ (algebraMap ℚ K) phiK
/-- `P₁∘φ` -/
def p1phiK (a b : ℚ) : K := (p1poly a b).eval₂ (algebraMap ℚ K) phiK
/-- `P₀∘φ` -/
def p0phiK (a b : ℚ) : K := (p0poly a b).eval₂ (algebraMap ℚ K) phiK
/-- `p∘φ` -/
def pphiK (a b : ℚ) (ra rb rab r0 : ℤ) : K := (ppoly a b ra rb rab r0).eval₂ (algebraMap ℚ K) phiK

/-- the leading coefficient `Q₂ = (P₂∘φ)(φ'∘φ)² = (P₂∘φ)(x-1)⁴` of `M^w` -/
def Q2K (a b : ℚ) : K := p2phiK a b * (xK - 1) ^ 4
/-- `Q₁ = (P₂∘φ)(φ''∘φ) + (P₁∘φ)(φ'∘φ) = 2(P₂∘φ)(x-1)³ - (P₁∘φ)(x-1)²` -/
def Q1K (a b : ℚ) : K := p2phiK a b * (2 * (xK - 1) ^ 3) + p1phiK a b * (-(xK - 1) ^ 2)
/-- `Q₀ = P₀∘φ` -/
def Q0K (a b : ℚ) : K := p0phiK a b

/-! ## The series side: `G = Sym⁺P` and its pullbacks -/

/-- `G = Sym⁺(logP a b ra rb rab r0) = Submission.CDTPlan.GC m n ra rb rab r0` for `a = 2m+1`, `b = 2n+1`. -/
def G0 (a b : ℚ) (ra rb rab r0 : ℤ) : PowerSeries ℚ :=
  Submission.CDT.sympSym (Submission.CDT.logP a b ra rb rab r0)

/-- `T k = (G^{(k)})∘y`, the pullback of the `k`-th derivative of `G`. -/
def T (a b : ℚ) (ra rb rab r0 : ℤ) (k : ℕ) : PowerSeries ℚ :=
  ((PowerSeries.derivative (R := ℚ))^[k] (G0 a b ra rb rab r0)).subst Submission.CDT.sympY

/-- `α̃ = -Q₁/Q₂` -/
def alphaKt (a b : ℚ) : K := -Q1K a b / Q2K a b
/-- `β̃ = -Q₀/Q₂` -/
def betaKt (a b : ℚ) : K := -Q0K a b / Q2K a b
/-- `γ̃ = (p∘φ)/Q₂` -/
def gammaKt (a b : ℚ) (ra rb rab r0 : ℤ) : K := pphiK a b ra rb rab r0 / Q2K a b

end Work.CDcl
