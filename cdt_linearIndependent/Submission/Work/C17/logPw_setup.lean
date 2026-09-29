import Mathlib
import Submission.Work.C17.seventeen_defs

/-!
# Definitions for `Work.C17.logPw_continuation` (area C17, X1)

The lemma `Work.C17.logPw_continuation` continues the function
`z ↦ Pfun a b ra rb rab r0 (z / (z - 1))` from the lens
`{z : ‖z / (z - 1)‖ < xs a b}` (where the unlikely series converges) to a convex open
"stadium" `S` joining a small disc around the cusp `x_s = xs a b` to the point
`p₀ = 1/4 + i/5`, and contained in the unit disc.

The continuation is produced as a solution of the *pullback* of the paper's order-two
operator `M = P2x·D² + P1x·D + P0x` along `w(z) = z/(z-1)`, so this file collects

* `p0C`, `stadiumSet c δ ρ`, `wfun` — the geometry;
* `QtilC`, `pi2C`, `pi1C`, `pi0C`, `rhoTil` — the pullbacks of `Q4x`, `P2x`, `P1x`,
  `P0x` and `rhoMx` to the `z`-plane, obtained by clearing the powers of `(z-1)`;
* `odeP`, `odeQ`, `odeR` — the normalized coefficients of the pullback equation
  `u'' + odeP·u' + odeQ·u = odeR`.
-/

namespace Work.C17

open Polynomial
open scoped BigOperators

noncomputable section

/-- The point `p₀ = 1/4 + i/5` of the statement of `logPw_continuation`. -/
def p0C : ℂ := (1 / 4 : ℂ) + Complex.I / 5

/-- The involution `w(z) = z/(z-1)` of the statement (`‖w z‖ = ‖z/(z-1)‖`). -/
def wfun (z : ℂ) : ℂ := z / (z - 1)

/-- The lens on which the composition `Pfun ∘ w` is given by the convergent unlikely
series: the open disc `{z | z ≠ 1 ∧ ‖w z‖ < c}`.  It is defined as an explicit ball (the
Apollonius disc of the condition `‖z/(z-1)‖ < c`) so that convexity and openness are
immediate; `Work.C17.lensSet_props` identifies it with `{z | z ≠ 1 ∧ ‖w z‖ < c}`
(without the `z ≠ 1` clause the set would contain the spurious point `1`, where
`wfun 1 = 1/0 = 0`). -/
def lensSet (c : ℝ) : Set ℂ :=
  Metric.ball ((-(c ^ 2 / (1 - c ^ 2)) : ℝ) : ℂ) (c / (1 - c ^ 2))

/-- The **stadium** joining a disc of radius `δ` around `c` to a disc of radius `ρ`
around `p₀`: the union of the discs `ball ((1-t)c + t·p₀) ((1-t)δ + tρ)`, which is
`conv (ball c δ ∪ ball p₀ ρ)`. -/
def stadiumSet (c δ ρ : ℝ) : Set ℂ :=
  {z : ℂ | ∃ t ∈ Set.Icc (0 : ℝ) 1,
    z ∈ Metric.ball (((((1 - t) * c : ℝ)) : ℂ) + (t : ℂ) * p0C) ((1 - t) * δ + t * ρ)}

/-- `(z-1)^4 · Q4x(z/(z-1))`, the pullback of the quartic whose roots are the four
cusp values `(a ± √(a²−1))(b ± √(b²−1))`. -/
def QtilC (a b : ℚ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range 5, C (((Q4x a b).coeff k : ℚ) : ℂ) * X ^ k * (X - 1) ^ (4 - k)

/-- `(z-1)^7 · P2x(z/(z-1)) = z·(2z−1)·Q̃(z)`, the pullback of the leading coefficient
`P2x = (X−1)X(X+1)Q4x`. -/
def pi2C (a b : ℚ) : Polynomial ℂ := X * (2 * X - 1) * QtilC a b

/-- `(z-1)^6 · P1x(z/(z-1))`, the pullback of `P1x`. -/
def pi1C (a b : ℚ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range 7, C (((P1x a b).coeff k : ℚ) : ℂ) * X ^ k * (X - 1) ^ (6 - k)

/-- `(z-1)^5 · P0x(z/(z-1))`, the pullback of `P0x`. -/
def pi0C (a b : ℚ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range 6, C (((P0x a b).coeff k : ℚ) : ℂ) * X ^ k * (X - 1) ^ (5 - k)

/-- `(z-1)^4 · rhoMx(z/(z-1))`, the pullback of the inhomogeneity `rhoMx`. -/
def rhoTil (a b : ℚ) (ra rb rab : ℤ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range 5, C (((rhoMx a b ra rb rab).coeff k : ℚ) : ℂ) * X ^ k * (X - 1) ^ (4 - k)

/-- The `u'`-coefficient of the pullback equation
`u'' + odeP·u' + odeQ·u = odeR`, namely `(2π₂ − π₁)/(π₂·(z−1))`. -/
def odeP (a b : ℚ) (z : ℂ) : ℂ :=
  (2 * (pi2C a b).eval z - (pi1C a b).eval z) / ((pi2C a b).eval z * (z - 1))

/-- The `u`-coefficient of the pullback equation, namely `π₀/(π₂·(z−1)²)`. -/
def odeQ (a b : ℚ) (z : ℂ) : ℂ :=
  (pi0C a b).eval z / ((pi2C a b).eval z * (z - 1) ^ 2)

/-- The inhomogeneity of the pullback equation, namely `ρ̃/(π₂·(z−1))`. -/
def odeR (a b : ℚ) (ra rb rab : ℤ) (z : ℂ) : ℂ :=
  (rhoTil a b ra rb rab).eval z / ((pi2C a b).eval z * (z - 1))

end

end Work.C17
