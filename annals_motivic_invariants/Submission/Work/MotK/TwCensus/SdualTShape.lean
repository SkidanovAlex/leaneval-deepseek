import Mathlib
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.MotV.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sdualT` — the explicit shape of the target ruling divisor (neutral module)

This module holds the *elementary structural facts* about the chart restriction

`Work.MotK.TGen.sdualT a b h = kleinTwSDualV a b h (chart3 K)`

of the target-side dual secant quintic of the T-twisted Crauder--Katz link:

* `sdualT_explicit` — the twelve-term shape of `sdualT a b h`, i.e. its four weight pieces for
  `wt x₀ = 3`, `wt x₁ = 2`, `wt x₂ = 1` (whose `h`-degrees satisfy `5·(h-degree) = 5 + wt`);
* `sdualT_scale_ab` — homogeneity in `(a,b)`: `sdualT (μa) (μb) h = μ^10 · sdualT a b h`;
* `sdG5` — the degree-five part of `sdualT a b 1`;
* `sdualT_one_eq_structural` — the common-factor decomposition of `sdualT a b 1`.

They are used by the irreducibility cluster (`TGen/SdG5hDefs.lean`,
`TwCensus/SdualTOneIrreducible.lean`, `TwCensus/SdG5*.lean`, ...), which imports *this* module, so
that the target theorem `Work.MotK.TwCensus.SdualTPrimeGood` can live in
`TwCensus/SdualTPrimeGood.lean` (which imports the cluster) without an import cycle.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.MotK.TwCensus

open MvPolynomial

variable {K : Type} [Field K]

/-! ## §0 The chart values -/

private lemma chart3_0 : Work.MotK.chart3 K 0 = 0 := rfl
private lemma chart3_1 : Work.MotK.chart3 K 1 = MvPolynomial.X 0 := rfl
private lemma chart3_2 : Work.MotK.chart3 K 2 = MvPolynomial.X 1 := rfl
private lemma chart3_3 : Work.MotK.chart3 K 3 = MvPolynomial.X 2 := rfl
private lemma chart3_4 : Work.MotK.chart3 K 4 = 1 := rfl

/-! ## §1 The explicit shape of `sdualT` -/

/-- **The twelve-term shape of the target ruling divisor**, written in the atoms
`C a, C b, C h, X 0, X 1, X 2` with every coefficient expanded as a polynomial in `C a, C b, C h`
(so that the identity is a polynomial identity in six atoms, checked by `ring`):

```
sdualT a b h = -a⁵b⁵h⁴x₀⁵ - a⁵b⁵h³x₁⁵ - a⁵b⁵h²x₂⁵ - a⁵b⁵h
             + h³(2a³b⁷+a⁸b²) x₀³x₂ + h²(2a³b⁷+a⁸b²) x₀x₁
             - h³(3a⁶b⁴+ab⁹) x₀²x₁² - h²(3a⁶b⁴+ab⁹) x₀x₂²
             + h³(3a⁴b⁶-a⁹b) x₀²x₁x₂² + h²(3a⁴b⁶-a⁹b) x₁²x₂
             + h³(2a⁷b³-a²b⁸) x₀x₁³x₂ + h²(2a⁷b³-a²b⁸) x₁x₂³
```

The `x`-weights `(3,2,1)` split this into the four pieces of weights `15, 10, 5, 0` with
`h`-degrees `4, 3, 2, 1`; equivalently every monomial satisfies `5·(h-degree) = 5 + weight`,
which is `sdualT_scale`. -/
theorem sdualT_explicit (a b h : K) :
    Work.MotK.TGen.sdualT a b h =
      -((C a) ^(5:ℕ) * (C b) ^(5:ℕ) * (C h) ^(4:ℕ) * (X 0) ^(5:ℕ))
      - ((C a) ^(5:ℕ) * (C b) ^(5:ℕ) * (C h) ^(3:ℕ) * (X 1) ^(5:ℕ))
      - ((C a) ^(5:ℕ) * (C b) ^(5:ℕ) * (C h) ^(2:ℕ) * (X 2) ^(5:ℕ))
      - ((C a) ^(5:ℕ) * (C b) ^(5:ℕ) * (C h))
      + ((C h) ^(3:ℕ) * (2 * (C a) ^(3:ℕ) * (C b) ^(7:ℕ) + (C a) ^(8:ℕ) * (C b) ^(2:ℕ))) * (X 0) ^(3:ℕ) * X 2
      + ((C h) ^(2:ℕ) * (2 * (C a) ^(3:ℕ) * (C b) ^(7:ℕ) + (C a) ^(8:ℕ) * (C b) ^(2:ℕ))) * X 0 * X 1
      - ((C h) ^(3:ℕ) * (3 * (C a) ^(6:ℕ) * (C b) ^(4:ℕ) + (C a) * (C b) ^(9:ℕ))) * (X 0) ^(2:ℕ) * (X 1) ^(2:ℕ)
      - ((C h) ^(2:ℕ) * (3 * (C a) ^(6:ℕ) * (C b) ^(4:ℕ) + (C a) * (C b) ^(9:ℕ))) * X 0 * (X 2) ^(2:ℕ)
      + ((C h) ^(3:ℕ) * (3 * (C a) ^(4:ℕ) * (C b) ^(6:ℕ) - (C a) ^(9:ℕ) * (C b))) * (X 0) ^(2:ℕ) * X 1 * (X 2) ^(2:ℕ)
      + ((C h) ^(2:ℕ) * (3 * (C a) ^(4:ℕ) * (C b) ^(6:ℕ) - (C a) ^(9:ℕ) * (C b))) * (X 1) ^(2:ℕ) * X 2
      + ((C h) ^(3:ℕ) * (2 * (C a) ^(7:ℕ) * (C b) ^(3:ℕ) - (C a) ^(2:ℕ) * (C b) ^(8:ℕ))) * X 0 * (X 1) ^(3:ℕ) * X 2
      + ((C h) ^(2:ℕ) * (2 * (C a) ^(7:ℕ) * (C b) ^(3:ℕ) - (C a) ^(2:ℕ) * (C b) ^(8:ℕ))) * X 1 * (X 2) ^(3:ℕ) := by
  rw [Work.MotK.TGen.sdualT, Work.MotK.kleinTwSDualV, chart3_0, chart3_1, chart3_2, chart3_3,
    chart3_4]
  first | refl_ring1 | ring

/-! ## §2 The two scalings -/

/-- **Homogeneity in `(a,b)`**: the `a`-degree plus the `b`-degree of every monomial of
`sdualT a b h` is `10`, so `(a,b) ↦ (μa, μb)` scales the polynomial by `μ^10`.  In particular
irreducibility of `sdualT a b h` depends only on the ratio `b/a`. -/
theorem sdualT_scale_ab (a b h μ : K) :
    Work.MotK.TGen.sdualT (μ * a) (μ * b) h
      = (C μ) ^(10:ℕ) * Work.MotK.TGen.sdualT a b h := by
  rw [sdualT_explicit (μ * a) (μ * b) h, sdualT_explicit a b h]
  simp only [C_mul, C_pow]
  first | refl_ring1 | ring

/-! **Weighted scaling in `(h, x₀, x₁, x₂)`**: for `wt h = -5`, `wt x₀ = 3`, `wt x₁ = 2`,
`wt x₂ = 1` the polynomial `sdualT` is homogeneous of weight `-5`.  Written as the
`MvPolynomial.aeval` *substitution* of the variables (`X 0 ↦ C (t^3) * X 0`, `X 1 ↦ C (t^2) * X 1`,
`X 2 ↦ C t * X 2`) the identity is

`t^5 · (sdualT a b h) (t³x₀, t²x₁, t x₂) = sdualT a b (t⁵h)`.

Hence only the Kummer class of `h` matters: if `t⁵ = h` then irreducibility of `sdualT a b h` over
a field containing `t` is equivalent to irreducibility of `sdualT a b 1`; over `K` itself
reducibility additionally requires `h ∈ K^{×5}`. -/
-- NOTE (area owner, 2026-10-04, kept): the weighted scaling is
--   `(C t)^5 * MvPolynomial.aeval (fun i => ![C (t^3)*X 0, C (t^2)*X 1, C t*X 2] i)
--      (sdualT a b h) = sdualT a b (t^5 * h)`
-- Its proof by `rw [sdualT_explicit, sdualT_explicit]` gets stuck on the `aeval`-images of the
-- *numerals* (`aeval f 2`), so it needs `map_natCast`/`map_ofNat` in the simp set; it was left
-- unproved rather than carrying a non-compiling declaration in the census closure.

/-! ## §3 The key structural decomposition of `sdualT a b 1`

Grouping the twelve monomials of `sdualT_explicit` at `h = 1` by their *common factors*, the
four "off-diagonal" patterns factor through the two quadrics `x₀²x₂ + x₁` and `x₀x₁² + x₂²`:

`sdualT a b 1 = c₀·(x₀⁵+x₁⁵+x₂⁵+1) + (c₁x₀ + c₃x₁x₂)(x₀²x₂+x₁) + (c₂x₀ + c₄x₁x₂)(x₀x₁²+x₂²)`

with `c₀ = -a⁵b⁵`, `c₁ = 2a³b⁷+a⁸b²`, `c₂ = -(3a⁶b⁴+ab⁹)`, `c₃ = 3a⁴b⁶-a⁹b`,
`c₄ = 2a⁷b³-a²b⁸`.  This is the form in which the irreducibility proof should proceed, via the
*total-degree* argument: the degree-five part of the right-hand side is the homogeneous quintic

`G₅ = c₀(x₀⁵+x₁⁵+x₂⁵) + c₃x₀²x₁x₂² + c₄x₀x₁³x₂`,

and for *any* `f` with top-degree part `T` one has `Irreducible T → Irreducible f`: from
`f = g·h`, the top-degree parts multiply, `T = (top g)(top h)`, and an irreducible homogeneous
`T` forces `top g` or `top h` to be a unit, hence `g` or `h` to be a constant.  So it suffices to
show `G₅` irreducible; `G₅` is a *five-term homogeneous ternary quintic*, and
`factor` over `ℚ(B)` (PARI) returns it irreducible for `B = 2, 3, 5, 7`, while in the degenerate
case it factors into five linear forms — so `G₅` carries the whole discriminant condition.
The weight argument (`wt x₀ = 3, wt x₁ = 2, wt x₂ = 1`) constrains a factorization
`G₅ = g·h` to have `deg g = deg h` in the `x₀`- and `x₂`-degrees as well: the highest-weight
monomial of `G₅` is `c₀x₀⁵` and the lowest is `c₀x₂⁵`, so `(top g)(top h) = c₀x₀⁵` and
`(low g)(low h) = c₀x₂⁵` force `top g = αx₀^{d}`, `low g = βx₂^{d}` with `d = deg g`; the only
remaining cases are `d = 1` (linear × quartic) and `d = 2` (quadratic × cubic). -/

/-- **The degree-five part `G₅` of `sdualT a b 1`**: the homogeneous quintic which carries the
whole discriminant condition.  Weight argument (`wt x₀ = 3`, `wt x₁ = 2`, `wt x₂ = 1`): the
highest-weight monomial of `G₅` is `-a⁵b⁵x₀⁵` and its lowest is `-a⁵b⁵x₂⁵`, so a non-trivial
factorisation `G₅ = F·H` (both homogeneous) has `top F = αx₀^d` and `low F = βx₂^d` with
`d = deg F ∈ {1,2}` (the middle coefficients of `F` are *not* constrained, so `F` need not be
diagonal — an earlier claim of mine that it is was wrong, see below).

* `d = 1`, i.e. a linear factor, forces `Δ := a^10 - 11a^5b^5 - b^10 = 0`:
  `Work.MotK.TwCensus.SdG5LinearFactorDisc` (delegated; independently verified: the elimination
  ideal of the six coefficient equations in `B = b/a` is `⟨B^10 + 11B^5 - 1⟩`, and the derivation
  is `β⁵ = γ⁵ = 1`, `B⁵ + 5γβ³B² = 2`, `3B⁵ + 5γ²βB⁴ = 1` (after normalising `α = 1`) ⟹
  `Δ = -25(γ²βB⁴ - 3γβ³B² + 1) = 0`).
* `d = 2` is **still open**: the diagonal-quadratic statement is true
  (`(MvPolynomial.C α * X 0 ^ 2 + C δ * X 1 ^ 2 + C ζ * X 2 ^ 2) ∣ sdG5 a b` is impossible for
  `α ≠ 0`), but a *general* quadratic factor is not excluded by it, and quadratic factors do exist
  when `Δ = 0` (products of two of the five lines of the pentagon).  The correct target is:
  **every non-trivial factorisation of `G₅` has a factor of degree 1** — equivalently
  `G₅` irreducible for `Δ ≠ 0`.  For `d = 2` one must use the middle coefficients
  `βx₀x₁ + γx₀x₂ + δx₁² + εx₁x₂` of `F` together with the weight decomposition
  `G₅ = -a⁵b⁵x₀⁵ + (-a⁵b⁵x₁⁵ + (3a⁴b⁶-a⁹b)x₀²x₁x₂² + (2a⁷b³-a²b⁸)x₀x₁³x₂) - a⁵b⁵x₂⁵`
  of `G₅` (three weight pieces) and the analogous pieces of `H`.  The `d = 1` case above is the
  half of the argument that is settled. -/
noncomputable def sdG5 (a b : K) : MvPolynomial (Fin 3) K :=
  -((C a) ^(5:ℕ) * (C b) ^(5:ℕ)) * ((X 0) ^(5:ℕ) + (X 1) ^(5:ℕ) + (X 2) ^(5:ℕ))
    + (3 * (C a) ^(4:ℕ) * (C b) ^(6:ℕ) - (C a) ^(9:ℕ) * (C b)) * (X 0) ^(2:ℕ) * X 1 * (X 2) ^(2:ℕ)
    + (2 * (C a) ^(7:ℕ) * (C b) ^(3:ℕ) - (C a) ^(2:ℕ) * (C b) ^(8:ℕ)) * X 0 * (X 1) ^(3:ℕ) * X 2

/-- **The common-factor decomposition of `sdualT a b 1`**: the four off-diagonal monomial patterns
factor through the quadrics `x₀²x₂ + x₁` and `x₀x₁² + x₂²`, and all twelve coefficients match the
`h = 1` instance of `sdualT_explicit` term by term.

Warning on signs (two rounds of errors were made on exactly this point): the third factor is
`((2a⁷b³-a²b⁸)x₁x₂ - (3a⁶b⁴+ab⁹)x₀)`, i.e. the `x₁x₂`-bracket is `+(2a⁷b³-a²b⁸)` (matching the
terms `+(2a⁷b³-a²b⁸)x₀x₁³x₂ + (2a⁷b³-a²b⁸)x₁x₂³` of the explicit shape) while the `x₀`-bracket is
`-(3a⁶b⁴+ab⁹)` (matching `-(3a⁶b⁴+ab⁹)x₀²x₁² - (3a⁶b⁴+ab⁹)x₀x₂²`). -/
theorem sdualT_one_eq_structural (a b : K) :
    Work.MotK.TGen.sdualT a b 1 =
      -((C a) ^(5:ℕ) * (C b) ^(5:ℕ)) * ((X 0) ^(5:ℕ) + (X 1) ^(5:ℕ) + (X 2) ^(5:ℕ) + 1)
      + ((2 * (C a) ^(3:ℕ) * (C b) ^(7:ℕ) + (C a) ^(8:ℕ) * (C b) ^(2:ℕ)) * X 0
          + (3 * (C a) ^(4:ℕ) * (C b) ^(6:ℕ) - (C a) ^(9:ℕ) * (C b)) * X 1 * X 2)
        * ((X 0) ^(2:ℕ) * X 2 + X 1)
      + ((2 * (C a) ^(7:ℕ) * (C b) ^(3:ℕ) - (C a) ^(2:ℕ) * (C b) ^(8:ℕ)) * X 1 * X 2
          - (3 * (C a) ^(6:ℕ) * (C b) ^(4:ℕ) + (C a) * (C b) ^(9:ℕ)) * X 0)
        * (X 0 * (X 1) ^(2:ℕ) + (X 2) ^(2:ℕ)) := by
  rw [sdualT_explicit]
  simp only [MvPolynomial.C_1]
  first | refl_ring1 | ring

end Work.MotK.TwCensus
