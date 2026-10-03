/-
# Area 4 (round 6): the vocabulary of the §15 reduction of `A6PieceBound`

The definitions used by `Submission.Work.FIArea4.A6_piece_bound` and its delegated inputs.
No theorem with a `sorry` lives here, so it can be imported by work in flight.

## The reduction is stated for `IsPrimBoxCoeff`, not for `IsBetaCoeff6`

The closing step (the two-branch/hybrid argument of FI §15's closing estimate) must split a
coefficient into a *light* and a *heavy* part.  `Work.FITop3.IsBoxCoeff` and
`Work.FIArea4.IsPrimBoxCoeff` are closed under restriction of the support — `|β z| ≤ τ(|z|²)` and
the polar-box support survive a further restriction — whereas `Work.FITop4.IsBetaCoeff6` is *not*
(it pins `β z` to the value `q(arg z - φ)p(|z|²)μ(|z|²)γ(|z|²;C)` on the whole good set, so a
restriction of an `IsBetaCoeff6` array is again one only on the good set).  The reduction half of
§15, on the other hand, uses nothing from (5.13) beyond `|β z| ≤ τ(|z|²)`, the polar-box support,
the primitivity `(Re z, 2 Im z) = 1` and (5.8) — which is exactly what `IsPrimBoxCoeff` records.
So the reduction is stated at `IsPrimBoxCoeff`, and the target's `IsBetaCoeff6` hypothesis is
discharged by `IsBetaCoeff6 ⟹ IsPrimBoxCoeff` (the `μ`-factor gives squarefreeness, hence
`(Re z, Im z) = 1`, and `InPolarBox` gives primacy, hence `Re z` odd).
## Build-performance rule (from the project lead, applies to the whole A6 subtree)

Never let an arithmetic tactic (`ring`, `norm_num`, `simp`, `positivity`, `nlinarith`,
`field_simp`) see a *literal* huge exponent such as `(Real.log N + 1) ^ (2 ^ 20)` or
`(2 : ℝ) ^ (2 ^ 20 + 2)`: it tries to normalise/unfold the power and the search explodes (hour-long
builds).  Make every such quantity opaque first,

```
set L : ℝ := (Real.log Pa.N + 1) ^ (2 ^ 20) with hLdef
have hL1 : 1 ≤ L := one_le_pow₀ (by positivity)   -- proved ONCE
clear_value L
```

and then do the inequality with `L` (and `K := (2:ℝ)^(2^20+2)`, ...) as atoms
(`linarith only [...]`, `nlinarith only [...]` on explicit facts, `mul_le_mul`, `div_le_div`).
Verify each piece with `lean_check` (seconds) before rebuilding the file.

## Remaining-work map for `A6_piece_bound` (round-6 §15)

* proved: `A6Light` (`A6Light.lean`), `A6Crude` (`A6Crude.lean`), `A6Ener3_le`,
  `A6R/enerQuad6` (= the τ³ stratum-energy bookkeeping, `Σ_{e|n}τ(n/e) = τ₂(n) ≤ τ(n)³`),
  `A6R/removal6` (the coprimality removal), `A6R2/Crux`, `A6R2/pD6ngStratumBound`,
  `A6R2/sepBound6`, `A6R2/expLogBound6`, `A6R2/psiSumEqTcut6`;
* proved and WIRED: `A6R2.strUvarSum6` (`A6R/strUvarSum6.lean`, via `Work.A6R.strUvarBrSum6`
  + `p14_all` + `enerQuad6`), `A6R2.Removal6` (`A6R/removal6.lean`),
  `A6R2/strUEner_le` = `Work.FIArea4.strUEner6fill` (the τ³ stratum energy, from `enerQuad6`),
  the bracket sums (`Work.FIArea4.kBracketSum6c`, `A6R2/kBracketSum_le`), the closing
  `Work.FIArea4.A6Close`, and `A6Red` (`A6Red.lean`, whose two wiring sorries are filled);
* `A6R2/Crux.lean` used to import the (now deleted by the frozen-chain agents) module
  `S15EvarG_filtered_sum_le` for three helper lemmas; those are re-proved in
  `S15EG_strV_eq_strU_neg`, `S15EG_sum_divisors_Icc_filter`, `S15EG_sum_sum_sqrt_mul_sqrt_le`
  and imported by `Crux` instead;
* final assembly: `A6_piece_bound_of_inputs A6Red A6Close A6Crude` (`A6_piece_bound.lean`).

## State of the route (updated 2026-10-02, A6 owner)

The frozen-§15 import churn that used to block `A6psi/*` was removed on the A6 side by rooting the
round-6 support bookkeeping on `Submission.Work.FIArea4.A6supp6` (`A6supp`,
`A6sum_S15ixSet_eq_sum_supp`, `A6supp_bounds`, `A6summable_S15theta` — verbatim copies, under fresh
names, of the frozen items the round-6 separation steps use).  The frozen modules themselves are no
longer imported by this subtree.

The **only** remaining input of the target is now the per-`w` estimate with dilation decay, i.e.
`Work.FIArea4.A6R.perW6b` (`Submission/Work/FIArea4/A6R/perW6b.lean`), consumed by
`Work.FIArea4.A6R.removal6` (`removal6_of_perW6b`) together with the proved divisor bookkeeping
`Work.A6R.sumInvSixthNorm_le`.  That file is now a *pure reduction*: it is
`perW6b_of_risingStrip Work.A6R.riseStripBoundClean`, and `riseStripBoundClean` is the three-regime
assembly `risingStripVvar_of_regimes BandSmallD BandMiddleD BandLargeD` of the **band forms of FI
Propositions 11.1, 13.1, 12.1**.  So the residual gap of `A6_piece_bound` is exactly the *band
large sieve* (frontier map: `Submission/Work/A6R/NOTES_bandNarrowHighSteepT11.md` and
`Submission/Work/A6R/riseHighLargeD_FINDINGS.md`; the current statement is
`Work.A6R.bandLargeSieveNode`, `Submission/Work/A6R/bandLargeSieveNode.lean`).

Two statements of that frontier have been shown FALSE and must not be re-attempted:
`Work.A6R.DilatedP14` (`Submission/Work/A6R/dilatedP14_false.lean`, `not_DilatedP14`) and the naive
band Cauchy–Schwarz comparison of `bandCorrInner` against `√(Evar)·√(Evar)`
(`Submission/Work/FIArea4/NOTES_A6_bandCorrInner_CS_false.md`, counterexample included).

-/

import Mathlib
import Submission.Work.FIArea4.A6Setup
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea4.S15prim_defs

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The §15 bracket of *FI* (15.8) **without** the outer `·N` and the `+1` of
`Work.FIArea4.S15Bracket6`: `X^{-1/2}N + N^{1/3}X^{-1/3}N^{2/3} + N^{23/24+1/1000}`. -/
def S15Br6 (Pa : Work.FITop.Params) (X : ℕ) : ℝ :=
  ((X : ℝ) ^ (-(1 : ℝ) / 2) * Pa.N)
    + (Pa.N ^ ((1 : ℝ) / 3) * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3))
    + Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 1000)

/-- `S15Bracket6` is the bracket of the reduction times `1 + S15Br6`. -/
lemma S15Bracket6_eq (Pa : Work.FITop.Params) (X : ℕ) :
    S15Bracket6 Pa X = (S15Br6 Pa X + 1) * Pa.N := by
  unfold S15Bracket6 S15Br6
  ring

/-- The `τ³`-energy `Σ_{z ∈ boxN} τ(|Re z|)³‖β z‖²` of *FI* §15 (the paper's
`Σ_r Σ_s τ³(r)|β_{r+is}|²`, summed over the frozen box rather than the polar box — harmless
because `β` is supported in the polar box). -/
def A6Ener3 (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : ℝ :=
  ∑ z ∈ Work.FITop.boxN Pa,
    ((((z.re.natAbs.divisors.card : ℕ) : ℝ)) ^ 3) * Complex.normSq (β z)

lemma A6Ener3_nonneg (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : 0 ≤ A6Ener3 Pa β := by
  unfold A6Ener3
  exact Finset.sum_nonneg (fun z _ => mul_nonneg (by positivity) (Complex.normSq_nonneg _))

/-- The `ψ`-cut of the target, as a named cut family. -/
def A6cut (ψ : ℝ → ℝ) (X j : ℕ) : GaussianInt → GaussianInt → ℕ → ℝ :=
  fun z1 z2 d => if X < d then
    ψ ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * 2 ^ j * (d : ℝ))) else 0

/-- **The reduction half of *FI* §15 in the round-6 vocabulary** (the paper's display on p. 1003,
for the paper's ratio symbol `(z₂/z₁|d)`): for every smooth `ψ` supported in `(1/2, 5/2)` there are
`C, x₀ > 0` such that for every admissible datum with `x ≥ x₀`, every primitive box coefficient
(`Work.FIArea4.IsPrimBoxCoeff`), every `j` and `1 ≤ X ≤ N^{1/9}`,

  `‖Tcut (radN Pa) (ψ-cut) β‖ ≤ C·(log N+1)^8·S15Br6 Pa X·Σ_{z∈boxN} τ(|Re z|)³‖β z‖²`.

There is **no** additive `P^{-1}N²` term: the target `A6PieceBound` has none and could not absorb
one (a crude `P^{-1}N²` exceeds its right-hand side by `≍ exp((loglog x)²)` for every `X ≥ 1`), so
the coprimality of the pair sum must be removed inside the class Cauchy–Schwarz
(`Work.FIArea4.S15red.pairSum_classFactor_le`, the route of
`Submission/Work/FIArea4/S15red/relSum_bound.lean`) rather than paid for crudely. -/
def A6RedProp : Prop :=
  ∀ (ψ : ℝ → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) ψ → (∀ y : ℝ, 0 ≤ ψ y) → (∀ y : ℝ, ψ y ≤ 1) →
    (∀ y : ℝ, (y ≤ 1 / 2 ∨ 5 / 2 ≤ y) → ψ y = 0) →
  ∃ C x0 : ℝ, 0 < C ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
  ∀ (X : ℕ) (φ : ℝ) (j : ℕ) (β : GaussianInt → ℂ),
    IsPrimBoxCoeff Pa φ β → 1 ≤ X → (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9) →
    ‖Work.FITop4.Tcut (Work.FITop.radN Pa) (A6cut ψ X j) β‖
      ≤ C * (Real.log Pa.N + 1) ^ 8 * S15Br6 Pa X * A6Ener3 Pa β

/-- **The light part of the `τ³`-energy** (the elementary half of the light branch of the closing
estimate): if every point of `S ⊆ polar box` carries `τ(|Re z|)³‖β z‖² ≤ Y` then the whole
`τ³`-energy of `S` is at most `#S · Y`, and `#S ≤ 100(θ²N + θ√N + 1)` (`polarBox_card_le`). -/
def A6LightProp : Prop :=
  ∃ C : ℝ, 0 < C ∧
  ∀ (Pa : Work.FITop.Params) (φ Y : ℝ) (S : Finset GaussianInt) (β : GaussianInt → ℂ),
    1 ≤ Y →
    (∀ z ∈ S, Work.FITop3.InPolarBox Pa φ z) →
    (∀ z : GaussianInt, ‖β z‖ ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)) →
    (∀ z ∈ S, ((((z.re.natAbs.divisors.card : ℕ) : ℝ)) ^ 3) * Complex.normSq (β z) ≤ Y) →
    (∑ z ∈ S, ((((z.re.natAbs.divisors.card : ℕ) : ℝ)) ^ 3) * Complex.normSq (β z))
      ≤ C * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * Y * (Real.log Pa.N + 1) ^ 40

/-- **The crude (triangle-inequality) bound for the round-6 `Tcut`** — the concentrated-support
branch of the closing estimate, the round-6 analogue of `Work.FIArea4.psiCut_crude_bound`. -/
def A6CrudeProp : Prop :=
  ∃ C : ℝ, 0 < C ∧
  ∀ (ψ : ℝ → ℝ), (∀ y : ℝ, 0 ≤ ψ y) → (∀ y : ℝ, ψ y ≤ 1) →
  ∀ (Pa : Work.FITop.Params) (X j : ℕ) (Bmax Dmax : ℝ) (S : Finset GaussianInt)
    (β : GaussianInt → ℂ),
    1 ≤ X → (∀ z : GaussianInt, β z ≠ 0 → z ∈ S) → (∀ z : GaussianInt, ‖β z‖ ≤ Bmax) →
    (∀ z1 ∈ S, ∀ z2 ∈ S,
      (((Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
          (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2 ∧ X < d)).card : ℝ) ≤ Dmax) →
    ‖Work.FITop4.Tcut (Work.FITop.radN Pa) (A6cut ψ X j) β‖
      ≤ C * Bmax ^ 2 * (S.card : ℝ) ^ 2 * Dmax * (Real.log (4 * Pa.N) + 1)

/-- **The closing half of *FI* §15**: given the reduction, the light-energy bound and the crude
bound, produce the frozen `A6PieceBound`.

## The two branches (this is the proof route; both fit under the target, with overlap)

Write `A := Pa.A'`, so that `θ = (log x)^{-A}` (`Pa.hθ`), and `θ²N + θ√N + 1 ≍ θ²N` unless
`θ√N ≲ 1`.  The two available estimates for `‖Tcut (radN Pa) (A6cut ψ X j) β‖` are

* **energy branch**: `A6RedProp` with the *proved* arithmetic box energy
  `Work.FIArea4.A6Ener3_le` (`Σ_{z∈boxN} τ(Re z)³τ(|z|²)² ≪ (θ²N + N^{5/6} + 1)(log N)^{2^20-30}`)
  gives `≪ (log N)^{2^20-22}·S15Br6·(θ²N + N^{5/6})`, which fits under
  `c θ²(log N)^{2^20}·S15Bracket6` as soon as `N^{5/6} ≪ θ²N(log N)^{22}`;
* **crude branch**: `A6CrudeProp` with `Bmax ≤ max_{n ≤ 2N} τ(n) ≤ 2^{log(2N)/log P}`
  (`NoSmallPrimes`, `log P ≥ (loglog x)²`), `Dmax ≤ max_{n ≤ 2N} τ(n)` (every admissible `d`
  divides `|Δ|/4`) and `#S ≤ 100(θ²N + θ√N + 1)` (`S15_light_energy`'s `polarBox_card_le` step)
  gives `≪ (θ²N + θ√N + 1)²·2^{3log(2N)/log P}·log N`, which fits as soon as
  `θ²·2^{3log(2N)/log P} ≪ (log N)^{2^20}`.

At `log x = 10^{12}` the two thresholds are `A ≤ log N/(12 loglog x) ≈ 1.0·10^9` and
`A ≥ 3.6·10^8` respectively, i.e. **they overlap** (the crude branch also improves as `A`
grows, because `θ² = (log x)^{-2A}` decays while `2^{3log(2N)/log P} ≤ N^{o(1)}` grows only
subpolynomially); so the two branches cover every admissible datum.  `A6LightProp` is the
elementary half needed when the crossing is organised through the *light* set
(`τ(Re z)³‖β z‖² ≤ Y`) rather than through `A6Ener3_le`. -/
def A6CloseProp : Prop :=
  A6RedProp → A6LightProp → A6CrudeProp → Work.FIArea4.A6PieceBound

end

end Work.FIArea4
