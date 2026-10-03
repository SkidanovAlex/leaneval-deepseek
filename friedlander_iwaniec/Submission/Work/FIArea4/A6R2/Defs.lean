/-
# Area 4 (round 6): the *separated* form of the round-6 §15 reduction (ratio symbol `(z₂/z₁|d)`)

The target `Work.FIArea4.A6RedProp` bounds

  `‖Tcut (radN Pa) (A6cut ψ X j) β‖ ≤ C(log N+1)^8 · S15Br6 Pa X · Σ_{z∈boxN} τ(Re z)³‖β z‖²`

— *FI* §15 (p. 1003) for the round-6 symbol `(z₂/z₁|d)`, with the `τ³` energy and **without** the
crude `P^{-1}N²` term of the paper.

## Route (the paper's, as in the frozen chain but symbol-aligned)

* `psiSum6` — the `ψ`-cut sum on the relaxed index set `S15ixSet` (identified with the `Tcut` of
  the target by `PsiSumEqTcut6`); its per-pair weight is `coef6 = 2β₁β̄₂(φ(d)/d)(z₂/z₁|d)`;
* `expLog6` — the same with `logFac6` in place of the `ψ`-cut (the object of the separation step);
* `expSum6` — the same with the angular character `e^{iℓ(α₂-α₁)}` in place of `logFac6` (the
  object of the variance estimate);
* `pD6`/`expSum6` reindexed by the modulus, `pD6Stratum` the per-modulus `e`-stratified
  class-Cauchy–Schwarz bound, `strUvarSum6` the dyadic summation of the stratum class variances
  against Proposition 14.1, and `ExpBound6` the resulting variance bound.

The point of the round-6 alignment is that **the stratum arrays are the frozen ones**
(`S15strU`, `S15strV`: the `(Re z|e)`-factor of *FI* (15.2) is exactly the `e`-part
`(s₁s₂|e)` of the *ratio* symbol, and `EvarG`'s built-in weight `(Re w|oddPart m)` is exactly
its `d'`-part `(ρ₁ρ₂|d')`), so the round-6 per-modulus step is the frozen one with the **class
factor `≡ 1`** instead of `(e²+a²|d')`, and the `τ³` energy absorbs the whole `Σ_{e|d}`
stratification (`Σ_{e|r} e^{-σ} ≤ Π_{p|r}(1-p^{-σ})^{-1} ≤ 3.41^{ω(r)} < 8^{ω(r)} ≤ τ(r)³`).
-/
import Mathlib
import Submission.Work.FIArea4.A6Defs
import Submission.Work.FIArea4.S15cutDefs
import Submission.Work.FIArea4.S15stratumDefs
import Submission.Work.FIArea4.S15expSumDefs
import Submission.Work.FIArea4.S15EvarGDefs
import Submission.Work.FIArea4.S15prim_defs
import Submission.Work.FITop4.Defs6

namespace Work.FIArea4
namespace A6R2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The round-6 pair weight and the separated sums -/

/-- The round-6 weight of a modulus: `(φ(d)/d)·(z₂/z₁|d)` (the *ratio* symbol of *FI* (8.14)). -/
def w6 (i : S15Id) : ℂ :=
  (((Nat.totient i.2 : ℝ) / (i.2 : ℝ) : ℝ) : ℂ) *
    ((Work.FITop4.ratioSym i.1.1 i.1.2 i.2 : ℤ) : ℂ)

/-- The round-6 coefficient `2β_{z₁}β̄_{z₂}(φ(d)/d)(z₂/z₁|d)` of a triple. -/
def coef6 (β : GaussianInt → ℂ) (i : S15Id) : ℂ :=
  2 * (β i.1.1 * star (β i.1.2)) * w6 i

/-- **The separated round-6 sum**: `Σ_{(z₁,z₂,d)} 2β₁β̄₂(φ(d)/d)(z₂/z₁|d)e^{iℓ(α₂-α₁)}e(ux)y^{it}`
on the relaxed index set `S15ixSet`. -/
def expSum6 (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ) : ℂ :=
  ∑ i ∈ S15ixSet Pa X j, coef6 β i * S15theta ℓ i.1.1 i.1.2 * S15phase X j u t i

/-- The separated round-6 sum with the round-6 logarithm `logFac6` (the object of the log-sine
Fourier expansion). -/
def expLog6 (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ) (u t : ℝ) : ℂ :=
  ∑ i ∈ S15ixSet Pa X j,
    coef6 β i * ((Work.FITop4.logFac6 i.1.1 i.1.2 : ℝ) : ℂ) * S15phase X j u t i

/-- The round-6 `ψ`-cut sum on the relaxed index set (identified with the target's `Tcut`). -/
def psiSum6 (Pa : Work.FITop.Params) (X j : ℕ) (ψ : ℝ → ℝ) (β : GaussianInt → ℂ) : ℂ :=
  ∑ i ∈ S15ixSet Pa X j,
    coef6 β i * ((Work.FITop4.logFac6 i.1.1 i.1.2 : ℝ) : ℂ) *
      ((ψ (|S15x i.1.1 i.1.2| * S15y X j i.2 i.1.1 i.1.2) : ℝ) : ℂ)

/-- The triples of `S15ixSet` on which the coefficient `2β_{z₁}β̄_{z₂}` does not vanish. -/
def supp6 (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ) : Finset S15Id :=
  (S15ixSet Pa X j).filter (fun i => β i.1.1 ≠ 0 ∧ β i.1.2 ≠ 0)

/-! ## 2. The per-modulus sum -/

/-- **The per-modulus round-6 sum**: `expSum6` with the modulus `d` fixed (the object of the
per-modulus `e`-stratified class Cauchy–Schwarz). -/
def pD6 (Pa : Work.FITop.Params) (X j d : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ) : ℂ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if Work.FIPlan.GaussCoprime z1 z2 ∧ X < d ∧
        4 * d ∣ Work.FIPlan.absDelta z1 z2 ∧ 0 < Work.FIPlan.absDelta z1 z2
      then coef6 β ((z1, z2), d) * S15theta ℓ z1 z2 * S15phase X j u t ((z1, z2), d)
      else 0)

/-- **The unfiltered round-6 index set** (the pair coprimality `GaussCoprime` dropped): the
pair sum over the *unfiltered* index set is what the class Cauchy–Schwarz controls, the filtered
one being recovered by the crude (energy-aware) removal of the non-coprime pairs. -/
def ngset6 (Pa : Work.FITop.Params) (X j : ℕ) : Finset S15Id :=
  ((Work.FITop.boxN Pa ×ˢ Work.FITop.boxN Pa) ×ˢ Finset.Icc 1 (S15Y Pa X j)).filter
    (fun i => X < i.2 ∧ 4 * i.2 ∣ Work.FIPlan.absDelta i.1.1 i.1.2 ∧
      0 < Work.FIPlan.absDelta i.1.1 i.1.2)

/-- **The unfiltered separated round-6 sum** (no pair coprimality). -/
def expSum6ng (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ) : ℂ :=
  ∑ i ∈ ngset6 Pa X j, coef6 β i * S15theta ℓ i.1.1 i.1.2 * S15phase X j u t i

/-- **The unfiltered per-modulus round-6 sum**. -/
def pD6ng (Pa : Work.FITop.Params) (X j d : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ) : ℂ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2 ∧ 0 < Work.FIPlan.absDelta z1 z2
      then coef6 β ((z1, z2), d) * S15theta ℓ z1 z2 * S15phase X j u t ((z1, z2), d)
      else 0)

/-! ## 3. The five inputs -/

/-- **The identification**: on the `ψ`-support window the round-6 `ψ`-cut sum `psiSum6` is the
target's `Tcut` with the round-6 cut `A6cut`. -/
def PsiSumEqTcut6 : Prop :=
  ∀ (Pa : Work.FITop.Params) (X j : ℕ) (ψ : ℝ → ℝ),
    (∀ y : ℝ, (y ≤ 1 / 2 ∨ 5 / 2 ≤ y) → ψ y = 0) → 1 ≤ X →
    ∀ (φ : ℝ) (β : GaussianInt → ℂ),
      IsPrimBoxCoeff Pa φ β →
      Work.FITop4.Tcut (Work.FITop.radN Pa) (A6cut ψ X j) β = psiSum6 Pa X j ψ β

/-- **The separation step** (*FI* (12.13)–(12.14), `Work.FIArea4.Vflip.separation_ineq`): the
`ψ`-cut sum is bounded by `(log N+1)²` times a bound for the exponential sums `expLog6`. -/
def SepBound6 : Prop :=
  ∀ (ψ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
    (∀ y : ℝ, (y ≤ 1 / 2 ∨ 5 / 2 ≤ y) → ψ y = 0) →
  ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (X j : ℕ) (φ : ℝ) (β : GaussianInt → ℂ)
      (M : ℝ),
      IsPrimBoxCoeff Pa φ β → 1 ≤ X → (∀ u t : ℝ, ‖expLog6 Pa X j β u t‖ ≤ M) →
      ‖psiSum6 Pa X j ψ β‖ ≤ C * (Real.log Pa.N + 1) ^ 2 * M

/-- **The log-sine step** (*FI* (15.4)–(15.7), `Work.FIArea4.logSine_fourier` together with
`Work.FIArea7.fi_logFac6_eq_logFac_add_log4`): `expLog6` is bounded by `(log N+1)²` times a bound
for the separated sums `expSum6 ℓ`. -/
def ExpLogBound6 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (X j : ℕ) (φ : ℝ) (β : GaussianInt → ℂ)
      (u t M : ℝ),
      IsPrimBoxCoeff Pa φ β → 1 ≤ X → (∀ ℓ : ℤ, ‖expSum6 Pa X j β ℓ u t‖ ≤ M) →
      ‖expLog6 Pa X j β u t‖ ≤ C * (Real.log Pa.N + 1) ^ 2 * M

/-- **The crux** (*FI* §15 variance half for the ratio symbol): the separated round-6 sum obeys
the Proposition-14.1 bracket `S15Br6` with the `(log N+1)^4` of the bracket's
`D^{1/3}(RS)^{2/3}(log 2RS)^4` term, against the full `τ³` energy `A6Ener3`. -/
def ExpBound6 : Prop :=
  ∃ C x0 : ℝ, 0 < C ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
  ∀ (X j : ℕ) (φ : ℝ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ),
    IsPrimBoxCoeff Pa φ β → 1 ≤ X → (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9) →
    ‖expSum6 Pa X j β ℓ u t‖
      ≤ C * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β

/-- **The per-modulus `e`-stratified class Cauchy–Schwarz** (*FI* (15.1)–(15.2)) for the ratio
symbol, for the **unfiltered** per-modulus sum: bounded by the stratum class variances of the
*frozen* stratum arrays `S15strU`/`S15strV` (whose `(Re w | e)`-factor is precisely the `e`-part
`(s₁s₂|e)` of the ratio symbol) plus the diagonal correction `2Σ_z‖β z‖²`.

The proof mirrors `Work.FIArea4.S15red.stratumSumE_le_EvarG` (the frozen per-stratum bound) with
the symbol factorisation of *FI* (15.2) for the ratio symbol
(`ratioSym z₁ z₂ d = (s₁s₂|e)·(ρ₁ρ₂|d/e)` for `e = (d,Re z₁) = (d,Re z₂)`, `d = e·d'`,
`ρᵢ = Re zᵢ/e`) in place of the frozen `Work.FIArea4.S15red.jacobiSym_factor`, and with the class
factor `F ≡ 1` in place of `(e²+a²|d')`.  The round-6 analogue is
`Work.FIArea4.A6psi.pDng6_le_EvarG`.

(The **filtered** per-modulus sum does *not* obey this bound — the class Cauchy–Schwarz sees the
unfiltered classes, and deleting the non-coprime pairs is not a class condition; the coprimality
is therefore removed at the level of the separated sums by `Removal6`.) -/
def pD6ngStratum : Prop :=
  ∀ (Pa : Work.FITop.Params) (X j d : ℕ) (φ : ℝ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ),
    IsPrimBoxCoeff Pa φ β → 1 ≤ d →
    ‖pD6ng Pa X j d β ℓ u t‖
      ≤ 2 * (∑ e ∈ d.divisors,
          Real.sqrt (EvarG (Work.FITop.radN Pa) (4 * (d / e)) (S15strU β u t ℓ e))
          * Real.sqrt (EvarG (Work.FITop.radN Pa) (4 * (d / e)) (S15strV β u t ℓ e)))
        + 2 * ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2

/-- **The unfiltered crux**: the variance half of *FI* §15 for the unfiltered separated sum, with
the `τ³` energy and the `(log N+1)^4` budget of Proposition 14.1. -/
def ExpBound6ng : Prop :=
  ∃ C x0 : ℝ, 0 < C ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
  ∀ (X j : ℕ) (φ : ℝ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ),
    IsPrimBoxCoeff Pa φ β → 1 ≤ X → (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9) →
    ‖expSum6ng Pa X j β ℓ u t‖
      ≤ C * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β

/-- **The removal of the pair coprimality.**  The difference between the *unfiltered* and the
*filtered* separated round-6 sums — the sum over the *non-coprime* pairs, crudely estimated — is
dominated by the same bracket and energy.  This is the round-6 form of *FI*'s removal of
`(z₁,z₂) = 1`, but *energy-aware* (the paper's crude `P^{-1}N²` is not affordable): by (5.8) every
non-coprime pair carries a common Gaussian divisor `γ` with `|γ|² ≥ P`, so for a fixed `z₁` the
number of partners is at most `ω(z₁)·K/P`, and the loss `K/P` is absorbed by the
`N^{-17/18}`-sized bracket `S15Br6 ≥ X^{-1/2}N` (for `x ≥ x₀`). -/
def Removal6 : Prop :=
  ∃ C x0 : ℝ, 0 < C ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
  ∀ (X j : ℕ) (φ : ℝ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ),
    IsPrimBoxCoeff Pa φ β → 1 ≤ X → (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9) →
    ‖expSum6 Pa X j β ℓ u t - expSum6ng Pa X j β ℓ u t‖
      ≤ C * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β

/-- **The dyadic summation of the stratum class variances** against Proposition 14.1
(*FI* §15: Prop. 14.1 over each dyadic modulus range and each stratum `e`), with the `τ³` energy
that absorbs the `Σ_{e|d}` stratification. -/
def strUvarSum6 : Prop :=
  ∃ C x0 : ℝ, 0 < C ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
  ∀ (X j : ℕ) (φ : ℝ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ),
    IsPrimBoxCoeff Pa φ β → 1 ≤ X → (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9) →
    (∑ e ∈ Finset.Icc 1 (S15Y Pa X j),
        ∑ d' ∈ (Finset.Icc 1 (S15Y Pa X j / e)).filter (fun d' => X < e * d'),
          EvarG (Work.FITop.radN Pa) (4 * d') (S15strU β u t ℓ e))
      ≤ C * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β

end

end A6R2

end Work.FIArea4
