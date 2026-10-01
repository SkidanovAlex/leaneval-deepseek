/-
# `Work.LinnikAreas.BGTZ` — the Benli--Goel--Twiss--Zaman (2024) repulsion, vocabulary

This module holds the **definitions** used by the formalization of the explicit
Deuring--Heilbronn repulsion of *Benli, Goel, Twiss, Zaman*, "Explicit Deuring--Heilbronn
phenomenon for Dirichlet L-functions", arXiv:2410.06082 (Theorem 1.3 / Cor. 1.2), which is the
single deep input of AREA 6 of the Linnik contract (see `Submission/Work/LinnikAreas/BGTZ.lean`
for the statement `Siegel.RepulsionBGTZ` that AREA 6 consumes, and `NOTES_area6_route.md` §8 for
the route).

## The source

The paper is in this workspace as `Paper/bgtz.txt` (plain text) and `./.gwork/ex/main-arxiv-v3.tex`
(LaTeX, the authority for the displayed formulae).  The pieces requested against this vocabulary
are the labelled statements of that paper:  Lemma 9.6 of Graham's thesis (= BGTZ Lemma 4.2,
`SieveWeights`), BGTZ Lemma 4.1 (`SelbergSieveMain`), BGTZ Lemma 2.8 (`RatioLone`), BGTZ
Lemma 2.6 (`Phragmen`), BGTZ Lemma 4.3 (`GEstimate`) and BGTZ Proposition 5.1 (`ZeroDetector`).

## The theorem being formalized (BGTZ, Thm. 1.3)

Let `q > 400000`, `T ≥ 4`, and let `χ₁` be a real (quadratic) Dirichlet character modulo `q` with
a real zero `β₁` of `L(s,χ₁)` satisfying `1 - 1/(10 log q) < β₁`.  Assume

* **(Hyp A)** every *primitive* `ψ` mod `N` satisfies `‖L(1/2+it,ψ)‖ ≤ A (N(1+|t|))^θ`, `θ ≤ 1/4`;
* **(Hyp B)** `β₁ < 1 - B/(q^ε (log q)²)`, `ε ≤ 1/2`.

Then every *other* zero `ρ = β+iγ` of any `L(s,χ)`, `χ` a Dirichlet character mod `q` (the
principal one included), with `β > 1/2` and `|γ| ≤ T`, satisfies

`β < 1 - log(θ/(4(1-β₁) log M)) / log M`, `M = K q^{8θ+2ε} T^{4θ}`,

for an explicit absolute `K = K(A,θ,B,ε)` (BGTZ (1.5)).

## The objects of the argument

With `a(n) = Σ_{d|n} χ₁(d) ≥ 0` (Graham's non-negative multiplicative function `1 * χ₁`), the
detector of BGTZ §5 is the mollified sum

`S = Σ_{n ≤ N} a(n) χ(n) (Σ_{d|n} θ_d)² n^{-ρ} (1 - n/N)`,

where `(θ_d)` are Selberg-sieve weights (Graham's Lemma 9.6).  Its Mellin transform is
`F(s,χ) G(s,χ)` with `F(s,χ) = L(s,χ)L(s,χχ₁)` (the Dirichlet series `Σ_n a(n)χ(n)n^{-s}`) and the
sieve function `G` of (BGTZ (5.3)), whose local factors at a prime `p` are, for `u = χ(p)p^{-s}`,

`A(p,u)/(1+A(p,u)) = u(1+χ₁(p)) - χ₁(p)u²`  (writing `A(p,u) = Σ_{k≥1} a(p^k)u^k`),

which is the closed form used by `sieveLocal` below (the identity is proved from
`Σ_{k≥0}a(p^k)u^k = ((1-u)(1-χ₁(p)u))^{-1}`).

Everything below is stated for `χ₁` with `χ₁² = 1` (a real/quadratic character); `(χ₁ n).re` is
then the real value `χ₁(n) ∈ {-1,0,1}` of the character, so all the coefficients are real.
-/

import Mathlib
import Submission.Work.LinnikAreas.SiegelBase

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

namespace BGTZ

variable {q : ℕ} [NeZero q]

/-! ## 1. The coefficients and the detector sum -/

/-- **Graham's `a(n)`**: `a(n) = Σ_{d | n} χ₁(d)`, written through the real part of the (real)
character `χ₁`. -/
def aCoeff (χ₁ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (χ₁ d).re

/-- The local factor of the Selberg sieve function `G(s,χ)` at the prime `p`
(BGTZ (5.3) in the closed form `u(1+χ₁(p)) - χ₁(p)u²`, `u = χ(p)p^{-s}`). -/
def sieveLocal (χ₁ χ : DirichletCharacter ℂ q) (s : ℂ) (p : ℕ) : ℂ :=
  ((1 + ((χ₁ p).re : ℂ)) * (χ p) * (p : ℂ) ^ (-s))
    - (((χ₁ p).re : ℂ) * (χ p) ^ 2 * (p : ℂ) ^ (-(2 * s)))

/-- **The Selberg sieve function `G(s,χ)`** of BGTZ (5.3), in the multiplicative closed form
`Σ_{d,e ≤ R} θ_dθ_e ∏_{p | [d,e]} (u_p(1+χ₁(p)) - χ₁(p)u_p²)` with `u_p = χ(p)p^{-s}`.

For `χ` the principal character mod `q` and `s = 1` this is exactly the quantity bounded by
Graham's Lemma 9.6: the local factor at a prime `p | q` vanishes (as `χ(p) = 0`) and for `p ∤ q`
it equals `1/h(p)` with `h(p) = g(p)+1`, `g(p) = (Σ_{k≥1}a(p^k)p^{-k})^{-1}`. -/
def sieveG (χ₁ : DirichletCharacter ℂ q) (R : ℕ) (θ : ℕ → ℝ) (s : ℂ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
    (θ d : ℂ) * (θ e : ℂ) * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ s p

/-- **The BGTZ detector sum** `Σ_{n ≤ N} a(n)χ(n)(Σ_{d|n}θ_d)² n^{-ρ}(1 - n/N)`. -/
def detector (χ₁ χ : DirichletCharacter ℂ q) (N : ℕ) (θ : ℕ → ℝ) (ρ : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (aCoeff χ₁ n : ℂ) * (χ n)
    * ((∑ d ∈ n.divisors, (θ d : ℂ)) ^ 2) * ((n : ℂ) ^ (-ρ)) * (1 - (n : ℂ) / (N : ℂ))

/-- The `q`-part of the sieve weights: `μ(d)h(d)/(V(R)g(d)) Σ_{r ≤ R/d, (r,d)=1} μ²(r)/g(r)`
is *one* admissible choice; here we only record the structural properties that the proofs use
(`θ_1 = 1`, `θ_d = 0` for non-squarefree `d` or `d > R`, `|θ_d| ≤ 1`). -/
def IsSieveWeight (R : ℕ) (θ : ℕ → ℝ) : Prop :=
  θ 1 = 1 ∧ (∀ d : ℕ, ¬ Squarefree d ∨ R < d → θ d = 0) ∧ ∀ d : ℕ, |θ d| ≤ 1

/-! ## 2. The two hypotheses (BGTZ (2.1), (2.2)) -/

/-- **Hypothesis A** (BGTZ §2): a subconvexity bound on the critical line, uniform over primitive
characters.

The paper states it for `θ ≤ 1/4`; the reason for the slightly wider range `θ ≤ 1/4 + 1/100` allowed
here is that this is what the *shared commons* proves: `LFunction_strip_convexity_explicit` gives
`‖L(1/2+iT,ψ)‖ ≤ C (N(2+|T|))^{1/4}(log(N(2+|T|))+2)`, and the logarithmic factor is absorbed by
any extra positive power of `N(1+|T|)` (`log u + 2 ≤ K u^{1/100}`), so `θ = 1/4 + 1/100` *is*
Hypothesis A with an absolute `A`.  The paper's own choice is the explicit convexity bound of
Thorner--Zaman (`θ = 1/4`, `A = 2.97655`), which needs sharp Stirling estimates; using
`θ = 1/4 + 1/100` instead replaces that deep input by the elementary convexity bound, at the cost
of `8θ = 2.08` instead of `2` in the exponent `c₁ = 8θ + 2ε` of the repulsion — still far below
the threshold `12/5` that AREA 6 needs.  Everywhere in the argument `θ ≤ 1/4` was used only to
dominate `(1+|t|)^{1/4+θ}` by `(1+|t|)^{1/2}`, and the corresponding integrals converge for every
`θ < 3/4`, so the statements are unaffected. -/
def HypA (A θ : ℝ) : Prop :=
  0 < A ∧ 0 < θ ∧ θ ≤ 1 / 4 + 1 / 100 ∧
  ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N), ψ.IsPrimitive → ψ ≠ 1 →
    ∀ t : ℝ, ‖LFunction ψ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ A * (((N : ℝ) * (1 + |t|)) ^ θ)

/-- **Hypothesis B** (BGTZ §2): an upper bound for the Landau--Siegel zero, i.e. a lower bound for
`1 - β₁`.  Siegel's theorem (`Commons…LFunction_realZero_siegel_uniform`, proved in the shared
commons) gives it with any `ε > 0` and an ineffective `B = B(ε)`; Bordignon's theorem gives the
effective `ε = 1/2`, `B = 100`. -/
def HypB (B ε : ℝ) : Prop :=
  0 < B ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧
  ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    1 - β₁ < 1 / (10 * Real.log q) →
    B / ((q : ℝ) ^ ε * (Real.log q) ^ 2) < 1 - β₁

/-! ## 3. The form of the repulsion that AREA 6 consumes -/

/-- **The Deuring--Heilbronn repulsion at all heights**, with *parameters* `(u,v)`:

`λ(ρ) ≥ (log(1/λ₁) - log(24(u + v·ξ)))/(u + v·ξ)`, `ξ = log(5+|Im ρ|)/log q`,

for every further zero `ρ` of every `L(s,χ)`, `χ` mod `q` (the primitive-one formulation of
`zeroMult` covers all primitive characters of conductor dividing `q`), assumed to hold for
`1/(q^{1/100} log q) < λ₁ ≤ 1/10` (the BGTZ hypotheses `β₁ > 1 - 1/(10 log q)` and
`β₁ < 1 - B/(q^ε (log q)²)`).

BGTZ's Theorem 1.3 gives this with `u = 8θ + 2ε`, `v = 4θ`, `24` replaced by anything `≥ 1/c₄`
with `c₄ = θ/4`; with the trivial convexity input `θ = 1/4` this is `u ≈ 2`, `v ≈ 1`, which is
what the high-zero bound `RestHighBGTZSpec` needs (the exponent `(49/10 - 5/2)/u > 1` requires
`u < 12/5`).  See `Submission/Work/LinnikAreas/BGTZ.lean` for the specialisation used by AREA 6
and `BGTZMaster.lean` for the reduction to BGTZ's Theorem 1.3. -/
def RepulsionGen (u v : ℝ) : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log q) < lamOf q (β₁ : ℂ) →
    lamOf q (β₁ : ℂ) ≤ 1 / 10 →
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) →
      lamOf q (β₁ : ℂ) ≤ lamOf q ρ →
      (Real.log (1 / lamOf q (β₁ : ℂ))
          - Real.log (24 * (u + v * (Real.log (5 + |ρ.im|) / Real.log q))))
        / (u + v * (Real.log (5 + |ρ.im|) / Real.log q)) ≤ lamOf q ρ

/- The extra hypothesis `λ₁ ≤ λ(ρ)` in `RepulsionGen` is *not* redundant: it says that the
exceptional zero has the largest real part among the zeros under consideration, which is exactly
what makes the lower-bound half of the detector argument work at `β₁` (the monotonicity step
`n ^ (β₁ - β) ≤ N ^ (β₁ - β)` for `n ≤ N` is valid precisely when `β ≤ β₁`).  Zeros with `λ(ρ)` below
`λ₁` are not repelled in this sense, and in the assembly they are handled by the `λ₁`-free
log-free family count instead: their total mass is of size a negative power of `log q`, which is
dominated by `λ₁` times a negative power of `log q` because Siegel's theorem gives
`λ₁ ≥ C (log q) / q^{1/200}`. -/

/-- **The Deuring--Heilbronn repulsion at all heights, with an arbitrary additive constant.**

This is the form in which the *proof* of BGTZ's Theorem 1.3 (the detector argument) delivers the
repulsion: the additive constant `C₀` is a multiple of `1/cZ`, where `cZ` is the constant of the
zero-free region that the detector consumes (it is used to bound `1/(1 - Re ρ) ≤ log(q·max 4|Im ρ|)/cZ`
in the detector's upper bound), and *this is the only place where that constant enters*.  The
statement `RepulsionGen u v` is the special case `C₀ = 24`; every form with a larger `C₀` is weaker,
and the high-zero bound `Siegel.RestHighBGTZSpec` is insensitive to `C₀` (its dependence is absorbed
into that bound's existential constant). -/
def RepulsionGenC (u v C₀ : ℝ) : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log q) < lamOf q (β₁ : ℂ) →
    lamOf q (β₁ : ℂ) ≤ 1 / 10 →
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) →
      lamOf q (β₁ : ℂ) ≤ lamOf q ρ →
      (Real.log (1 / lamOf q (β₁ : ℂ))
          - Real.log (C₀ * (u + v * (Real.log (5 + |ρ.im|) / Real.log q))))
        / (u + v * (Real.log (5 + |ρ.im|) / Real.log q)) ≤ lamOf q ρ

/-- `RepulsionGen u v` is `RepulsionGenC u v 24` (they are the same statement with the additive
constant displayed). -/
theorem repulsionGen_iff_repulsionGenC (u v : ℝ) :
    RepulsionGen u v ↔ RepulsionGenC u v 24 := Iff.rfl

/-- The real part of the sieve function: the quantity `G(1,χ₀)` bounded by Graham's Lemma 9.6. -/
def sieveGre (χ₁ : DirichletCharacter ℂ q) (R : ℕ) (θ : ℕ → ℝ) (s : ℂ)
    (χ : DirichletCharacter ℂ q) : ℝ :=
  (sieveG χ₁ R θ s χ).re

/-- The sifting level of BGTZ (5.5) — the `R` of the Selberg sieve. -/
def sieveR (A θ : ℝ) (q : ℕ) (β₁ : ℝ) : ℝ :=
  256 * A ^ 2 * (q : ℝ) ^ (2 * θ) * Real.exp (2 * (Real.log q) ^ (3 / 4 : ℝ))
    * (1 - β₁) ^ (-2 : ℝ)

/-- The detection length of BGTZ (5.6) — the `N` of the detector sum. -/
def detN (A θ : ℝ) (q : ℕ) (β₁ T : ℝ) : ℝ :=
  (3 * 10 ^ 16 : ℝ) * A ^ 8 * Real.exp (8 * (Real.log q) ^ (3 / 4 : ℝ))
    * (Real.log (14 * A ^ 2 * (q : ℝ) ^ 3)) ^ 24 * (q : ℝ) ^ (8 * θ) * T ^ (4 * θ)
    * (1 - β₁) ^ (-2 : ℝ)

/-- A convexity bound for the Riemann zeta function on the critical line (the `ζ`-input of the
`G`-estimate), available in the shared commons as
`Commons.NumberTheory.LSeries.exists_bound_norm_riemannZeta_fractional`. -/
def HypZeta (Cz : ℝ) : Prop :=
  0 < Cz ∧ ∀ t : ℝ, 1 ≤ |t| →
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ Cz * |t| ^ (1 / 2 : ℝ) * Real.log (|t| + 2)

/-! ## 4. The piece-Propositions of the BGTZ argument

These are the statements delegated as the pieces of `BGTZ`'s Theorem 1.3 (see the modules
`Submission/Work/LinnikAreas/BGTZ/*.lean`): the Selberg-sieve weights and Graham's bound
(`SieveWeightsProp`), the lower bound for `Σ_{n ≤ R} a(n)/n` (`SelbergSieveMainProp`), the two-sided
relation `L(1,χ₁) ≍ 1 - β₁` (`RatioLoneProp`), the critical-line convexity bound
(`UniformConvexity`), the `G`-estimate (`GEstimate`), and the zero detector
(`DetectorMainProp`).  They are recorded as `Prop`s here so that the assembly
(`Repulsion_of_pieces`) can take them as hypotheses and later be instantiated with the proved
theorems, without repeating their long quantifier blocks. -/

/-- **(Piece) Graham's Selberg-sieve weights and Lemma 9.6.** -/
def SieveWeightsProp : Prop :=
  ∀ {q : ℕ} [NeZero q], 400000 < q → ∀ (χ₁ : DirichletCharacter ℂ q), χ₁ ^ 2 = 1 →
    ∀ {R : ℕ}, 200 ≤ R →
    ∃ θ : ℕ → ℝ, IsSieveWeight R θ ∧
      sieveGre χ₁ R θ 1 (1 : DirichletCharacter ℂ q)
        ≤ (q : ℝ) / (q.totient : ℝ)
          * (∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n / (n : ℝ))⁻¹

/-- **(Piece) BGTZ Lemma 4.1**, in the form the source's proof produces (without the spurious
factor `R^{1-β₁}` of the printed display, see `Work.LinnikAreas.BGTZ.SelbergSieveMain`). -/
def SelbergSieveMainProp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 400000 < q → ∀ (χ₁ : DirichletCharacter ℂ q),
    χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ∀ {β₁ : ℝ}, β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    1 - 1 / (10 * Real.log q) < β₁ → ∀ {A θ : ℝ}, HypA A θ → ∀ {R : ℝ}, 200 ≤ R →
    ‖LFunction χ₁ (1 : ℂ)‖ / ((1 - β₁) * (2 - β₁))
      * (1 - C * A * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (q : ℝ) ^ θ / R ^ (1 / 2 : ℝ))
      ≤ ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aCoeff χ₁ n / (n : ℝ)

/-- **(Piece) BGTZ Lemma 2.8**: `L(1,χ₁) ≍ 1 - β₁`.** -/
def RatioLoneProp : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (q : ℕ) [NeZero q], 400000 < q → ∀ (χ₁ : DirichletCharacter ℂ q),
    χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ∀ {β₁ : ℝ}, β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    1 - 1 / (10 * Real.log q) < β₁ →
    c * (1 - β₁) ≤ ‖LFunction χ₁ (1 : ℂ)‖ ∧
      ‖LFunction χ₁ (1 : ℂ)‖ ≤ C * (Real.log q) ^ 2 * (1 - β₁)

/-- **(Piece) BGTZ Proposition 5.1, the zero detector** (see
`Submission/Work/LinnikAreas/BGTZ/DetectorMain.lean`; the sieve bound is an explicit hypothesis,
without which the statement is false — the residue term is `L(1,χ₁)(φ(q)/q)G(1,χ₀)`). -/
-- **Repair (2026-09-28).**  The sifting level `R` is now pinned from *above* as well as from
-- below: the source *chooses* `R = sieveR A θ q β₁ = 256A²q^{2θ}e^{2(log q)^{3/4}}(1-β₁)^{-2}`
-- (BGTZ (5.1)), and a statement with the lower bound alone is false -- BGTZ Lemma 4.3 carries an
-- `R`-linear term, so for `R` up to `A²q³` the contour integral `detJ` breaks the conclusion (and
-- `IsSieveWeight` alone admits weights with no Selberg cancellation, `‖G(1/2,χ)‖ ≍ R log²R`).  The
-- previous upper bound `Real.log (2eR) ≤ Real.log (2+A²q³)` was far too weak.  Consequences:
-- every consumer of `DetectorMainProp` gets a *stronger* hypothesis, and its own R-choice must now
-- also produce `R ≤ 2*sieveR`.
def DetectorMainProp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 400000 < q → ∀ (χ₁ : DirichletCharacter ℂ q),
    χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ∀ {β₁ : ℝ}, β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    1 - 1 / (10 * Real.log q) < β₁ →
    ∀ {A θ B ε Cz : ℝ}, HypA A θ → HypB B ε → HypZeta Cz →
    ∀ {R : ℕ}, 200 ≤ R →
    C * A ^ 2 * (q : ℝ) ^ (2 * θ) * Real.exp (2 * (Real.log q) ^ (3 / 4 : ℝ))
        * (1 - β₁) ^ (-2 : ℝ) ≤ (R : ℝ) →
    (R : ℝ) ≤ 2 * sieveR A θ q β₁ →
    ∀ {θw : ℕ → ℝ}, IsSieveWeight R θw →
    sieveGre χ₁ R θw 1 (1 : DirichletCharacter ℂ q)
        ≤ (q : ℝ) / (q.totient : ℝ)
          * (∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n / (n : ℝ))⁻¹ →
    ∀ (χ : DirichletCharacter ℂ q) (T : ℝ), 4 ≤ T → ∀ {ρ : ℂ},
      (DirichletCharacter.LFunction χ ρ = 0 ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0) →
      1 / 2 < ρ.re → |ρ.im| ≤ T →
    ∀ (N : ℕ), C * A ^ 8 * Real.exp (8 * (Real.log q) ^ (3 / 4 : ℝ))
          * (Real.log (2 + A ^ 2 * (q : ℝ) ^ 3)) ^ 24 * (q : ℝ) ^ (8 * θ) * T ^ (4 * θ)
          * (1 - β₁) ^ (-2 : ℝ) ≤ (N : ℝ) →
      ‖detector χ₁ χ N θw ρ‖
        ≤ ((2 - β₁) / (1 - ρ.re) + 1 / (ρ.re - 1 / 2)) * (1 - β₁)
          * ((N : ℝ) ^ (1 - ρ.re))

end BGTZ

end Work.LinnikAreas
