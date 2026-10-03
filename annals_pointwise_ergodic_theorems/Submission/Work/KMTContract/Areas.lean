/-
# The eight areas of the KMT contract (`ROUTE_LEAD.md` §3.1)

**FROZEN.**  This file lists, as one `Prop` each, the eight mathematical areas into which the
proof of Krause--Mirek--Tao's Theorem `end-var` is decomposed by `ROUTE_LEAD.md` §3.1.  They are
consumed, and *only* consumed, by `Submission/Work/KMTContract/Composition.lean`, which proves
the composition `exists_varEstHalfFin_Cv_of_areas` (`ROUTE_LEAD.md` §3.2) from them, and their
hypothesis lists are shown to be satisfiable at non-degenerate instances in
`Submission/Work/KMTContract/Witness.lean`.

## Refereeing record

Each area statement was read by two independent referees (`request_review`), who checked it
against the paper's source (`ROUTE_LEAD.md` §3.1 and the TeX of arXiv:2008.00857), the
quantifier order of §3.3, satisfiability of the hypotheses, and the neighbouring definitions.
All eight were found **correct as stated**.  Their substantive remarks are recorded with each
area below.  Three remarks are worth repeating here:

* **A2**: the hypothesis `N₀ ≤ A·N^deg` is weaker than the paper's `N₀ ~ N^deg`; dropping the
  lower bound only *strengthens* the statement (small supports are a special case).
* **A7**: the clause `p₁ ≠ 2 ∨ p₂ ≠ 2` is redundant (the loss bound at `(2,2)` follows from the
  gain bound of A6), but keeping it makes the constant bookkeeping of the composition explicit —
  the composition instantiates A7 only at the *auxiliary* exponents, which satisfy it by
  construction.
* **A8**: the `q₀ = 1` endpoint of the interpolation is outside the range of the interpolation
  lemma `bilinear_operator_interp` of the workspace's `Interpolation` area; the `ℓ¹` endpoint
  needs the trilinear Stein interpolation `stein_trilinear` (which is proved there) instead.  This
  is extra work for whoever proves A8, not a defect of the statement.

## Changes with respect to `ROUTE_LEAD.md` §3.1

* A8's interpolated constant is written with the *real* power `(M : ℝ) ^ θ` and
  `Real.toNNReal` (`ENNReal.rpow` of a coerced non-negative real is the same number); the
  composition does all of its arithmetic in `ℝ`, and this avoids `ENNReal.rpow` bookkeeping at
  every use site.  A8 additionally requires `Cθ > 0` (needed so that the degenerate
  `ℓ^p`-infinite cases are vacuous).
* A4's minor-arc hypothesis is the *physical-space* condition `kmtProj ρ l k f = 0` (as in
  `ROUTE_LEAD.md` §3.4, which explains that this is what §5's proof uses), rather than a
  vanishing condition on an `ℓ²` Fourier transform.
* A6/A7 are stated for the canonical gain/loss weights of §3.1 with the constant of A6/A7 being a
  function of `Λ` (forced, see finding F2); the composition interpolates them with A8.

## The areas

* A1 `AreaA1` — the Ionescu--Wainger multiplier theorem at even exponents (MSZ3 Thm 2.1 /
  Tao arXiv:2008.05066); already present in the workspace as
  `Work.Analysis.IWMultiplier.IWMultiplierBoundStatement_even` (Appendix A of the paper);
* A2 `AreaA2` — Peluse's inverse theorem in the corrected form (paper Thm `pp`;
  Peluse arXiv:1909.00309 Thm 3.3);
* A3 `AreaA3` — the `ℓ^p`-improving estimate for polynomial averages for *some* `p < 2`
  (paper Prop `lp-improv`; provable by a classical Weyl-inequality circle-method argument);
* A4 `AreaA4` — the single-scale minor-arc estimate `improv` (paper §5) from A1, A2 and A3;
* A5 `AreaA5` — the minor-arc input (B) of §4 for the concrete projections `kmtPj` (from A4);
* A6 `AreaA6` — Theorem `varp` at `(2,2,1)` with the exponential gain (paper §6--§9);
* A7 `AreaA7` — Theorem `varp` at all other exponents with a controlled loss (paper §6--§8);
* A8 `VarBilinInterp` — the `V^r`-valued bilinear interpolation lemma (Stein/Calderón);
  a general lemma, not an assumption about the paper.

## Design of the quantifiers (why they are as they are)

The areas are *implications* from the earlier areas, so all eight can be attacked in parallel.
The quantifier order is dictated by the hierarchy of constants of `ROUTE_LEAD.md` §3.3:

`c_improv` (A4, **independent of `ρ`**) → `C₀ ≥ C₀min(c_improv, p₁, p₂)` (A5) → for that `C₀`:
`c_varp`, `A` (A6, A7, **independent of `ρ`**) → `ρ ≤ min(ρ₀'s, (1-θ)c_varp/(2θ(A+1)))`.

An area statement must never quantify `∀ C₀` *after* `ρ`, nor let `c`/`A` depend on `ρ`: those are
exactly the over-general forms that would be false (see §3.3 of `ROUTE_LEAD.md`; for A6/A7 the
`C₀`-parameter is fixed before `ρ` is chosen, and the `∃ c`/`∃ A` come out *after* `C₀` but
*before* `ρ`).

## Notations

* `kmtProj ρ l k`, `kmtPj ρ`, `PieceBound ρ P C₀ p₁ p₂ p r w`, `truncZ` — the shared definitions of
  `Submission/Work/KMTContract/Defs.lean`;
* `logN N = ⌊log₂ max(N,2)⌋` and `heightScale C₀ N`, `inIndexSet C₀ l s₁ s₂ N`, `varpCol`, `lmax`,
  `AhalfR TZ N X P`, `MinorArcInput`, `VarpStatementΛ` — the §5 vocabulary of the `EndVar` chapter
  (`Submission/Work/Analysis/EndVar/`) and of `Submission/Work/KMTContract/VarpLambda.lean`;
* `SupportIn`, `bilinPair`, `AhalfZ`, `FinSupp` — `Submission/Work/Analysis/InverseTheory/`;
* `AhalfZ` is the paper's `Ã_N(f,g)(x) = N⁻¹ ∑_{N/2<n≤N} f(x+n)g(x+P(n))`; `AhalfR TZ` is the
  same operator with the shifts `x - n`, `x - P(n)` (the reflection `x ↦ -x` of the paper's
  convention, which does not affect any norm).
-/
import Submission.Work.KMTContract.VarpLambda

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTContract

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems

open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier
open Work.Analysis.EndVar
open Work.Analysis.InverseTheory
open Work.Analysis.Paraproduct (IWProjections)

/-! ## A1 — the Ionescu--Wainger multiplier theorem, even exponents -/

/-- **Area A1 (Ionescu--Wainger multiplier theorem, even exponents).**

Appendix `iw-app` of the paper states, and cites `[MSZ3, Theorem 2.1]` for, the bound

`‖T^{≤l}_φ‖_{ℓ^q(ℤ;H)} ≲_{ρ,q} ⟨l⟩ ‖T_φ‖_{L^q(ℝ)}`

for `q ∈ 2ℕ ∪ (2ℕ)'`, on good major arcs and for symbols `φ` supported in `ℝ_{≤k}`.  The
workspace already contains this statement, with the deep part isolated as the *even* exponents
(`k₀ ≥ 2`); the dual-even exponents follow from the even case by the proved duality transfer
`IWLqBound_of_dual`, and all other `1 < q < ∞` by the proved Riesz--Thorin interpolation
`IWLqBound_interpolation`.  So A1 is literally the workspace's
`Work.Analysis.IWMultiplier.IWMultiplierBoundStatement_even`, and there is nothing to state.

This is the deepest *analytic* input of the areas (together with A2), and the point at which the
contract meets the `Fourier`/`IonescuWainger` literature.  See the report of
`Submission/Work/KMTContract/` for the correspondence with the sibling development. -/
def AreaA1 : Prop := IWMultiplierBoundStatement_even

theorem areaA1_iff : AreaA1 ↔ IWMultiplierBoundStatement_even := Iff.rfl

/-! ## A2 — Peluse's inverse theorem, corrected -/

/-- **Area A2 (Peluse's inverse theorem, corrected).**  Krause--Mirek--Tao, Theorem `pp`
(whose displayed statement has the absolute value in the wrong place): Peluse,
arXiv:1909.00309, Theorem 3.3 with `m = 2`, `P₁ = y`, `P₂ = P`.

Let `P ∈ ℤ[X]`, `d = deg P ≥ 2` and `A ≥ 1`.  There are `C, K > 0` (depending on `P` and `A`)
such that for all `N ≥ 1`, `0 < δ ≤ 1`, `N₀ ≤ A N^d` and `f, g, h : ℤ → ℂ` supported in
`[-N₀, N₀]` with `‖f‖_∞, ‖g‖_∞, ‖h‖_∞ ≤ 1` and `|⟨Ã_N(f,g), h⟩| ≥ δ N^d`, either
`N ≤ C δ^{-K}`, or there are `1 ≤ q ≤ C δ^{-K}` and `δ^K N ≤ C N' ≤ C N` with

`δ^K N^d ≤ C ∑_x ‖(1/N') ∑_{m=1}^{N'} f(x + q m)‖`.

Two corrections with respect to the workspace's `Work.Analysis.InverseTheory.PeluseInverseTheorem`
and `Work.Analysis.Concentration.PeluseInverse` (findings F3 of `ROUTE_LEAD.md`):

* the absolute value is *inside* the `x`-sum (as in the paper's proof of Prop `lip` and in
  Peluse's Theorem 3.3).  With the absolute value outside, the `x`-sum equals `∑ f` by
  translation invariance and the statement is false: for `P = X²`,
  `f = g = (-1)^x 1_{[-N₀,N₀]}`, `h = 1_{[-N₀,N₀]}` one has `Ã_N(f,g) ≈ 1/2` on `[-N₀,N₀]`,
  `δ ≍ 1`, while `∑ f ∈ {0, ±1}` and conclusion (i) fails for large `N`;
* the constants `C, K` depend on `P` (and `A`), not only on `A`.
-/
def PeluseInverseKMT (P : ℤ[X]) : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
  ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
    (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
    SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
    (∀ x, ‖f x‖ ≤ 1) → (∀ x, ‖g x‖ ≤ 1) → (∀ x, ‖h x‖ ≤ 1) →
    δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
    (N : ℝ) ≤ C * δ⁻¹ ^ K ∨
    ∃ q N' : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ C * δ⁻¹ ^ K ∧ 1 ≤ N' ∧ N' ≤ N ∧ δ ^ K * N ≤ C * N' ∧
      δ ^ K * (N : ℝ) ^ P.natDegree ≤
        C * ∑' x : ℤ, ‖(N' : ℂ)⁻¹ * ∑ m ∈ Finset.Icc 1 N', f (x + (q : ℤ) * (m : ℤ))‖

/-- **Area A2.** -/
def AreaA2 : Prop := ∀ P : ℤ[X], 2 ≤ P.natDegree → PeluseInverseKMT P

/-! ## A3 — `ℓ^p`-improving for polynomial averages, some `p < 2` -/

/-- **Area A3 (the `ℓ^p`-improving estimate, `p < 2`).**  Krause--Mirek--Tao, Proposition
`lp-improv`, in the form "for *some* `p < 2`" (which is all the paper uses, see `ROUTE_LEAD.md`
§1.2 S3).  `A^Q_N f(x) = N⁻¹ ∑_{n=1}^N f(x - Q(n))` and the estimate is

`‖A^Q_N f‖_{ℓ²} ≤ C N^{d(1/2 - 1/p)} ‖f‖_{ℓ^p}`,  `d = deg Q ≥ 2`, for some `1 < p < 2`.

The constant `C` may depend on `Q` (it does in the paper: the implied constant depends on the
degree and the coefficients; HKLMY give `p ∈ (1,2)` for `d ≥ 3`, and the circle-method argument
of `ROUTE_LEAD.md` §1.2 S3 gives some `p = 2 - δ_d` for every `d ≥ 2`). Only `Q = P - X` and
`Q = X - P` are consumed by A4. -/
def PolyImproving (Q : ℤ[X]) : Prop :=
  ∃ p : ℝ, 1 < p ∧ p < 2 ∧ ∃ C : ℝ≥0, 0 < C ∧ ∀ (N : ℕ) (f : ℤ → ℂ), 1 ≤ N →
    eLpNorm (fun x : ℤ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, f (x - Q.eval (n : ℤ)))
        2 Measure.count
      ≤ (C : ℝ≥0∞) * ENNReal.ofReal ((N : ℝ) ^ ((Q.natDegree : ℝ) * (1 / 2 - 1 / p))) *
          eLpNorm f (ENNReal.ofReal p) Measure.count

/-- **Area A3.** -/
def AreaA3 : Prop := ∀ Q : ℤ[X], 2 ≤ Q.natDegree → PolyImproving Q

/-! ## A4 — the single-scale minor-arc estimate `improv` -/

/-- **Area A4 (the single-scale minor arc estimate `improv`).**  Krause--Mirek--Tao §5,
Theorem `improv`, in the *physical-space* form in which §5 uses it: the minor-arc hypothesis is
`Π_{≤l,≤-Log N+l} f = 0` (or the analogous condition on `g` at the rescaled height
`d(-Log N + l)`), *not* a vanishing condition on an `ℓ²` Fourier transform (which is not
available for `f ∉ ℓ¹`, see finding F4 of `ROUTE_LEAD.md`).

There is a rate `c > 0` **independent of `ρ`** such that for every `ρ ∈ (0,1]` there is a
constant `C_ρ` with

`‖Ã_N(f,g)‖_{ℓ¹(ℤ)} ≤ C_ρ (2^{-c l} + (Log N)^{-c/ρ}) ‖f‖_{ℓ²} ‖g‖_{ℓ²}`

for all `N ≥ 1`, `l ∈ ℕ` and `f, g ∈ ℓ²(ℤ)` such that `Π_{≤l,≤-Log N+l} f = 0` or
`Π_{≤l,≤d(-Log N+l)} g = 0`.

Here `Π_{≤l,≤k} = kmtProj ρ l k`, i.e. the paper's `T^{≤l}_{η_{≤k}}`; the hypothesis
`kmtProj ρ l k f = 0` is equivalent to `𝓕 f = 0` a.e. on the open arcs of radius `2^k` around
`(ℚ/ℤ)_{≤l}` (the symbol is non-negative), which contains the paper's closed arcs of radius
`2^{k-1}`; this equivalence and the monotonicity in `(l,k)` are what turn the case "(l, -Log N+l)
not good" into the largest good `l' ≤ l`, producing the second summand. -/
def ImprovKMT (P : ℤ[X]) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ≥0,
    ∀ (N l : ℕ) (f g : ℤ → ℂ), 1 ≤ N →
      MemLp f 2 Measure.count → MemLp g 2 Measure.count →
      (kmtProj ρ l (-(logN N) + (l : ℤ)) f = 0 ∨
        kmtProj ρ l ((P.natDegree : ℤ) * (-(logN N) + (l : ℤ))) g = 0) →
      eLpNorm (fun x : ℤ => AhalfR TZ (N : ℝ≥0) X P f g x) 1 Measure.count
        ≤ (C : ℝ≥0∞) *
            ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))) + (logN N : ℝ) ^ (-(c / ρ))) *
            eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count

/-- **Area A4.**  `improv` from the Ionescu--Wainger multiplier theorem (A1), Peluse's inverse
theorem (A2) and the `ℓ^p`-improving estimate (A3), by the chain
PP → LIP → HAHN → STRUCT-I → PROPDUAL → STRUCT-III → STRUCT-IV of §5. -/
def AreaA4 : Prop := ∀ P : ℤ[X], 2 ≤ P.natDegree →
  AreaA1 → PeluseInverseKMT P → PolyImproving (P - X) → PolyImproving (X - P) → ImprovKMT P

/-! ## A5 — the minor-arc input (B) for the concrete projections -/

/-- **Area A5 (the minor-arc input (B) of §4, for the concrete projections).**  There is a
threshold `C₀min` such that for every `C₀ ≥ C₀min` there is `ρ₀ > 0` with: for every
`ρ ∈ (0, ρ₀]`, the single-scale minor arc input `MinorArcInput (kmtPj ρ) P P.natDegree C₀ p₁ p₂ p`
of §4 holds — i.e. both minor-arc parts of the halved average are bounded by
`C ⟨Log N⟩^{-10} ‖f‖_{ℓ^{p₁}} ‖g‖_{ℓ^{p₂}}`.

`C₀min` depends on the rate `c` of `ImprovKMT` and on `p₁, p₂` (through the interpolation
`(1-θ)` of `ROUTE_LEAD.md` §3.2), and `ρ₀` on `C₀`; this dependence, together with the `Λ`-form of
`VarpStatementΛ`, is the hierarchy of constants of §3.3. -/
def MinorArcKMT (P : ℤ[X]) (p₁ p₂ : ℝ≥0∞) : Prop :=
  ∃ C₀min : ℕ, ∀ C₀ : ℕ, C₀min ≤ C₀ → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      Work.Analysis.EndVar.MinorArcInput (kmtPj ρ) P P.natDegree C₀ p₁ p₂ (p₁⁻¹ + p₂⁻¹)⁻¹

/-- **Area A5.** -/
def AreaA5 : Prop := ∀ (P : ℤ[X]) (p₁ p₂ : ℝ≥0∞), 2 ≤ P.natDegree →
  1 < p₁ → p₁ < ⊤ → 1 < p₂ → p₂ < ⊤ → p₁⁻¹ + p₂⁻¹ ≤ 1 →
  AreaA1 → ImprovKMT P → MinorArcKMT P p₁ p₂

/-! ## A6 — Theorem `varp` at `(2,2,1)` with the exponential gain -/

/-- **Area A6 (Theorem `varp` at `(2,2,1)`, with gain).**  For every `C₀ ≥ 1` and `r > 2` there
are a rate `c > 0` (independent of `ρ`) and `ρ₀ > 0` such that for every `ρ ∈ (0, ρ₀]` the §5
columns satisfy the paraproduct estimate at `(p₁,p₂,p) = (2,2,1)` with the *exponential gain*

`2^{-c·max(max l₁ l₂)(max s₁ s₂)}`.

This is the paper's Proposition `high-high-l2` together with the model-operator analysis of
§6--§9 at `(2,2)`; it is the only place where the number theory (A2 through `ImprovKMT`) enters
the paraproduct analysis, and the gain is what makes `∑_{N ∈ D} (Log N)^{-10}` summable over a
lacunary set `D`. -/
def VarpL2KMT (P : ℤ[X]) : Prop :=
  ∀ (C₀ : ℕ) (r : ℝ≥0), 1 ≤ C₀ → (2 : ℝ≥0) < r → ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      PieceBound ρ P C₀ 2 2 1 r
        (fun l₁ l₂ s₁ s₂ => (2 : ℝ) ^ (-(c * (lmax l₁ l₂ (s₁ : ℤ) (s₂ : ℤ) : ℝ))))

/-- **Area A6.** -/
def AreaA6 : Prop := ∀ P : ℤ[X], 2 ≤ P.natDegree → AreaA1 → ImprovKMT P → VarpL2KMT P

/-! ## A7 — Theorem `varp` at every other exponent, with controlled loss -/

/-- **Area A7 (Theorem `varp` at all other exponents, with controlled loss).**  For every
`C₀ ≥ 1` and `r > 2` there are a loss exponent `A ≥ 0` (independent of `ρ`) and `ρ₀ > 0` such
that for every `ρ ∈ (0, ρ₀]` the §5 columns satisfy the paraproduct estimate at `(p₁,p₂,p)`
with `p = (p₁⁻¹+p₂⁻¹)⁻¹` and the *loss*

`2^{A·ρ·max(max l₁ l₂)(max s₁ s₂)}`.

No number theory enters here (see `ROUTE_LEAD.md` §1.2 S6): the proof uses only the
Ionescu--Wainger multiplier theorem, the shifted Calderón--Zygmund theorem, Rademacher--Menshov,
Lépingle/Stein and the sampling theorem. -/
def VarpLossKMT (P : ℤ[X]) (p₁ p₂ : ℝ≥0∞) : Prop :=
  ∀ (C₀ : ℕ) (r : ℝ≥0), 1 ≤ C₀ → (2 : ℝ≥0) < r → ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      PieceBound ρ P C₀ p₁ p₂ (p₁⁻¹ + p₂⁻¹)⁻¹ r
        (fun l₁ l₂ s₁ s₂ => (2 : ℝ) ^ (A * ρ * (lmax l₁ l₂ (s₁ : ℤ) (s₂ : ℤ) : ℝ)))

/-- **Area A7.** -/
def AreaA7 : Prop := ∀ (P : ℤ[X]) (p₁ p₂ : ℝ≥0∞), 2 ≤ P.natDegree →
  1 < p₁ → p₁ < ⊤ → 1 < p₂ → p₂ < ⊤ → p₁⁻¹ + p₂⁻¹ ≤ 1 → (p₁ ≠ 2 ∨ p₂ ≠ 2) →
  AreaA1 → VarpLossKMT P p₁ p₂

/-! ## A8 — `V^r`-valued bilinear interpolation -/

/-- **Area A8 (`V^r`-valued bilinear interpolation).**  Stein/Calderón complex interpolation of a
bilinear operator with values in `ℤ → ℂ` carrying the variational norm `V^r`:
the bounds at `(a₀,b₀,q₀)` and `(a₁,b₁,q₁)` with constants `M₀, M₁` imply the bound at the
interpolated exponents `(a,b,q)` with constant `Cθ · M₀^{1-θ} M₁^θ`.

The hypotheses on `T` are exactly those supplied in the composition of §3.2 for the paraproduct
columns `T = varpCol (kmtPj ρ) …`:

* bilinearity on *finitely supported* inputs (this is where the contract needs the
  linearity of the Ionescu--Wainger projections, see `Submission/Work/KMTContract/ProjAPI`);
* the two `FinSupp` bounds (from A6 and A7);
* pointwise convergence of `T` along the truncations `truncZ K` on `ℓ^p` inputs (this is where the
  contract needs the `O(j^{-2})` decay of the Ionescu--Wainger kernel).

The conclusion is stated for `MemLp` inputs; the extension to all inputs is trivial because the
right-hand side is then `⊤`.  The interpolated constant is written with the *real* power
operation `(M : ℝ) ^ θ` (rather than `ENNReal.rpow` on coerced non-negative reals) purely so that
the composition can do all of its arithmetic in `ℝ`; the two are the same number. -/
def VarBilinInterp : Prop :=
  ∀ (r : ℝ≥0) (a₀ b₀ q₀ a₁ b₁ q₁ a b q : ℝ≥0∞) (θ : ℝ), 1 ≤ r → 0 < θ → θ < 1 →
    1 < a₀ → a₀ < ⊤ → 1 < b₀ → b₀ < ⊤ → 1 < a₁ → a₁ < ⊤ → 1 < b₁ → b₁ < ⊤ →
    1 ≤ q₀ → q₀ < ⊤ → 1 ≤ q₁ → q₁ < ⊤ →
    a⁻¹ = ENNReal.ofReal (1 - θ) * a₀⁻¹ + ENNReal.ofReal θ * a₁⁻¹ →
    b⁻¹ = ENNReal.ofReal (1 - θ) * b₀⁻¹ + ENNReal.ofReal θ * b₁⁻¹ →
    q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹ →
    ∃ Cθ : ℝ≥0, 0 < Cθ ∧ ∀ (T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ) (M₀ M₁ : ℝ≥0),
      (∀ f f' g (c : ℂ), FinSupp f → FinSupp f' → FinSupp g →
        T (f + c • f') g = T f g + c • T f' g) →
      (∀ f g g' (c : ℂ), FinSupp f → FinSupp g → FinSupp g' →
        T f (g + c • g') = T f g + c • T f g') →
      (∀ f g, FinSupp f → FinSupp g →
        eLpNorm (fun x => variationalNorm r (fun n => T f g n x)) q₀ Measure.count
          ≤ (M₀ : ℝ≥0∞) * eLpNorm f a₀ Measure.count * eLpNorm g b₀ Measure.count) →
      (∀ f g, FinSupp f → FinSupp g →
        eLpNorm (fun x => variationalNorm r (fun n => T f g n x)) q₁ Measure.count
          ≤ (M₁ : ℝ≥0∞) * eLpNorm f a₁ Measure.count * eLpNorm g b₁ Measure.count) →
      (∀ f g, MemLp f a Measure.count → MemLp g b Measure.count → ∀ n x,
        Tendsto (fun K : ℕ => T (truncZ K f) (truncZ K g) n x) atTop (𝓝 (T f g n x))) →
      ∀ f g, MemLp f a Measure.count → MemLp g b Measure.count →
        eLpNorm (fun x => variationalNorm r (fun n => T f g n x)) q Measure.count
          ≤ ((Cθ : ℝ) * (M₀ : ℝ) ^ (1 - θ) * (M₁ : ℝ) ^ θ).toNNReal *
              eLpNorm f a Measure.count * eLpNorm g b Measure.count

/-! ## The conjunction of the areas -/

/-- The eight areas, in the form in which the composition `exists_varEstHalfFin_Cv_of_areas`
consumes them. -/
def AllAreas : Prop :=
  AreaA1 ∧ AreaA2 ∧ AreaA3 ∧ AreaA4 ∧ AreaA5 ∧ AreaA6 ∧ AreaA7 ∧ VarBilinInterp

end

end Work.KMTContract
