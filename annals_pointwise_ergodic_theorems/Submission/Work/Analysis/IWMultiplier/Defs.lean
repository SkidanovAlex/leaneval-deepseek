/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Analysis.IonescuWainger.EtaCut
import Submission.Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing
import Submission.Work.Analysis.IonescuWainger.iwQl_le
import Submission.Work.Analysis.IonescuWainger.iw_height_card_le
import Submission.Work.Analysis.IonescuWainger.memLp_periodize
import Submission.Work.Analysis.IonescuWainger.multiplier_add
import Submission.Work.Analysis.IonescuWainger.multiplier_comp
import Submission.Work.Analysis.IonescuWainger.norm_iwOpSet_le
import Submission.Work.Analysis.IonescuWainger.one_div_le_norm_of_ne
import Submission.Work.Analysis.IonescuWainger.supportedInArc_periodize

/-!
# The vector-valued Ionescu–Wainger multiplier theorem: vocabulary

This file sets up the vocabulary in which the *vector-valued Ionescu–Wainger multiplier theorem*
(Theorem `thm:iw` of Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages*, Annals of Math. 195 (2022), proved in Appendix `iw-app`) is stated.  The
statement itself is the `Prop` `Work.Analysis.IWMultiplier.IWMultiplierTheorem` at the bottom of
this file.

## Setting and notation

Write `T^{≤l}_φ` for the Ionescu–Wainger Fourier projection of §5 of the paper: for a symbol
`φ ∈ Schwartz(ℝ)` supported in the arc `ℝ_{≤k} = [-2^k, 2^k]`, the operator `T^{≤l}_φ` on
`ℓ²(ℤ)` is the Fourier multiplier whose symbol on the dual circle `ℝ/ℤ` is
`ξ ↦ ∑_{α ∈ (ℚ/ℤ)_{≤l}} (periodize φ)(ξ - α)` — this is `iwSymbolSet (iwArithFreqs ρ l) Φ`
with `Φ = periodize φ` in the vocabulary of `Submission.Work.Analysis.IonescuWainger`
(see `Work.Analysis.IonescuWainger.iwSymbolSet` and `…iwOpSet`).

For the `ℓ^q` theory we need the multiplier operator *as an operator on `ℓ^q`*, where it cannot be
defined through the `ℓ²` Fourier isomorphism.  We therefore realise it explicitly as the
convolution on `ℤ` with the Fourier coefficients of its symbol:

* `iwKernel m j = fourierCoeff m j` — the `j`-th Fourier coefficient of `m` on the circle;
* `iwConv A Φ f n = ∑'_j (iwKernel (iwSymbolSet A Φ) j) • f (n - j)` — the convolution of an
  `H`-valued sequence `f` with the kernel of the IW symbol.  For finitely supported `f` this is
  the genuine action of the multiplier, and the identification with the `ℓ²` operator `iwOpSet`
  of the Ionescu–Wainger API is `Work.Analysis.IWMultiplier.iwConv_eq_iwOpSet` (`Basic.lean`).

The *continuous* comparison operator on `ℝ` is the Fourier multiplier `T_φ` with symbol `φ`, and
the norm that appears on the right-hand side of `thm:iw` is `‖T_φ‖_{L^q(ℝ) → L^q(ℝ)}`, encoded by
the predicate `IsLqMultiplierBound q φ M` ("`M` is an upper bound for that operator norm"), tested
on Schwartz functions (which are dense in `L^q`, `q < ∞`).

## Main definitions

* `Work.Analysis.IWMultiplier.angleBracket` — the paper's `⟨l⟩ = max 1 l`;
* `Work.Analysis.IWMultiplier.IsEvenOrDualEven` — the exponent set `2ℕ ∪ (2ℕ)'`;
* `Work.Analysis.IWMultiplier.iwKernel`, `…iwConv` — the IW multiplier on `ℓ^q(ℤ;H)`;
* `Work.Analysis.IWMultiplier.contMulOp`, `…IsLqMultiplierBound` — the continuous multiplier `T_φ`;
* `Work.Analysis.IWMultiplier.IWLqBound` — the `ℓ^q(ℤ;H) → ℓ^q(ℤ;H)` bound for all finite
  dimensional Hilbert spaces `H`;
* `Work.Analysis.IWMultiplier.IWNonAliasingStatement`, `…IWMultiplierBoundStatement`,
  `…IWMultiplierTheorem` — Theorem `thm:iw`.

## Main results

* `Work.Analysis.IWMultiplier.iwNonAliasingStatement` (`NonAliasing.lean`) — the *non-aliasing*
  half of Theorem `thm:iw`, **proved**;
* `Work.Analysis.IWMultiplier.IWMultiplierBoundStatement_q2` (`Q2.lean`) — the `q = 2` case of the
  multiplier half, **proved**.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal FourierTransform
open MeasureTheory

namespace Work.Analysis.IWMultiplier

open Work.Analysis.IonescuWainger

/-- The frequency circle `ℝ/ℤ`, the reducible abbreviation `Work.Analysis.IonescuWainger.Circle`
of `AddCircle 1` (repeated here so that the unqualified name `Circle` is unambiguous in this
namespace). -/
abbrev Circle : Type := AddCircle (1 : ℝ)

/-! ## The bracket `⟨l⟩` and the exponent set `2ℕ ∪ (2ℕ)'` -/

/-- The paper's bracket `⟨l⟩ = max 1 l`, a positive real. -/
def angleBracket (l : ℕ) : ℝ≥0 := max 1 l

theorem angleBracket_pos (l : ℕ) : 0 < angleBracket l :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem one_le_angleBracket (l : ℕ) : 1 ≤ angleBracket l := le_max_left _ _

/-- `q ∈ 2ℕ ∪ (2ℕ)'`: `q` is the exponent of a (non-trivial) even integer, or the dual exponent
`(2k)' = 2k/(2k-1)` of one.  These are exactly the exponents for which the vector-valued
Ionescu–Wainger multiplier theorem of Krause–Mirek–Tao is formulated. -/
def IsEvenOrDualEven (q : ℝ≥0∞) : Prop :=
  (∃ k : ℕ, 1 ≤ k ∧ q = ((2 * k : ℕ) : ℝ≥0∞)) ∨
    (∃ k : ℕ, 1 ≤ k ∧ q = ENNReal.ofReal ((2 * (k : ℝ)) / (2 * (k : ℝ) - 1)))

theorem IsEvenOrDualEven.one_lt {q : ℝ≥0∞} (hq : IsEvenOrDualEven q) : 1 < q := by
  rcases hq with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · have hk2 : 2 ≤ 2 * k := by
      calc 2 = 2 * 1 := by ring
        _ ≤ 2 * k := Nat.mul_le_mul_left 2 hk
    have h2 : ((2 : ℕ) : ℝ≥0∞) ≤ ((2 * k : ℕ) : ℝ≥0∞) := by exact_mod_cast hk2
    exact lt_of_lt_of_le (by norm_num) h2
  · rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff']
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hpos : (0 : ℝ) < 2 * (k : ℝ) - 1 := by linarith
    refine ⟨?_, by positivity⟩
    rw [lt_div_iff₀ hpos]
    linarith

theorem IsEvenOrDualEven.ne_top {q : ℝ≥0∞} (hq : IsEvenOrDualEven q) : q ≠ ⊤ := by
  rcases hq with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact ENNReal.natCast_ne_top _
  · exact ENNReal.ofReal_ne_top

theorem IsEvenOrDualEven.pos {q : ℝ≥0∞} (hq : IsEvenOrDualEven q) : q ≠ 0 := by
  intro h
  rw [h] at hq
  exact absurd hq.one_lt (by norm_num)

/-! ## The Ionescu–Wainger multiplier on `ℓ^q(ℤ; H)` -/

/-- The kernel on `ℤ` of the Fourier multiplier with symbol `m : ℝ/ℤ → ℂ`: the `j`-th Fourier
coefficient `∫ m(ξ) e(-jξ) dξ` of `m`.  The multiplier with symbol `m` acts on sequences by
convolution with this kernel, `(T_m f)(n) = ∑_j (iwKernel m j) f(n - j)`. -/
noncomputable def iwKernel (m : Circle → ℂ) (j : ℤ) : ℂ :=
  fourierCoeff m j

/-- The Ionescu–Wainger multiplier acting on `H`-valued sequences: convolution with the kernel of
the symbol `iwSymbolSet A Φ`.  For finitely supported `f` this is the action of the Fourier
multiplier with symbol `iwSymbolSet A Φ`; see `iwConv_eq_iwOpSet`. -/
noncomputable def iwConv {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : Finset Circle) (Φ : Circle → ℂ) (f : ℤ → H) (n : ℤ) : H :=
  ∑' j : ℤ, iwKernel (iwSymbolSet A Φ) j • f (n - j)

theorem iwConv_apply {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : Finset Circle) (Φ : Circle → ℂ) (f : ℤ → H) (n : ℤ) :
    iwConv A Φ f n = ∑' j : ℤ, iwKernel (iwSymbolSet A Φ) j • f (n - j) := rfl

/-- **The `ℓ^q` bound for the Ionescu–Wainger multiplier.**  `IWLqBound A Φ q C` is the assertion
that the multiplier with symbol `iwSymbolSet A Φ` is bounded on `ℓ^q(ℤ; H)` with norm at most `C`,
*uniformly* over all finite dimensional Hilbert spaces `H`, tested on finitely supported
sequences (which are dense in `ℓ^q`, `q < ∞`). -/
def IWLqBound (A : Finset Circle) (Φ : Circle → ℂ) (q : ℝ≥0∞) (C : ℝ≥0) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (f : ℤ → H), (Function.support f).Finite →
      eLpNorm (iwConv A Φ f) q Measure.count
        ≤ ENNReal.ofReal (C : ℝ) * eLpNorm f q Measure.count

/-- The scalar specialisation of `IWLqBound`: the multiplier on `ℓ^q(ℤ; ℂ)`. -/
def IWLqBoundScalar (A : Finset Circle) (Φ : Circle → ℂ) (q : ℝ≥0∞) (C : ℝ≥0) : Prop :=
  ∀ f : ℤ → ℂ, (Function.support f).Finite →
    eLpNorm (iwConv A Φ f) q Measure.count
      ≤ ENNReal.ofReal (C : ℝ) * eLpNorm f q Measure.count

theorem IWLqBound.scalar {A : Finset Circle} {Φ : Circle → ℂ} {q : ℝ≥0∞} {C : ℝ≥0}
    (h : IWLqBound A Φ q C) : IWLqBoundScalar A Φ q C :=
  fun f hf => h ℂ f hf

/-! ## The continuous multiplier `T_φ` on `ℝ` -/

/-- The continuous Fourier multiplier on `ℝ` with symbol `φ`: `T_φ f = 𝓕⁻(φ · 𝓕 f)`.  For
Schwartz `φ` this is convolution with the Schwartz function `𝓕⁻φ`, hence bounded on every
`L^q(ℝ)`, `1 < q < ∞`. -/
noncomputable def contMulOp (φ : ℝ → ℂ) (f : ℝ → ℂ) : ℝ → ℂ :=
  𝓕⁻ (fun ξ : ℝ => φ ξ * 𝓕 f ξ)

/-- `IsLqMultiplierBound q φ M` asserts that `M` bounds the operator norm of the continuous
Fourier multiplier `T_φ` on `L^q(ℝ)`.  Since Schwartz functions are dense in `L^q` for `q < ∞`,
it is equivalent to `‖T_φ‖_{L^q(ℝ)→L^q(ℝ)} ≤ M`; in particular the optimal such `M` is the
operator norm appearing on the right-hand side of Theorem `thm:iw`. -/
def IsLqMultiplierBound (q : ℝ≥0∞) (φ : ℝ → ℂ) (M : ℝ≥0) : Prop :=
  ∀ f : SchwartzMap ℝ ℂ, eLpNorm (contMulOp φ (f : ℝ → ℂ)) q volume
    ≤ ENNReal.ofReal (M : ℝ) * eLpNorm (f : ℝ → ℂ) q volume

/-! ## Theorem `thm:iw` -/

/-- **The non-aliasing half of Theorem `thm:iw`** (Krause–Mirek–Tao, Appendix `iw-app`): for
`ρ > 0` there is a constant `C_ρ` such that whenever `(l,k)` has good major arcs, i.e.
`k ≤ -C_ρ 2^{ρl}`, the addition map `(θ,α) ↦ θ + α` is injective on `ℝ_{≤k} × (ℚ/ℤ)_{≤l}`.

This half is *proved* in `NonAliasing.lean`. -/
def IWNonAliasingStatement : Prop :=
  ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧
    ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → NonAliasing k (iwArithFreqs ρ l)

/-- **The multiplier half of Theorem `thm:iw`** — the *vector-valued Ionescu–Wainger multiplier
theorem*.  For every `ρ ∈ (0,1]` there is a constant `C_ρ` such that, whenever `(l,k)` has good
major arcs, the compact set `ℝ_{≤k} × (ℚ/ℤ)_{≤l}` is non-aliasing *and*, for every
`q ∈ 2ℕ ∪ (2ℕ)'`, every Schwartz symbol `φ` supported in `ℝ_{≤k}` and every finite dimensional
Hilbert space `H`, the Ionescu–Wainger projection `T^{≤l}_φ` is bounded on `ℓ^q(ℤ;H)` with

`‖T^{≤l}_φ‖_{ℓ^q(ℤ;H) → ℓ^q(ℤ;H)} ≤ C_{ρ,q} ⟨l⟩ ‖T_φ‖_{L^q(ℝ) → L^q(ℝ)}`,

where `‖T_φ‖_{L^q(ℝ)→L^q(ℝ)}` is encoded by `IsLqMultiplierBound q φ M`.  In the paper the
constant `C_{ρ,q}` is `≲_{ρ,q} 1`; here it is produced existentially, as a function of `ρ` and
`q`. -/
def IWMultiplierBoundStatement : Prop :=
  ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧
    (∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → NonAliasing k (iwArithFreqs ρ l)) ∧
    (∀ (q : ℝ≥0∞), IsEvenOrDualEven q → ∃ C : ℝ≥0, 0 < C ∧
      ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k →
      ∀ (φ : SchwartzMap ℝ ℂ), (∀ x, φ x ≠ 0 → x ∈ realArc k) →
      ∀ (M : ℝ≥0), IsLqMultiplierBound q (φ : ℝ → ℂ) M →
        IWLqBound (iwArithFreqs ρ l) (periodize (φ : ℝ → ℂ)) q (C * angleBracket l * M))

/-- **Theorem `thm:iw`** (vector-valued Ionescu–Wainger multiplier theorem), as a single named
`Prop`: the conjunction of the non-aliasing statement and the multiplier bound. -/
def IWMultiplierTheorem : Prop := IWNonAliasingStatement ∧ IWMultiplierBoundStatement

/-- The multiplier half of Theorem `thm:iw` implies the non-aliasing half. -/
theorem IWMultiplierBoundStatement.nonAliasing (h : IWMultiplierBoundStatement) :
    IWNonAliasingStatement :=
  fun ρ hρ hρ1 => by
    obtain ⟨Cρ, hCρ, hA, _⟩ := h ρ hρ hρ1
    exact ⟨Cρ, hCρ, hA⟩

end Work.Analysis.IWMultiplier
