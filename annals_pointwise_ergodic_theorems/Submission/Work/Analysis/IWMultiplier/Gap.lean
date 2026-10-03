/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Analysis.IWMultiplier.Q2Vector
import Submission.Work.Analysis.IWMultiplier.Dual

/-!
# The residual input of the vector-valued Ionescu–Wainger multiplier theorem

This file records, precisely, the *gap* between what is proved in this area and Theorem `thm:iw` of
Krause–Mirek–Tao.  It contains no new mathematics: it is the bookkeeping that pinpoints the single
deep input on which `IWMultiplierBoundStatement` (hence `IWMultiplierTheorem`) rests.

## Where the proof stops

The paper's Appendix `iw-app` proves Theorem `thm:iw` in two steps:

1. *non-aliasing*: good major arcs imply that `ℝ_{≤k} × (ℚ/ℤ)_{≤l}` is non-aliasing.  This is
   `Work.Analysis.IWMultiplier.iwNonAliasingStatement`, **proved here** (in `NonAliasing.lean`,
   from `Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing`).

2. the *multiplier bound* `‖T^{≤l}_φ‖_{ℓ^q(ℤ;H)} ≲_{ρ,q} ⟨l⟩ ‖T_φ‖_{L^q(ℝ)}` for
   `q ∈ 2ℕ ∪ (2ℕ)'`.  For this the paper cites `[MSZ3, Theorem 2.1]` (Mirek–Stein–Zorin-Kranich):
   *"The claim (iw-mult) follows from [MSZ3, Theorem 2.1] (specialized to the one-dimensional
   case)"*.  The proof there is the deep super-orthogonality / square-function theory à la
   Ionescu–Wainger and is **not** contained in the present paper.

Accordingly:

* the case `q = 2` of (2) is **proved here**, in the exact shape of the conclusion of
  `IWMultiplierBoundStatement`, for every finite-dimensional Hilbert space `H`
  (`IWMultiplierBoundStatement_q2_vector`, `Q2Vector.lean`), together with the `L²(ℝ)` multiplier
  norm computation `‖T_φ‖_{L²→L²} = ‖φ‖_∞` (`isLqMultiplierBound_two`);
* the remaining exponents `q ∈ 2ℕ ∪ (2ℕ)'`, `q > 2`, are the residual input:
  * `IWMultiplierBoundStatement_even` — the even exponents `2k₀`, `k₀ ≥ 2`.  This is exactly
    `[MSZ3, Theorem 2.1]` specialised to one dimension, and it is the *only* deep missing input;
  * `IWLqBound_dualEven` — the dual-even exponents `(2k₀)'`.  These are **reduced to the even case
    here**: `IWLqBound_of_dual` (`Dual.lean`) transfers a bound at `q` to a bound at the Hölder
    dual `q'` for the *conjugate* symbol, so the even case applied to `star ∘ φ` yields the
    dual-even case for `φ` (the periodisation commutes with conjugation).  The only ingredient of
    that reduction which is not formalised here is the identification
    `‖T_{star φ}‖_{L^{2k₀}} = ‖T_φ‖_{L^{(2k₀)'}}` of the *continuous* multiplier norms — the `L^p`
    duality of the adjoint of `T_φ`, which concerns `IsLqMultiplierBound` and not the discrete
    multiplier;
* the passage from the exponents in `2ℕ ∪ (2ℕ)'` to *all* `1 < q < ∞` is the routine
  Riesz–Thorin interpolation step, **proved here** as `IWLqBound_interpolation` (in
  `IWLqBound_interpolation.lean`, together with the vector-valued three-lines machinery of
  `VecDefs.lean`); its statement is recorded below as
  `IWLqBound_interpolation_statement` for comparison with the residual estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal FourierTransform
open MeasureTheory

namespace Work.Analysis.IWMultiplier

open Work.Analysis.IonescuWainger

/-- `IWLqBound` is monotone in the constant. -/
theorem IWLqBound.mono {A : Finset Circle} {Φ : Circle → ℂ} {q : ℝ≥0∞} {C C' : NNReal}
    (h : IWLqBound A Φ q C) (hCC' : C ≤ C') : IWLqBound A Φ q C' := by
  intro H _ _ _ f hf
  refine le_trans (h H f hf) ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hCC')

/-- The set of exponents for which the multiplier bound of Theorem `thm:iw` has to be proved is
exactly `2ℕ ∪ (2ℕ)'`: an exponent `q` is covered by the two `even`/`dualEven` alternatives. -/
theorem isEvenOrDualEven_iff_even_or_dual (q : ℝ≥0∞) : IsEvenOrDualEven q ↔
    (∃ k : ℕ, 1 ≤ k ∧ q = ((2 * k : ℕ) : ℝ≥0∞)) ∨
      (∃ k : ℕ, 1 ≤ k ∧ q = ENNReal.ofReal ((2 * (k : ℝ)) / (2 * (k : ℝ) - 1))) :=
  Iff.rfl

/-- **The residual estimate (even exponents).**  This is the `q ∈ 2ℕ`, `q ≥ 4` case of the
multiplier half of Theorem `thm:iw`; in the paper it is `[MSZ3, Theorem 2.1]` specialised to one
dimension.  It is the *only* missing input of Theorem `thm:iw` in the even case. -/
def IWMultiplierBoundStatement_even : Prop :=
  ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧
    (∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → NonAliasing k (iwArithFreqs ρ l)) ∧
    ∀ (k₀ : ℕ), 2 ≤ k₀ → ∃ C : ℝ≥0, 0 < C ∧
      ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k →
      ∀ (φ : SchwartzMap ℝ ℂ), (∀ x, φ x ≠ 0 → x ∈ realArc k) →
      ∀ (M : ℝ≥0), IsLqMultiplierBound ((2 * k₀ : ℕ) : ℝ≥0∞) (φ : ℝ → ℂ) M →
        IWLqBound (iwArithFreqs ρ l) (periodize (φ : ℝ → ℂ)) ((2 * k₀ : ℕ) : ℝ≥0∞)
          (C * angleBracket l * M)

/-- **The dual-even exponents of the multiplier half of Theorem `thm:iw`.**  These follow from the
even case `IWMultiplierBoundStatement_even` applied to the *conjugate* symbol, by the duality
transfer `IWLqBound_of_dual` (proved in `Dual.lean`): if `φ` is Schwartz then so is `star ∘ φ`, the
periodisations satisfy `star ∘ periodize (star ∘ φ) = periodize φ`, and the constants match because
the adjoint of the continuous multiplier `T_φ` is `T_{star φ}`, so
`‖T_{star φ}‖_{L^{2k} → L^{2k}} = ‖T_φ‖_{L^{(2k)'} → L^{(2k)'}}`.

The only ingredient of that reduction which is *not* formalised here is the identification
`‖T_{star φ}‖_{L^{2k}} = ‖T_φ‖_{L^{q'}}` for the continuous multiplier on `ℝ` (the `L^p` duality of
the adjoint), which concerns `IsLqMultiplierBound` rather than the discrete multiplier. -/
def IWLqBound_dualEven : Prop :=
  ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧
    (∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → NonAliasing k (iwArithFreqs ρ l)) ∧
    ∀ (k₀ : ℕ), 2 ≤ k₀ → ∃ C : ℝ≥0, 0 < C ∧
      ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k →
      ∀ (φ : SchwartzMap ℝ ℂ), (∀ x, φ x ≠ 0 → x ∈ realArc k) →
      ∀ (M : ℝ≥0),
        IsLqMultiplierBound (ENNReal.ofReal ((2 * (k₀ : ℝ)) / (2 * (k₀ : ℝ) - 1)))
          (φ : ℝ → ℂ) M →
        IWLqBound (iwArithFreqs ρ l) (periodize (φ : ℝ → ℂ))
          (ENNReal.ofReal ((2 * (k₀ : ℝ)) / (2 * (k₀ : ℝ) - 1))) (C * angleBracket l * M)

/-- **The interpolation reduction.**  Riesz–Thorin convexity for the IW multiplier: a bound at the
two exponents `q₀, q₁` implies the bound at every intermediate exponent, with the interpolated
constant.  This is the formal content of Remark `rem:1`(iv) of the paper ("*by applying
(iw-mult) for `q ∈ 2ℕ ∪ (2ℕ)'` and then interpolating we can recover good bounds for all
`1 < q < ∞`"): combined with the theorem at even (and dual-even) exponents, it yields the bound at
every `1 < q < ∞`.

The proof is the usual complex-interpolation argument for a linear operator (here convolution with
a fixed kernel) on the scale of `ℓ^q` spaces; the finitely-supported formulation of `IWLqBound`
means that only finitely supported test functions are ever fed to the hypotheses. -/
def IWLqBound_interpolation_statement : Prop :=
  ∀ (A : Finset Circle) (Φ : Circle → ℂ) (q q₀ q₁ : ℝ≥0∞) (C₀ C₁ : NNReal) (θ : ℝ),
    IWLqBound A Φ q₀ C₀ → IWLqBound A Φ q₁ C₁ → 0 ≤ θ → θ ≤ 1 →
    1 ≤ q₀.toReal → 1 ≤ q₁.toReal →
    (q.toReal)⁻¹ = (1 - θ) * (q₀.toReal)⁻¹ + θ * (q₁.toReal)⁻¹ →
    IWLqBound A Φ q (C₀ ^ (1 - θ) * C₁ ^ θ)

/-- **The `L^p` duality of the adjoint continuous multiplier.**  The adjoint of `T_φ` is
`T_{star φ}` (multiplication by the conjugate symbol on the Fourier side), and the operator norm of
the adjoint on `L^p` equals the norm of the operator on the Hölder dual `L^{p'}`.  In the language
of `IsLqMultiplierBound`, a bound at the exponent `p'` for `φ` is therefore a bound at `p` for the
conjugate symbol `star ∘ φ`.

This is the ingredient which, together with the proved discrete duality `IWLqBound_of_dual`, turns
the even-exponent case of `thm:iw` into the dual-even case in the exact hypothesis form of
`IWMultiplierBoundStatement` (rather than the conjugate-symbol form used in the reduction described
in the docstring of `IWLqBound_dualEven`).  It is not formalised here: it is an `L^p`-duality
statement about the *continuous* multiplier and does not involve the Ionescu–Wainger arithmetic at
all. -/
def IsLqMultiplierBound_conj_dual_statement : Prop :=
  ∀ (p p' : ℝ), p.HolderConjugate p' → ∀ (φ : ℝ → ℂ) (M : NNReal),
    IsLqMultiplierBound (ENNReal.ofReal p') φ M →
      IsLqMultiplierBound (ENNReal.ofReal p) (fun x => star (φ x)) M

/-- **The reverse half of the `L²(ℝ)` multiplier norm computation.**  The `q = 2` case of the
conclusion of `IWMultiplierBoundStatement` is proved here from the *pointwise* sup-norm bound
`∀ x, ‖φ x‖ ≤ M` of the symbol (`IWMultiplierBound_q2_vector`), which is how the bound enters the
proof through `norm_iwOpSet_le`.  The paper's hypothesis is instead
`IsLqMultiplierBound 2 φ M`.  The two are equivalent because the `L²` multiplier norm of `φ` is
`‖φ‖_∞` — the forward direction is `isLqMultiplierBound_two` (proved), and the statement below
records the reverse direction, namely that a bound on the `L²` multiplier norm is a bound on the
symbol.  It is the standard fact that the operator norm of a multiplication operator on `L²` is the
essential supremum of its symbol (together with `sup = essSup` for a continuous symbol), and it is
not formalised here. -/
def IsLqMultiplierBound_two_pointwise : Prop :=
  ∀ (φ : ℝ → ℂ) (M : NNReal), Continuous φ → IsLqMultiplierBound 2 φ M → ∀ x, ‖φ x‖ ≤ M

/-- The interpolation reduction is *proved*: `IWLqBound_interpolation` of
`IWLqBound_interpolation.lean` has exactly this statement. -/
theorem IWLqBound_interpolation_statement_holds : IWLqBound_interpolation_statement :=
  fun A Φ q q₀ q₁ C₀ C₁ θ h0 h1 hθ0 hθ1 hq₀ hq₁ hq =>
    IWLqBound_interpolation A Φ h0 h1 hθ0 hθ1 hq₀ hq₁ hq

/-- The `q = 2` instance of the multiplier half of Theorem `thm:iw` is exactly the case
`q = 2` of `IWMultiplierBoundStatement`, and it is *proved* here.  This lemma records the
implication in the direction needed for the comparison with the residual estimate: the `q = 2`
case of the multiplier bound does not need any super-orthogonality input. -/
theorem IWMultiplierBoundStatement_q2_of_theorem_inputs {ρ Cρ : ℝ} (hρ : 0 < ρ) (hCρ : 2 ≤ Cρ)
    (hNA : ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → NonAliasing k (iwArithFreqs ρ l))
    {l : ℕ} {k : ℤ} (hgood : GoodMajorArcs ρ Cρ l k)
    {φ : ℝ → ℂ} (hφm : Measurable φ) (hφ : ∀ x, φ x ≠ 0 → x ∈ realArc k)
    (hsum : ∀ x, Summable fun j : ℤ => φ (x + j)) {M : NNReal}
    (hM : ∀ x, ‖φ x‖ ≤ (M : ℝ)) :
    IWLqBound (iwArithFreqs ρ l) (periodize φ) 2 (angleBracket l * M) :=
  IWMultiplierBound_q2_vector hρ hCρ hNA hgood hφm hφ hsum hM

end Work.Analysis.IWMultiplier
