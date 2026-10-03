/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Analysis.IWMultiplier.Basic
import Submission.Work.Analysis.IWMultiplier.NonAliasing
import Submission.Work.Analysis.IWMultiplier.isLqMultiplierBound_two

/-!
# The `q = 2` case of the vector-valued Ionescu–Wainger multiplier theorem

This file derives, from the `ℓ²` bound `Work.Analysis.IonescuWainger.norm_iwOpSet_le` of the
Ionescu–Wainger API (which is the `q = 2` case of Theorem `thm:iw`), the exact `q = 2` instance of
the statement `Work.Analysis.IWMultiplier.IWMultiplierBoundStatement`:

for good major arcs `(l,k)`, a symbol `φ` supported in `ℝ_{≤k}` and bounded by `M`, the IW
multiplier with symbol `periodize φ` is bounded on `ℓ²(ℤ;ℂ)` by `⟨l⟩ · M` — where the factor `M`
encodes the continuous `L²(ℝ)` multiplier norm `‖T_φ‖_{L²→L²} = ‖φ‖_∞` of Theorem `thm:iw`
(cf. `isLqMultiplierBound_two`, which identifies the optimal such `M`).

The proof combines four ingredients:

* `work.Analysis.IonescuWainger.norm_iwOpSet_le` — the `ℓ²` operator bound by the sup norm of the
  IW symbol, under non-aliasing (this is the only `q = 2`-specific input);
* `iwNonAliasing_of_goodMajorArcsConstant` (from the API module) — good major arcs imply
  non-aliasing;
* `periodize_norm_le` — the periodisation does not increase the sup norm, because the arc has
  length `< 1` (`two_pow_succ_lt_one_of_goodMajorArcs`);
* `IWLqBoundScalar_of_norm_le` — the identification of the `ℓ²` multiplier with the convolution
  form used in the `ℓ^q` statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal FourierTransform
open MeasureTheory

namespace Work.Analysis.IWMultiplier

open Work.Analysis.IonescuWainger

/-- **The `q = 2` case of the multiplier half of Theorem `thm:iw`** (Krause–Mirek–Tao,
Appendix `iw-app`), in the shape of the statement `IWLqBoundScalar`.  For `ρ > 0`, a
good-major-arcs constant `Cρ ≥ 2` and a pair `(l,k)` with `GoodMajorArcs ρ Cρ l k`, every symbol
`φ` supported in `ℝ_{≤k}` and bounded by `M` has its Ionescu–Wainger projection `T^{≤l}_φ`
bounded on `ℓ²(ℤ)` by `⟨l⟩ M`.  The factor `M` is the continuous `L²(ℝ)` multiplier norm of `φ`
(see `isLqMultiplierBound_two`). -/
theorem IWMultiplierBoundScalar_q2 {ρ Cρ : ℝ} (hρ : 0 < ρ) (hCρ : 2 ≤ Cρ)
    (hNA : ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → NonAliasing k (iwArithFreqs ρ l))
    {l : ℕ} {k : ℤ} (hgood : GoodMajorArcs ρ Cρ l k)
    {φ : ℝ → ℂ} (hφm : Measurable φ) (hφ : ∀ x, φ x ≠ 0 → x ∈ realArc k)
    (hsum : ∀ x, Summable fun j : ℤ => φ (x + j))
    {M : NNReal} (hM : ∀ x, ‖φ x‖ ≤ (M : ℝ)) :
    IWLqBoundScalar (iwArithFreqs ρ l) (periodize φ) 2 (angleBracket l * M) := by
  have h2 : (2 : ℝ) ^ (k + 1) < 1 := two_pow_succ_lt_one_of_goodMajorArcs hgood hCρ hρ
  have hΦC : ∀ ξ, ‖periodize φ ξ‖ ≤ (M : ℝ) := periodize_norm_le h2 hφ hM
  have hφ0 : ∀ x, (2 : ℝ) ^ k < |x| → φ x = 0 := by
    intro x hx
    by_contra hne
    have hmem := hφ x hne
    rw [realArc, Set.mem_Icc] at hmem
    have : |x| ≤ (2 : ℝ) ^ k := abs_le.mpr hmem
    linarith
  have hMem : MemLp (periodize φ) ⊤ circleMeasure :=
    memLp_periodize hφm (by positivity) hφ0 hM
  have hMemSym : MemLp (iwSymbolSet (iwArithFreqs ρ l) (periodize φ)) ⊤ circleMeasure :=
    memLp_iwSymbolSet _ hMem
  have hSupp : SupportedInArc k (periodize φ) := supportedInArc_periodize hφ hsum
  have hbnd : ‖iwOpSet (iwArithFreqs ρ l) (periodize φ) hMemSym‖
      ≤ ((angleBracket l * M : NNReal) : ℝ) := by
    refine norm_iwOpSet_le (hNA l k hgood) hSupp (by positivity) (fun ξ => ?_) hMemSym
    rw [NNReal.coe_mul]
    calc ‖periodize φ ξ‖ ≤ (M : ℝ) := hΦC ξ
      _ ≤ (angleBracket l : ℝ) * (M : ℝ) :=
          le_mul_of_one_le_left (by positivity) (by exact_mod_cast one_le_angleBracket l)
  exact IWLqBoundScalar_of_norm_le _ _ hMemSym hbnd

/-- The `q = 2` bound in the vocabulary of the paper's operator `iwOp` (the Ionescu–Wainger
projection `T^{≤l}_φ` as an operator on `ℓ²(ℤ)`): under good major arcs, a symbol supported in
`ℝ_{≤k}` and bounded by `M` gives `‖T^{≤l}_φ‖ ≤ ⟨l⟩ M` on `ℓ²(ℤ)`. -/
theorem IWMultiplierBound_q2_iwOp {ρ Cρ : ℝ} (hρ : 0 < ρ) (hCρ : 2 ≤ Cρ)
    (hNA : ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → NonAliasing k (iwArithFreqs ρ l))
    {l : ℕ} {k : ℤ} (hgood : GoodMajorArcs ρ Cρ l k)
    {φ : ℝ → ℂ} (hφm : Measurable φ) (hφ : ∀ x, φ x ≠ 0 → x ∈ realArc k)
    (hsum : ∀ x, Summable fun j : ℤ => φ (x + j))
    {M : NNReal} (hM : ∀ x, ‖φ x‖ ≤ (M : ℝ))
    (h : MemLp (iwSymbol ρ l (periodize φ)) ⊤ circleMeasure) :
    ‖iwOp ρ l (periodize φ) h‖ ≤ ((angleBracket l * M : NNReal) : ℝ) := by
  have h2 : (2 : ℝ) ^ (k + 1) < 1 := two_pow_succ_lt_one_of_goodMajorArcs hgood hCρ hρ
  have hΦC : ∀ ξ, ‖periodize φ ξ‖ ≤ (M : ℝ) := periodize_norm_le h2 hφ hM
  have hSupp : SupportedInArc k (periodize φ) := supportedInArc_periodize hφ hsum
  refine norm_iwOpSet_le (hNA l k hgood) hSupp (by positivity) (fun ξ => ?_) h
  rw [NNReal.coe_mul]
  calc ‖periodize φ ξ‖ ≤ (M : ℝ) := hΦC ξ
    _ ≤ (angleBracket l : ℝ) * (M : ℝ) :=
        le_mul_of_one_le_left (by positivity) (by exact_mod_cast one_le_angleBracket l)

/-- **The full `q = 2` instance of the statement of Theorem `thm:iw`**: for good major arcs, a
symbol `φ` supported in `ℝ_{≤k}` and bounded by `M`, both the continuous `L²(ℝ)` multiplier bound
`‖T_φ‖_{L²→L²} ≤ M` (the `‖T_Φ‖_{L²→L²} = ‖Φ‖_∞` computation, `IsLqMultiplierBound 2 φ M`) and
the discrete Ionescu–Wainger `ℓ²(ℤ)` bound `‖T^{≤l}_φ‖ ≤ ⟨l⟩ M` hold with the *same* constant. -/
theorem IWMultiplierBoundStatement_q2 {ρ Cρ : ℝ} (hρ : 0 < ρ) (hCρ : 2 ≤ Cρ)
    (hNA : ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → NonAliasing k (iwArithFreqs ρ l))
    {l : ℕ} {k : ℤ} (hgood : GoodMajorArcs ρ Cρ l k)
    {φ : ℝ → ℂ} (hφm : Measurable φ) (hφ : ∀ x, φ x ≠ 0 → x ∈ realArc k)
    (hsum : ∀ x, Summable fun j : ℤ => φ (x + j))
    {M : NNReal} (hM : ∀ x, ‖φ x‖ ≤ (M : ℝ)) :
    IsLqMultiplierBound 2 φ M ∧
      IWLqBoundScalar (iwArithFreqs ρ l) (periodize φ) 2 (angleBracket l * M) :=
  ⟨isLqMultiplierBound_two hM, IWMultiplierBoundScalar_q2 hρ hCρ hNA hgood hφm hφ hsum hM⟩

theorem exists_const_q2 {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ Cρ : ℝ, 2 ≤ Cρ ∧
      (∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → NonAliasing k (iwArithFreqs ρ l)) := by
  obtain ⟨Cρ, -, hNA⟩ := iwNonAliasing_of_goodMajorArcsConstant hρ
  refine ⟨max Cρ 2, le_max_right _ _, fun l k hgood => ?_⟩
  refine hNA l k ?_
  have hS : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) := by positivity
  have hunfold : (k : ℝ) ≤ -(max Cρ 2) * (2 : ℝ) ^ (ρ * (l : ℝ)) := hgood
  have hmul : Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ max Cρ 2 * (2 : ℝ) ^ (ρ * (l : ℝ)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hS
  show (k : ℝ) ≤ -Cρ * (2 : ℝ) ^ (ρ * (l : ℝ))
  linarith

end Work.Analysis.IWMultiplier
