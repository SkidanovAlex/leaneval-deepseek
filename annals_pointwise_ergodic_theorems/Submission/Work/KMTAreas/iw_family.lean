/-
Area A1 (`Work.KMTAreas.area_A1`) — the reduction of the frozen contract's area A1 to the
Ionescu–Wainger multiplier theorem of Mirek–Stein–Zorin-Kranich (MSZ3, Theorem 2.1) in the
form in which the KMT paper cites it (Appendix `iw-app`), i.e. Tao's "main theorem for narrow
symbols" (arXiv:2008.05066, Theorem 1.2) specialised to an even exponent.

## What is proved here

`Work.Analysis.IWMultiplier.IWMultiplierBoundStatement_even` has two conjuncts for each `ρ`:

1. *non-aliasing*: good major arcs do not alias `(ℚ/ℤ)_{≤l} = iwArithFreqs ρ l`.  This is
   **proved** in the workspace (`exists_goodMajorArcs_nonAliasing`, re-exported as
   `iwNonAliasing_of_goodMajorArcsConstant`);
2. *multiplier bound*: for even `q = 2k₀`, `k₀ ≥ 2`, `‖T^{≤l}_φ‖_{ℓ^q(ℤ;H)} ≲ ⟨l⟩ ‖T_φ‖_{L^q(ℝ)}`.

Only (2) is missing: it is `[MSZ3, Theorem 2.1]`, the deep super-orthogonality input, recorded in
`Submission/Work/Analysis/IWMultiplier/Gap.lean` as the residual estimate.

This file isolates (2) as the `Prop` `IWEvenMultiplierGap` and proves that
`IWEvenMultiplierGap` implies the frozen contract's `AreaA1`, using the proved non-aliasing
conjunct for the first half and a comparison of the constants `Cρ` for the second.

`Submission/Work/KMTAreas/A1_STATUS.md` states exactly what is needed from outside this workspace
(the closure of MSZ3 Theorem 2.1 / Tao's narrow-symbol main theorem) and the two equivalent
interfaces in which it may be delivered.
-/
import Mathlib
import Submission.Work.KMTContract.Areas

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal
open MeasureTheory

namespace Work.KMTAreas

open Work.Analysis.IWMultiplier
open Work.Analysis.IonescuWainger

/-- The frequency set `U(P) = R(P)` attached to a finite set `P` of denominators: the reduced
fractions with denominator in `P`, realised as `⋃_{q ∈ P} {a/q : 0 ≤ a < q}`.  For the IW
denominator set `P = iwP ρ l` this is exactly the paper's `(ℚ/ℤ)_{≤l} = iwArithFreqs ρ l`. -/
noncomputable def iwDenomFreqs (P : Finset ℕ) : Finset Work.Analysis.IonescuWainger.Circle :=
  P.biUnion (fun q => (Finset.range q).image
    (fun a : ℕ => ((a : ℝ) / (q : ℝ) : Work.Analysis.IonescuWainger.Circle)))

/-- `(ℚ/ℤ)_{≤l}` is the frequency set of the denominator set `P_{≤l}`. -/
theorem iwArithFreqs_eq_iwDenomFreqs (ρ : ℝ) (l : ℕ) :
    iwArithFreqs ρ l = iwDenomFreqs (iwP ρ l) := rfl

/-- Membership in `iwDenomFreqs P`: `α` is a frequency killed by some positive denominator
`q ∈ P`; this is the general form of `mem_iwArithFreqs`. -/
theorem mem_iwDenomFreqs {P : Finset ℕ} {α : Work.Analysis.IonescuWainger.Circle} :
    α ∈ iwDenomFreqs P ↔ ∃ q ∈ P, 1 ≤ q ∧ q • α = 0 := by
  rw [iwDenomFreqs, Finset.mem_biUnion]
  constructor
  · rintro ⟨q, hq, hα⟩
    rw [Finset.mem_image] at hα
    obtain ⟨a, ha, rfl⟩ := hα
    have hq1 : 1 ≤ q := by
      have : a < q := Finset.mem_range.mp ha
      omega
    exact ⟨q, hq, hq1, nsmul_div_eq_zero (Nat.pos_of_ne_zero (by omega))⟩
  · rintro ⟨q, hq, hq1, hα⟩
    exact ⟨q, hq, Finset.mem_image.mpr
      (eq_div_of_nsmul_eq_zero (Nat.pos_of_ne_zero (by omega)) hα)⟩

/-- `iwDenomFreqs` is monotone in the denominator set. -/
theorem iwDenomFreqs_mono {P P' : Finset ℕ} (h : P ⊆ P') :
    iwDenomFreqs P ⊆ iwDenomFreqs P' := by
  intro α hα
  rw [mem_iwDenomFreqs] at hα ⊢
  obtain ⟨q, hq, hq1, hqα⟩ := hα
  exact ⟨q, h hq, hq1, hqα⟩

/-- `GoodMajorArcs` is monotone in the constant `Cρ`: a larger constant makes the hypothesis
`k ≤ -Cρ 2^{ρl}` *stronger*, so it implies the version with a smaller constant. -/
theorem GoodMajorArcs.mono_const {ρ C C' : ℝ} (h : C ≤ C') {l : ℕ} {k : ℤ}
    (hk : GoodMajorArcs ρ C' l k) : GoodMajorArcs ρ C l k := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (ρ * (l : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have : C * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ C' * (2 : ℝ) ^ (ρ * (l : ℝ)) :=
    mul_le_mul_of_nonneg_right h hpow.le
  exact le_trans hk (by linarith)

/-- **The residual input of Area A1** (MSZ3 Theorem 2.1, one-dimensional case, even exponents):
the multiplier half of `IWMultiplierBoundStatement_even`, i.e. the second conjunct, without the
non-aliasing conjunct (which is already proved in the workspace).

For every `ρ ∈ (0,1]` there is `Cρ > 0` such that for every even exponent `q = 2k₀ ≥ 4` there is
`C > 0` with

`‖T^{≤l}_φ f‖_{ℓ^{q}(ℤ;H)} ≤ C ⟨l⟩ M ‖f‖_{ℓ^{q}(ℤ;H)}`

whenever `(l,k)` has good major arcs, `φ ∈ Schwartz(ℝ_{≤k})` and `M` bounds the continuous
multiplier `T_φ` on `L^q(ℝ)`.  The IW multiplier `T^{≤l}_φ` is `iwConv (iwArithFreqs ρ l)
(periodize φ)`, and the bound is required uniformly over all finite dimensional Hilbert spaces
`H`. -/
def IWEvenMultiplierGap : Prop :=
  ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧
    ∀ (k₀ : ℕ), 2 ≤ k₀ → ∃ C : ℝ≥0, 0 < C ∧
      ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k →
      ∀ (φ : SchwartzMap ℝ ℂ), (∀ x, φ x ≠ 0 → x ∈ realArc k) →
      ∀ (M : ℝ≥0), IsLqMultiplierBound ((2 * k₀ : ℕ) : ℝ≥0∞) (φ : ℝ → ℂ) M →
        IWLqBound (iwArithFreqs ρ l) (periodize (φ : ℝ → ℂ)) ((2 * k₀ : ℕ) : ℝ≥0∞)
          (C * angleBracket l * M)

/-- **Area A1 from the residual input.**  The non-aliasing half of
`IWMultiplierBoundStatement_even` is proved in the workspace for some constant `Cρ`; the
multiplier half is `IWEvenMultiplierGap`.  Taking the maximum of the two constants gives the
frozen contract's `AreaA1`. -/
theorem areaA1_of_IWEvenMultiplierGap (h : IWEvenMultiplierGap) :
    Work.KMTContract.AreaA1 := by
  rw [Work.KMTContract.areaA1_iff]
  intro ρ hρ hρ1
  obtain ⟨Cρ₁, hCρ₁, hgap⟩ := h ρ hρ hρ1
  obtain ⟨Cρ₂, hCρ₂, hNA⟩ := exists_goodMajorArcs_nonAliasing hρ
  refine ⟨max Cρ₁ Cρ₂, lt_max_of_lt_left hCρ₁, ?_, ?_⟩
  · intro l k hk
    exact hNA l k (GoodMajorArcs.mono_const (le_max_right _ _) hk)
  · intro k₀ hk₀
    obtain ⟨C, hC, hCb⟩ := hgap k₀ hk₀
    exact ⟨C, hC, fun l k hk φ hφ M hM =>
      hCb l k (GoodMajorArcs.mono_const (le_max_left _ _) hk) φ hφ M hM⟩

end Work.KMTAreas
