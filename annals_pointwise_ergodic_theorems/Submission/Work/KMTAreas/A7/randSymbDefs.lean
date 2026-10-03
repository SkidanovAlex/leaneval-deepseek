/-
# Vocabulary for `Work.KMTAreas.A7.randSymb_Tle_f_bound`

The randomised symbol of `Work.KMTAreas.A7.SmallModelDefs`,

  `randSymb φ ε K ξ = ∑_{n < K} ε n * (φ (n+1) ξ - φ n ξ)`,

with the concrete family `φ = smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t` of the small-scale tuple, is a
*finite* linear combination of the Ionescu–Wainger bumps:

  `randSymb (smallSymbF …) ε K = ∑_{m ≤ K} d m * φ_{N_m,t}`,
  `d m = ((ε (m-1) * 1_{m ≤ K} - ε m * 1_{m < K}) * 1_{m ≠ 0 ∧ smallCond … m})`,
  `φ_{N,t}(ξ) = varphiNt ⌊a m⌋ k₁ t ξ`.

The two facts about the coefficients that the analysis of the symbol uses are

* `‖d m‖ ≤ 2` (`norm_randCoeff_le`), and
* the *telescoping* of the coefficients over an interval of active indices,
  `‖∑_{m ∈ Icc c e} d m‖ ≤ 3` (`norm_sum_Icc_randCoeff_le`),

which is what makes the symbol bounded (and a Mikhlin multiplier) even when the number of
*lacunary scales* is unbounded.

This module collects the definitions and the elementary algebraic facts; the analysis of the
resulting symbol lives in the companion files.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallModelDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar

/-- **The index condition** of the `m`-th bump of the small-scale family: the family
`smallSymbF` vanishes at `0` and off the small-scale condition `smallCond`. -/
def randAct (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (m : ℕ) : Prop :=
  m ≠ 0 ∧ smallCond ρ C₀ a l₁ l₂ k₁ k₂ m

instance (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ m : ℕ) :
    Decidable (randAct ρ C₀ a l₁ l₂ k₁ k₂ m) := by
  unfold randAct; infer_instance

/-- **The coefficient** of the bump `varphiNt ⌊a m⌋ k₁ t` in `randSymb (smallSymbF …) ε K`. -/
noncomputable def randCoeff (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (ε : ℕ → ℂ)
    (K m : ℕ) : ℂ :=
  if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then
    (ε (m - 1) * (if m ≤ K then 1 else 0) - ε m * (if m < K then 1 else 0))
  else 0

/-- The family `smallSymbF` is the bump times the indicator of `randAct`. -/
theorem smallSymbF_apply (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (m : ℕ) :
    smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t m =
      (if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then varphiNt (Nat.floor (a m)) k₁ t else 0) := by
  funext ξ
  unfold smallSymbF randAct
  by_cases h0 : m = 0
  · subst h0; simp
  · by_cases hc : smallCond ρ C₀ a l₁ l₂ k₁ k₂ m <;> simp [h0, hc]

end

end Work.KMTAreas.A7
