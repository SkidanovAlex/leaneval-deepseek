import Submission.Vinogradov.ChallengeDeps
import Submission.Vinogradov.Core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.NumberTheory.VinogradovMeanValue
open scoped BigOperators

set_option autoImplicit false

namespace Submission.Vinogradov

noncomputable section
open Classical

/-- The comparison function in the statement of the Vinogradov mean value theorem:
`X ↦ X^(s+ε) + X^(2s - k(k+1)/2 + ε)`. -/
def rhs (s k : ℕ) (ε : ℝ) (X : ℕ) : ℝ :=
  (X : ℝ) ^ (s + ε) + (X : ℝ) ^ ((2 * s : ℝ) - (k * (k + 1) : ℝ) / 2 + ε)

/-- The target asymptotic statement, bundled. -/
def VMVT (s k : ℕ) (ε : ℝ) (hε : 0 < ε) : Prop :=
  J s k =O[Filter.atTop] rhs s k ε

/-- `rhs` is nonnegative for nonnegative bases. -/
lemma rhs_nonneg (s k : ℕ) (ε : ℝ) (X : ℕ) : 0 ≤ rhs s k ε X := by
  dsimp [rhs]
  exact add_nonneg (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le X) _)
    (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le X) _)

/-- `rhs` is at least `X^(s+ε)`. -/
lemma rhs_ge_first (s k : ℕ) (ε : ℝ) (X : ℕ) : (X : ℝ) ^ (s + ε) ≤ rhs s k ε X := by
  dsimp [rhs]
  exact le_add_of_nonneg_right (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le X) _)

/-- `rhs` is at least `X^(2s - k(k+1)/2 + ε)`. -/
lemma rhs_ge_second (s k : ℕ) (ε : ℝ) (X : ℕ) : (X : ℝ) ^ ((2 * s : ℝ) - (k * (k + 1) : ℝ) / 2 + ε) ≤ rhs s k ε X := by
  dsimp [rhs]
  exact le_add_of_nonneg_left (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le X) _)

/-- An eventual pointwise bound with a constant implies the big-O statement. -/
lemma isBigO_of_eventually_bound (s k : ℕ) (ε : ℝ) (hε : 0 < ε) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ᶠ X : ℕ in Filter.atTop, J s k X ≤ C * rhs s k ε X) :
    J s k =O[Filter.atTop] rhs s k ε := by
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [h] with X hX
  have hJ : 0 ≤ J s k X := J_nonneg s k X
  have hR : 0 ≤ rhs s k ε X := rhs_nonneg s k ε X
  rw [Real.norm_of_nonneg hJ, Real.norm_of_nonneg hR]
  exact hX

/-- Version of the pointwise bound lemma phrased with `∃ C` and an absolute bound. -/
lemma vmvt_of_eventually_le_mul (s k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (h : ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in Filter.atTop, J s k X ≤ C * rhs s k ε X) : VMVT s k ε hε := by
  rcases h with ⟨C, hC, hb⟩
  exact isBigO_of_eventually_bound s k ε hε C (le_of_lt hC) hb

/-- To prove the bound it suffices to show `J s k X ≤ C` times the first summand `X^(s+ε)`
eventually (the second summand is nonnegative). -/
lemma vmvt_of_eventually_le_first (s k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (h : ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in Filter.atTop, J s k X ≤ C * (X : ℝ) ^ (s + ε)) :
    VMVT s k ε hε := by
  rcases h with ⟨C, hC, hb⟩
  apply vmvt_of_eventually_le_mul s k ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with X hX
  exact hX.trans (mul_le_mul_of_nonneg_left (rhs_ge_first s k ε X) (le_of_lt hC))

/-- Variant: prove the bound via the second summand `X^(2s - k(k+1)/2 + ε)`. -/
lemma vmvt_of_eventually_le_second (s k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (h : ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in Filter.atTop,
      J s k X ≤ C * (X : ℝ) ^ ((2 * s : ℝ) - (k * (k + 1) : ℝ) / 2 + ε)) :
    VMVT s k ε hε := by
  rcases h with ⟨C, hC, hb⟩
  apply vmvt_of_eventually_le_mul s k ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with X hX
  exact hX.trans (mul_le_mul_of_nonneg_left (rhs_ge_second s k ε X) (le_of_lt hC))

end
end Submission.Vinogradov
