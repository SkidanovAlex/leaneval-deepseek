import Mathlib
import Submission.Work.BourgainPlan.Maximal.hlMaxTwoGrid
import Submission.Work.BourgainPlan.Maximal.dyadicMaximal

/-!
# The dyadic maximal function is dominated by two half-shifted dyadic grids

For every `φ : ℝ → ℝ≥0∞` and every `x : ℝ`,

`dyMax φ x ≤ 2 · dyMaxShift (1/2) φ x`.

The point is that the (unshifted) dyadic cell `C = [k·2^n, (k+1)·2^n)` containing `x` is always
contained in a *single* cell of the grid shifted by half a cell length at level `n+1`:

* if `k = 2m` is even, `C ⊆ [(2m-1)·2^n, (2m+1)·2^n) = dyCellShift (1/2) (n+1) (m-1)`;
* if `k = 2m+1` is odd, `C ⊆ [(2m+1)·2^n, (2m+3)·2^n) = dyCellShift (1/2) (n+1) m`.

That shifted cell has twice the length of `C` and still contains `x`, which yields the factor `2`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- `2^(n+1) = 2 · 2^n`. -/
lemma two_zpow_succ (n : ℤ) : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by
  rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring

/-- Every dyadic cell of level `n` is contained in a single cell of the grid shifted by half a
cell length at level `n+1`. -/
lemma dyCell_subset_dyCellShift (n k : ℤ) :
    ∃ j : ℤ, dyCell n k ⊆ dyCellShift (1 / 2) (n + 1) j := by
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · -- `k = 2m`, take `j = m - 1`
    refine ⟨m - 1, ?_⟩
    intro y hy
    have hk : (k : ℝ) = 2 * (m : ℝ) := by rw [hm]; push_cast; ring
    simp only [dyCell, dyCellShift, Set.mem_Ico] at hy ⊢
    rw [hk] at hy
    rw [two_zpow_succ n]
    constructor
    · push_cast
      nlinarith [hy.1, zpow_two_pos n]
    · push_cast
      nlinarith [hy.2]
  · -- `k = 2m + 1`, take `j = m`
    refine ⟨m, ?_⟩
    intro y hy
    have hk : (k : ℝ) = 2 * (m : ℝ) + 1 := by rw [hm]; push_cast; ring
    simp only [dyCell, dyCellShift, Set.mem_Ico] at hy ⊢
    rw [hk] at hy
    rw [two_zpow_succ n]
    constructor
    · push_cast
      nlinarith [hy.1]
    · push_cast
      nlinarith [hy.2, zpow_two_pos n]

/-- `ofReal (2^n)⁻¹ = 2 · ofReal (2^(n+1))⁻¹`. -/
lemma ofReal_inv_two_zpow (n : ℤ) :
    ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹) = 2 * ENNReal.ofReal (((2 : ℝ) ^ (n + 1))⁻¹) := by
  have hreal : (((2 : ℝ) ^ n)⁻¹) = 2 * (((2 : ℝ) ^ (n + 1))⁻¹) := by
    rw [two_zpow_succ n, mul_inv]; ring
  rw [hreal, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simp

theorem dyMax_le_two_dyMaxShift (φ : ℝ → ENNReal) (x : ℝ) :
    Work.BourgainPlan.Maximal.dyMax φ x ≤ 2 * Work.BourgainPlan.Maximal.dyMaxShift (1 / 2) φ x := by
  unfold dyMax
  refine iSup_le fun n => iSup_le fun k => iSup_le fun hx => ?_
  obtain ⟨j, hsub⟩ := dyCell_subset_dyCellShift n k
  have hmem : x ∈ dyCellShift (1 / 2) (n + 1) j := hsub hx
  have hInt : ∫⁻ y in dyCell n k, φ y ≤ ∫⁻ y in dyCellShift (1 / 2) (n + 1) j, φ y :=
    lintegral_mono_set hsub
  have hweight := ofReal_inv_two_zpow n
  calc ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹) * ∫⁻ y in dyCell n k, φ y
      ≤ ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹) * ∫⁻ y in dyCellShift (1 / 2) (n + 1) j, φ y :=
        mul_le_mul_right hInt _
    _ = 2 * (ENNReal.ofReal (((2 : ℝ) ^ (n + 1))⁻¹)
          * ∫⁻ y in dyCellShift (1 / 2) (n + 1) j, φ y) := by
        rw [hweight, mul_assoc]
    _ ≤ 2 * dyMaxShift (1 / 2) φ x := by
        refine mul_le_mul_right ?_ 2
        exact le_iSup_of_le (n + 1) (le_iSup_of_le j (le_iSup_of_le hmem le_rfl))

end Work.BourgainPlan.Maximal
