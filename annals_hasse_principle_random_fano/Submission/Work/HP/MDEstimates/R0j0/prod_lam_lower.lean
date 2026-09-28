import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.lam_basic

namespace Work.HP.MDEstimates.R0j0

open Finset

/-- Lower bound for the product of the first `k` successive minima of a rank-`R` integral lattice:
the first `min k j0` factors are at least `2M` (because `2M ≤ lam L 1`) and the remaining
`k - min k j0` factors are at least `2J` (because `2J ≤ lam L (j0+1)` and `lam` is monotone). -/
theorem prod_lam_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (R j0 k : ℕ) (M J : ℝ)
    (hrk : rk L = R) (hM : 0 ≤ M) (hJ : 0 ≤ J)
    (hj0 : j0 ≤ R) (hk : k ≤ R)
    (hM1 : 2 * M ≤ lam L 1) (hJ1 : 2 * J ≤ lam L (j0 + 1)) :
    (2 * M) ^ (min k j0) * (2 * J) ^ (k - min k j0)
      ≤ ∏ i ∈ Finset.range k, lam L (i + 1) := by
  classical
  set a := min k j0 with ha
  have ha_le_k : a ≤ k := by rw [ha]; exact Nat.min_le_left _ _
  have ha_le_j0 : a ≤ j0 := by rw [ha]; exact Nat.min_le_right _ _
  have hM2 : (0 : ℝ) ≤ 2 * M := by linarith
  have hJ2 : (0 : ℝ) ≤ 2 * J := by linarith
  -- Pointwise lower bound on the product by the step function `i ↦ if i < a then 2M else 2J`.
  have hstep :
      ∏ i ∈ Finset.range k, (if i < a then (2 * M : ℝ) else 2 * J)
        ≤ ∏ i ∈ Finset.range k, lam L (i + 1) := by
    apply Finset.prod_le_prod₀
    · intro i _
      by_cases hia : i < a
      · rw [if_pos hia]; exact hM2
      · rw [if_neg hia]; exact hJ2
    · intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      by_cases hia : i < a
      · -- first block: the `i`-th factor dominates `lam L 1 ≥ 2M`
        rw [if_pos hia]
        have hi1R : i + 1 ≤ rk L := by rw [hrk]; omega
        have := lam_mono L (show 1 ≤ i + 1 by omega) hi1R
        linarith
      · -- second block: `a = j0`, so the factor dominates `lam L (j0+1) ≥ 2J`
        rw [if_neg hia]
        have hai : a ≤ i := Nat.le_of_not_lt hia
        have hak : a = j0 := by
          rcases le_total k j0 with hkj | hjk
          · have hk_eq : a = k := ha.trans (Nat.min_eq_left hkj)
            exfalso; omega
          · exact ha.trans (Nat.min_eq_right hjk)
        have hj0i : j0 + 1 ≤ i + 1 := by omega
        have hi1R : i + 1 ≤ rk L := by rw [hrk]; omega
        have := lam_mono L hj0i hi1R
        linarith
  -- Compute the product of the step function.
  have hprodval :
      ∏ i ∈ Finset.range k, (if i < a then (2 * M : ℝ) else 2 * J)
        = (2 * M) ^ a * (2 * J) ^ (k - a) := by
    have hsplit : Finset.range k = Finset.range a ∪ (Finset.range k \ Finset.range a) := by
      rw [Finset.union_sdiff_of_subset (Finset.range_subset_range.mpr ha_le_k)]
    rw [hsplit, Finset.prod_union Finset.disjoint_sdiff]
    have h1 : ∏ i ∈ Finset.range a, (if i < a then (2 * M : ℝ) else 2 * J)
        = (2 * M) ^ a := by
      have hc : ∀ i ∈ Finset.range a, (if i < a then (2 * M : ℝ) else 2 * J) = 2 * M :=
        fun i hi => if_pos (Finset.mem_range.mp hi)
      rw [Finset.prod_congr rfl hc, Finset.prod_const, Finset.card_range]
    have h2 : ∏ i ∈ Finset.range k \ Finset.range a,
        (if i < a then (2 * M : ℝ) else 2 * J) = (2 * J) ^ (k - a) := by
      have hc : ∀ i ∈ Finset.range k \ Finset.range a,
          (if i < a then (2 * M : ℝ) else 2 * J) = 2 * J := by
        intro i hi
        rw [Finset.mem_sdiff, Finset.mem_range] at hi
        exact if_neg (fun h => hi.2 (Finset.mem_range.mpr h))
      rw [Finset.prod_congr rfl hc, Finset.prod_const,
        Finset.card_sdiff_of_subset (Finset.range_subset_range.mpr ha_le_k)]
      simp [Finset.card_range]
    rw [h1, h2]
  rw [← hprodval]
  exact hstep

end Work.HP.MDEstimates.R0j0
