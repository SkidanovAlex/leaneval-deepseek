import Mathlib
import Submission.Work.HP.DyadicR2Defs

/-!
# The fibre sum of powers of four over `dFib`, bounded by `X²`

`dFib s X Y = {a ≤ s + 1 : a ≤ s - a ∧ 2 ^ a ≤ 2 * X ∧ 2 ^ (s - a) ≤ 2 * Y}`.
Every `a` in the fibre satisfies `2 ^ a ≤ 2 * X`, so `4 ^ a = (2 ^ a) ^ 2 ≤ 4 * X ^ 2`.
Summing over the initial segment up to the largest element of the fibre gives at most
`(4 / 3) * 4 ^ A ≤ (4 / 3) * 4 * X ^ 2 = (16 / 3) * X ^ 2`.
-/

namespace Work.HP.DyadicAux

theorem dFib_four_X (s : ℕ) (X Y : ℝ) :
    ∑ a ∈ dFib s X Y, (4 : ℝ) ^ a ≤ (16 / 3) * X ^ 2 := by
  rcases Finset.eq_empty_or_nonempty (dFib s X Y) with h | h
  · rw [h, Finset.sum_empty]; positivity
  · set A := (dFib s X Y).max' h with hAdef
    have hAmem : A ∈ dFib s X Y := Finset.max'_mem _ h
    have hAle : ∀ a ∈ dFib s X Y, a ≤ A := fun a ha => Finset.le_max' _ _ ha
    have hsub : dFib s X Y ⊆ Finset.range (A + 1) := fun a ha =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (hAle a ha))
    have h1 : ∑ a ∈ dFib s X Y, (4 : ℝ) ^ a ≤ ∑ a ∈ Finset.range (A + 1), (4 : ℝ) ^ a :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by positivity)
    have h2 : ∑ a ∈ Finset.range (A + 1), (4 : ℝ) ^ a ≤ (4 / 3) * (4 : ℝ) ^ A := by
      have hg : ∑ a ∈ Finset.range (A + 1), (4 : ℝ) ^ a = ((4 : ℝ) ^ (A + 1) - 1) / 3 := by
        rw [geom_sum_eq (by norm_num : (4 : ℝ) ≠ 1)]
        norm_num
      rw [hg, div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) (A + 1), pow_succ (4 : ℝ) A]
    have hAcond := (Finset.mem_filter.mp hAmem).2
    have h2A : (2 : ℝ) ^ A ≤ 2 * X := hAcond.2.1
    have h3 : (4 : ℝ) ^ A ≤ 4 * X ^ 2 := by
      have h4 : (4 : ℝ) ^ A = ((2 : ℝ) ^ A) ^ 2 := by
        calc (4 : ℝ) ^ A = ((2 : ℝ) ^ 2) ^ A := by
              rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
          _ = ((2 : ℝ) ^ A) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]
      rw [h4]
      have h5 : ((2 : ℝ) ^ A) ^ 2 ≤ (2 * X) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2A 2
      nlinarith [h5]
    linarith

end Work.HP.DyadicAux
