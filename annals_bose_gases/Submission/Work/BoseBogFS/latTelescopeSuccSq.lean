import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- The partial sums of `∑_{n ≥ 1} 1/n²` are bounded by `2`.

For `i ≥ 0` the `(i+1)`-st term is dominated by the telescoping difference
`1/(i+1) - 1/(i+2) = 1/((i+1)(i+2)) ≥ 1/(i+2)²`; the leading `j = 0` term is `1`.
Summing the telescope gives `1 + (1 - 1/(K+1)) ≤ 2`. -/
theorem latTelescopeSuccSq (J : ℕ) :
    (∑ j ∈ Finset.range J, 1 / ((j : ℝ) + 1) ^ 2) ≤ 2 := by
  rcases Nat.eq_zero_or_pos J with h0 | hpos
  · subst h0
    simp
  · obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have hshift : ∀ i : ℕ, (((i + 1 : ℕ) : ℝ) + 1) = (i : ℝ) + 2 := by
      intro i; push_cast; ring
    have hterm : ∀ i : ℕ,
        1 / (((i + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
          1 / ((i : ℝ) + 1) - 1 / (((i + 1 : ℕ) : ℝ) + 1) := by
      intro i
      simp only [hshift]
      have hkey : 1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2) - 1 / ((i : ℝ) + 2) ^ 2
          = 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2) ^ 2) := by
        field_simp
        ring
      have hnn : 0 ≤ 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2) ^ 2) := by positivity
      linarith
    have hsum : (∑ i ∈ Finset.range K, 1 / (((i + 1 : ℕ) : ℝ) + 1) ^ 2) ≤ 1 := by
      calc (∑ i ∈ Finset.range K, 1 / (((i + 1 : ℕ) : ℝ) + 1) ^ 2)
          ≤ ∑ i ∈ Finset.range K,
              (1 / ((i : ℝ) + 1) - 1 / (((i + 1 : ℕ) : ℝ) + 1)) :=
            Finset.sum_le_sum (fun i _ => hterm i)
        _ = 1 / ((0 : ℝ) + 1) - 1 / ((K : ℝ) + 1) := by
            rw [Finset.sum_range_sub' (fun i : ℕ => 1 / ((i : ℝ) + 1))]
            norm_num
        _ ≤ 1 := by
            rw [show (1 : ℝ) / ((0 : ℝ) + 1) = 1 by norm_num]
            have hK : 0 ≤ 1 / ((K : ℝ) + 1) := by positivity
            linarith
    rw [Finset.sum_range_succ']
    have h0term : 1 / (((0 : ℕ) : ℝ) + 1) ^ 2 = 1 := by norm_num
    rw [h0term]
    linarith

end Work.BoseBogFS
