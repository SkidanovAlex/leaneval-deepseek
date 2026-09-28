import Mathlib

/-!
# The dyadic pair-sum bound `∑_{a ≤ b, a + 2b ≤ M} 2^{2a}`

For `M : ℕ` we bound the weighted pair sum

`∑_{a ≤ b, a + 2b ≤ M} 2^{2a} ≤ C · (M + 1) · (2^M)^{2/3}`

with an absolute constant `C = 4`.

The key point is that `a ≤ b` and `a + 2 b ≤ M` force `3 a ≤ M`, so the first coordinate
ranges only over `0 ≤ a ≤ M/3`; for each such `a` there are at most `M + 1` admissible
second coordinates, and the remaining sum `∑_{a ≤ M/3} 2^{2a} = ∑_{a ≤ M/3} 4^a` is a
geometric series dominated by its last term `4^{M/3} = (2^M)^{2/3}`.
-/

namespace Work.HP.MDEstimates

open Finset

/-- Geometric-series bound: `∑_{a < K+1} 4^a ≤ 4^{K+1}`. -/
private lemma geom_four_le (K : ℕ) :
    (∑ a ∈ Finset.range (K + 1), (4 : ℝ) ^ a) ≤ (4 : ℝ) ^ (K + 1) := by
  rw [geom_sum_eq (by norm_num : (4 : ℝ) ≠ 1) (K + 1)]
  have hpos : (0 : ℝ) < (4 : ℝ) ^ (K + 1) := by positivity
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4 - 1)]
  linarith

/-- `2^(2a) = 4^a` for a natural exponent. -/
private lemma two_pow_two_mul (a : ℕ) : (2 : ℝ) ^ (2 * a) = (4 : ℝ) ^ a := by
  rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, pow_mul]

/-- The numbers `a < M + 1` with `3 * a ≤ M` are exactly the numbers `a < M / 3 + 1`. -/
private lemma filter_range_div3 (M : ℕ) :
    (Finset.range (M + 1)).filter (fun a => 3 * a ≤ M) = Finset.range (M / 3 + 1) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, h3⟩
    have : a * 3 ≤ M := by omega
    exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mpr this)
  · intro h
    have ha : a ≤ M / 3 := Nat.lt_succ_iff.mp h
    have h3 : a * 3 ≤ M := (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mp ha
    have hM : M / 3 ≤ M := Nat.div_le_self M 3
    exact ⟨by omega, by omega⟩

/-- `4^(M/3) = (2^M)^(2/3)` for real powers. -/
private lemma four_rpow_eq (M : ℕ) :
    (4 : ℝ) ^ ((M : ℝ) / 3) = ((2 : ℝ) ^ M) ^ ((2 : ℝ) / 3) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hL : (4 : ℝ) ^ ((M : ℝ) / 3) = (2 : ℝ) ^ ((2 : ℝ) * ((M : ℝ) / 3)) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num [Real.rpow_natCast]]
    rw [← Real.rpow_mul h2]
  have hR : ((2 : ℝ) ^ M) ^ ((2 : ℝ) / 3) = (2 : ℝ) ^ ((2 : ℝ) * ((M : ℝ) / 3)) := by
    rw [← Real.rpow_natCast (2 : ℝ) M]
    rw [← Real.rpow_mul h2]
    congr 1
    ring
  rw [hL, hR]

theorem dyadic_pair_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ,
      (∑ p ∈ ((Finset.range (M + 1)).product (Finset.range (M + 1))).filter
          (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ p.1 + 2 * p.2 ≤ M),
        (2 : ℝ) ^ (2 * p.1))
      ≤ C * ((M : ℝ) + 1) * ((2 : ℝ) ^ M) ^ ((2 : ℝ) / 3) := by
  refine ⟨4, by norm_num, fun M => ?_⟩
  -- Regroup the sum as a double sum over `(a, b)`.
  have hrewrite :
      (∑ p ∈ ((Finset.range (M + 1)).product (Finset.range (M + 1))).filter
          (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ p.1 + 2 * p.2 ≤ M),
        (2 : ℝ) ^ (2 * p.1))
      = (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
          (if a ≤ b ∧ a + 2 * b ≤ M then (2 : ℝ) ^ (2 * a) else 0)) := by
    rw [Finset.sum_filter]
    rw [show (Finset.range (M + 1)).product (Finset.range (M + 1))
          = (Finset.range (M + 1)) ×ˢ (Finset.range (M + 1)) from rfl]
    rw [Finset.sum_product]
  rw [hrewrite]
  calc (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
          (if a ≤ b ∧ a + 2 * b ≤ M then (2 : ℝ) ^ (2 * a) else 0))
      -- Any admissible pair satisfies `3 a ≤ M`.
      ≤ (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
          (if 3 * a ≤ M then (2 : ℝ) ^ (2 * a) else 0)) := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        by_cases h3 : 3 * a ≤ M
        · rw [ite_eq_left h3]
          by_cases hP : a ≤ b ∧ a + 2 * b ≤ M
          · rw [ite_eq_left hP]
          · rw [ite_eq_right hP]; positivity
        · rw [ite_eq_right h3]
          have hnot : ¬(a ≤ b ∧ a + 2 * b ≤ M) := by
            rintro ⟨hab, hsum⟩
            exact h3 (by omega)
          rw [ite_eq_right hnot]
    -- The inner sum is constant in `b`.
    _ = ((M : ℝ) + 1) *
          (∑ a ∈ Finset.range (M + 1), (if 3 * a ≤ M then (2 : ℝ) ^ (2 * a) else 0)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = ((M : ℝ) + 1) *
          (∑ a ∈ Finset.range (M + 1), (if 3 * a ≤ M then (4 : ℝ) ^ a else 0)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        by_cases h3 : 3 * a ≤ M
        · rw [ite_eq_left h3, ite_eq_left h3, two_pow_two_mul]
        · rw [ite_eq_right h3, ite_eq_right h3]
    _ = ((M : ℝ) + 1) *
          (∑ a ∈ (Finset.range (M + 1)).filter (fun a => 3 * a ≤ M), (4 : ℝ) ^ a) := by
        congr 1
        rw [Finset.sum_filter]
    _ = ((M : ℝ) + 1) * (∑ a ∈ Finset.range (M / 3 + 1), (4 : ℝ) ^ a) := by
        rw [filter_range_div3]
    _ ≤ ((M : ℝ) + 1) * (4 : ℝ) ^ (M / 3 + 1) := by
        apply mul_le_mul_of_nonneg_left (geom_four_le (M / 3))
        positivity
    _ ≤ 4 * ((M : ℝ) + 1) * ((2 : ℝ) ^ M) ^ ((2 : ℝ) / 3) := by
        have hcast : ((M / 3 : ℕ) : ℝ) ≤ (M : ℝ) / 3 := Nat.cast_div_le
        have hle : (4 : ℝ) ^ (M / 3) ≤ (4 : ℝ) ^ ((M : ℝ) / 3) := by
          rw [← Real.rpow_natCast (4 : ℝ) (M / 3)]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hcast
        rw [pow_succ]
        rw [← four_rpow_eq M]
        calc ((M : ℝ) + 1) * ((4 : ℝ) ^ (M / 3) * 4)
            = 4 * ((M : ℝ) + 1) * (4 : ℝ) ^ (M / 3) := by ring
          _ ≤ 4 * ((M : ℝ) + 1) * (4 : ℝ) ^ ((M : ℝ) / 3) := by
              apply mul_le_mul_of_nonneg_left hle
              positivity

end Work.HP.MDEstimates
