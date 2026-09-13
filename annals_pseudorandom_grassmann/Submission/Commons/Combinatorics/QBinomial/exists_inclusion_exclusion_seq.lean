import Mathlib
import Submission.Commons.Combinatorics.QBinomial.alt_sum_eq_one

namespace Commons.Combinatorics.QBinomial

open Module

noncomputable section

/-- There is exactly one `n`-dimensional subspace of `𝔽₂ⁿ`, namely the whole space. -/
lemma gb_self (n : ℕ) : gb n n = 1 := by
  unfold gb
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨⊤, by rw [finrank_top, Module.finrank_pi, Fintype.card_fin]⟩, ?_⟩
  rintro ⟨W, hW⟩
  exact Subtype.ext (Submodule.eq_top_of_finrank_eq
    (by rw [hW, Module.finrank_pi, Fintype.card_fin]))

theorem exists_inclusion_exclusion_seq (d : ℕ) :
    ∃ a : ℕ → ℤ,
      (∀ k : ℕ, 1 ≤ k →
        a k = 1 - ∑ i ∈ Finset.Icc 1 (k - 1),
          a i * (Commons.Combinatorics.QBinomial.gb k i : ℤ)) ∧
      ∀ k : ℕ, k ≤ d → |a k| ≤ 2 ^ (2 * k ^ 2) := by
  refine ⟨fun k => (-1 : ℤ) ^ (k - 1) * (2 : ℤ) ^ (k * (k - 1) / 2), ?_, ?_⟩
  · intro k hk
    have ht : (∑ i ∈ Finset.Icc 1 k,
        ((-1 : ℤ) ^ (i - 1) * (2 : ℤ) ^ (i * (i - 1) / 2)) * (gb k i : ℤ)) = 1 := by
      simpa only [gb] using alt_sum_eq_one (n := k) hk
    have hsplit : Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hknot : k ∉ Finset.Icc 1 (k - 1) := by
      simp only [Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert hknot, gb_self k, Nat.cast_one, mul_one] at ht
    linarith
  · intro k _
    have habs : |(-1 : ℤ) ^ (k - 1) * (2 : ℤ) ^ (k * (k - 1) / 2)|
        = (2 : ℤ) ^ (k * (k - 1) / 2) := by
      rw [abs_mul, abs_neg_one_pow, one_mul, abs_pow, abs_two]
    rw [habs]
    apply pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
    have h1 : k * (k - 1) / 2 ≤ k * (k - 1) := Nat.div_le_self _ _
    have h2 : k * (k - 1) ≤ k * k := Nat.mul_le_mul_left k (Nat.sub_le k 1)
    have h3 : k * k ≤ 2 * k ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_left (k * k) (by norm_num)
    exact le_trans h1 (le_trans h2 h3)

end

end Commons.Combinatorics.QBinomial
