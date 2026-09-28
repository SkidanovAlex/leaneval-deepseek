import Mathlib

namespace Work.HP.MM2

open scoped BigOperators

/-- Reindex a sum over `Icc (L+1) M` as a sum over `Ico L M` of shifted terms. -/
private lemma sum_Icc_eq_sum_Ico (f : ℕ → ℝ) (L M : ℕ) :
    ∑ ℓ ∈ Finset.Icc (L + 1) M, f ℓ = ∑ i ∈ Finset.Ico L M, f (i + 1) := by
  rw [Finset.sum_Ico_add' f L M 1, Finset.Ico_add_one_right_eq_Icc]

/-- The base case `s = 2` of the tail estimate: telescopes after the pointwise bound
`1/ℓ² ≤ 1/(ℓ-1) - 1/ℓ`. -/
private lemma base (L M : ℕ) (hL : 1 ≤ L) :
    ∑ ℓ ∈ Finset.Icc (L + 1) M, (1 : ℝ) / (ℓ : ℝ) ^ 2 ≤ 2 / (L : ℝ) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    have : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  by_cases hML : M ≤ L
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    exact le_of_lt (div_pos (by norm_num) hLpos)
  · simp only [not_le] at hML
    have hLM : L ≤ M := le_of_lt hML
    rw [sum_Icc_eq_sum_Ico (fun ℓ => (1 : ℝ) / (ℓ : ℝ) ^ 2) L M]
    have htel :
        ∑ i ∈ Finset.Ico L M, ((1 : ℝ) / (i : ℝ) - 1 / (((i + 1 : ℕ)) : ℝ))
          = 1 / (L : ℝ) - 1 / (M : ℝ) := by
      have h2 :
          ∑ i ∈ Finset.Ico L M, ((1 : ℝ) / (i : ℝ) - 1 / (((i + 1 : ℕ)) : ℝ))
            = -∑ i ∈ Finset.Ico L M, ((1 : ℝ) / (((i + 1 : ℕ)) : ℝ) - 1 / (i : ℝ)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [h2, Finset.sum_Ico_sub (fun j : ℕ => (1 : ℝ) / (j : ℝ)) hLM]
      ring
    calc ∑ i ∈ Finset.Ico L M, (1 : ℝ) / (((i + 1 : ℕ)) : ℝ) ^ 2
        ≤ ∑ i ∈ Finset.Ico L M, ((1 : ℝ) / (i : ℝ) - 1 / (((i + 1 : ℕ)) : ℝ)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi1 : 1 ≤ i := le_trans hL (Finset.mem_Ico.mp hi).1
          have hi0 : (0 : ℝ) < (i : ℝ) := by
            exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hi1)
          have hc : (((i + 1 : ℕ)) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
          rw [hc]
          have hden : (0 : ℝ) < (i : ℝ) * ((i : ℝ) + 1) := by positivity
          have hle : (i : ℝ) * ((i : ℝ) + 1) ≤ ((i : ℝ) + 1) * ((i : ℝ) + 1) := by
            nlinarith [hi0]
          calc (1 : ℝ) / ((i : ℝ) + 1) ^ 2 = 1 / (((i : ℝ) + 1) * ((i : ℝ) + 1)) := by
                rw [pow_two]
            _ ≤ 1 / ((i : ℝ) * ((i : ℝ) + 1)) := one_div_le_one_div_of_le hden hle
            _ = 1 / (i : ℝ) - 1 / ((i : ℝ) + 1) := by
                field_simp
                ring
      _ = 1 / (L : ℝ) - 1 / (M : ℝ) := htel
      _ ≤ 2 / (L : ℝ) := by
          have h1 : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
          have ha : 1 / (L : ℝ) - 1 / (M : ℝ) ≤ 1 / (L : ℝ) := by linarith
          have hb : (1 : ℝ) / (L : ℝ) ≤ 2 / (L : ℝ) :=
            div_le_div_of_nonneg_right (by norm_num) hLpos.le
          linarith

/-- Tail estimate for all exponents `s ≥ 2`, by induction on `s`; the induction step
factors out `1/L` and the base case telescopes. -/
private lemma general : ∀ (s : ℕ), 2 ≤ s → ∀ (L M : ℕ), 1 ≤ L →
    ∑ ℓ ∈ Finset.Icc (L + 1) M, (1 : ℝ) / (ℓ : ℝ) ^ s ≤ 2 / (L : ℝ) ^ (s - 1) := by
  refine Nat.le_induction ?_ ?_
  · intro L M hL
    simpa using base L M hL
  · intro n hn ih L M hL
    have hLpos : (0 : ℝ) < (L : ℝ) := by
      have : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
      linarith
    rw [Nat.add_sub_cancel]
    have hpow : (L : ℝ) ^ n = (L : ℝ) * (L : ℝ) ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ']
    calc ∑ ℓ ∈ Finset.Icc (L + 1) M, (1 : ℝ) / (ℓ : ℝ) ^ (n + 1)
        ≤ ∑ ℓ ∈ Finset.Icc (L + 1) M, (1 / (L : ℝ)) * ((1 : ℝ) / (ℓ : ℝ) ^ n) := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          have hℓge : (L : ℝ) ≤ (ℓ : ℝ) := by
            have : L ≤ ℓ := le_trans (Nat.le_succ L) (Finset.mem_Icc.mp hℓ).1
            exact_mod_cast this
          have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := lt_of_lt_of_le hLpos hℓge
          have hinv : (1 : ℝ) / (ℓ : ℝ) ≤ 1 / (L : ℝ) := one_div_le_one_div_of_le hLpos hℓge
          have hpow' : (0 : ℝ) ≤ (1 : ℝ) / (ℓ : ℝ) ^ n := by positivity
          calc (1 : ℝ) / (ℓ : ℝ) ^ (n + 1) = (1 / (ℓ : ℝ)) * ((1 : ℝ) / (ℓ : ℝ) ^ n) := by
                rw [pow_succ]
                field_simp
            _ ≤ (1 / (L : ℝ)) * ((1 : ℝ) / (ℓ : ℝ) ^ n) :=
                mul_le_mul_of_nonneg_right hinv hpow'
      _ = (1 / (L : ℝ)) * ∑ ℓ ∈ Finset.Icc (L + 1) M, (1 : ℝ) / (ℓ : ℝ) ^ n :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (1 / (L : ℝ)) * (2 / (L : ℝ) ^ (n - 1)) := by
          apply mul_le_mul_of_nonneg_left (ih L M hL)
          positivity
      _ = 2 / (L : ℝ) ^ n := by
          rw [hpow]
          field_simp

theorem ss1_sum_inv_pow_tail (L M s : ℕ) (hs : 3 ≤ s) (hL : 1 ≤ L) :
    ∑ ℓ ∈ Finset.Icc (L + 1) M, (1 : ℝ) / (ℓ : ℝ) ^ s ≤ 2 / (L : ℝ) ^ (s - 1) :=
  general s (by omega) L M hL

end Work.HP.MM2
