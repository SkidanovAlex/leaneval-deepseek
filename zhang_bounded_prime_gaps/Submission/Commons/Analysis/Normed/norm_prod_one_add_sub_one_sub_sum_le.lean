import Mathlib.Analysis.CStarAlgebra.Classes

namespace Commons.Analysis.Normed

open scoped BigOperators

/-- Product bound: if every `‖f i‖ ≤ B` with `B ≥ 0`, then
`‖∏ (1 + f i) - 1‖ ≤ (1 + B) ^ s.card - 1`. -/
theorem norm_prod_one_add_sub_one_le_pow {ι : Type*} (s : Finset ι) (f : ι → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hf : ∀ i ∈ s, ‖f i‖ ≤ B) :
    ‖∏ i ∈ s, (1 + f i) - 1‖ ≤ (1 + B) ^ s.card - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha IH =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    rw [show (1 + f a) * (∏ i ∈ t, (1 + f i)) - 1
          = ((∏ i ∈ t, (1 + f i)) - 1) + f a * (∏ i ∈ t, (1 + f i)) by ring]
    have hfa : ‖f a‖ ≤ B := hf a (Finset.mem_insert_self a t)
    have hPn : ‖∏ i ∈ t, (1 + f i)‖ ≤ (1 + B) ^ t.card := by
      calc
        ‖∏ i ∈ t, (1 + f i)‖ ≤ ∏ i ∈ t, ‖1 + f i‖ := Finset.norm_prod_le t _
        _ ≤ ∏ i ∈ t, (1 + B) := by
              apply Finset.prod_le_prod
              · intro i hi; positivity
              · intro i hi
                calc ‖1 + f i‖ ≤ ‖(1 : ℂ)‖ + ‖f i‖ := norm_add_le 1 (f i)
                  _ = 1 + ‖f i‖ := by rw [norm_one]
                  _ ≤ 1 + B := by linarith [hf i (Finset.mem_insert_of_mem hi)]
        _ = (1 + B) ^ t.card := Finset.prod_const _
    calc
      ‖((∏ i ∈ t, (1 + f i)) - 1) + f a * (∏ i ∈ t, (1 + f i))‖
          ≤ ‖(∏ i ∈ t, (1 + f i)) - 1‖ + ‖f a * (∏ i ∈ t, (1 + f i))‖ := norm_add_le _ _
      _ ≤ ((1 + B) ^ t.card - 1) + B * (1 + B) ^ t.card := by
            rw [norm_mul]
            have hmul : ‖f a‖ * ‖∏ i ∈ t, (1 + f i)‖ ≤ B * (1 + B) ^ t.card :=
              mul_le_mul hfa hPn (norm_nonneg _) hB
            linarith [IH (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
      _ = (1 + B) ^ (t.card + 1) - 1 := by rw [pow_succ]; ring

theorem norm_prod_one_add_sub_one_sub_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hf : ∀ i ∈ s, ‖f i‖ ≤ B) :
    ‖∏ i ∈ s, (1 + f i) - 1 - ∑ i ∈ s, f i‖ ≤ (1 + B) ^ s.card - 1 - s.card * B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha IH =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    rw [show (1 + f a) * (∏ i ∈ t, (1 + f i)) - 1 - (f a + ∑ i ∈ t, f i)
          = ((∏ i ∈ t, (1 + f i)) - 1 - ∑ i ∈ t, f i)
            + f a * ((∏ i ∈ t, (1 + f i)) - 1) by ring]
    have hfa : ‖f a‖ ≤ B := hf a (Finset.mem_insert_self a t)
    have hPt : ‖(∏ i ∈ t, (1 + f i)) - 1‖ ≤ (1 + B) ^ t.card - 1 :=
      norm_prod_one_add_sub_one_le_pow t f B hB (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    calc
      ‖((∏ i ∈ t, (1 + f i)) - 1 - ∑ i ∈ t, f i)
          + f a * ((∏ i ∈ t, (1 + f i)) - 1)‖
          ≤ ‖(∏ i ∈ t, (1 + f i)) - 1 - ∑ i ∈ t, f i‖
            + ‖f a * ((∏ i ∈ t, (1 + f i)) - 1)‖ := norm_add_le _ _
      _ ≤ ((1 + B) ^ t.card - 1 - t.card * B) + B * ((1 + B) ^ t.card - 1) := by
            rw [norm_mul]
            have hmul : ‖f a‖ * ‖(∏ i ∈ t, (1 + f i)) - 1‖ ≤ B * ((1 + B) ^ t.card - 1) :=
              mul_le_mul hfa hPt (norm_nonneg _) hB
            linarith [IH (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
      _ = (1 + B) ^ (t.card + 1) - 1 - ((t.card + 1 : ℕ) : ℝ) * B := by
            rw [pow_succ]; push_cast; ring

end Commons.Analysis.Normed