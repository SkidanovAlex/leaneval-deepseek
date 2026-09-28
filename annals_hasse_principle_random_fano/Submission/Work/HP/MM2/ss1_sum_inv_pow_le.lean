import Mathlib

namespace Work.HP.MM2

/-- The partial sums of `∑_k 1/(k+1)^2` are bounded by `2`. -/
lemma sum_range_inv_succ_sq_le (M : ℕ) :
    ∑ i ∈ Finset.range M, (1 : ℝ) / ((i : ℝ) + 1) ^ 2 ≤ 2 := by
  have hterm : ∀ i : ℕ,
      (1 : ℝ) / ((i : ℝ) + 1) ^ 2
        ≤ 2 / ((i : ℝ) + 1) - 2 / (((i : ℝ) + 1) + 1) := by
    intro i
    have hA : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    rw [div_sub_div _ _ (ne_of_gt hA) (by positivity)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [show (0 : ℝ) ≤ (i : ℝ) from Nat.cast_nonneg i]
  have htel : ∑ i ∈ Finset.range M, (2 / ((i : ℝ) + 1) - 2 / (((i : ℝ) + 1) + 1))
      = 2 - 2 / ((M : ℝ) + 1) := by
    have h := Finset.sum_range_sub' (fun i : ℕ => (2 : ℝ) / ((i : ℝ) + 1)) M
    simpa [Nat.cast_add, Nat.cast_one] using h
  calc ∑ i ∈ Finset.range M, (1 : ℝ) / ((i : ℝ) + 1) ^ 2
      ≤ ∑ i ∈ Finset.range M, (2 / ((i : ℝ) + 1) - 2 / (((i : ℝ) + 1) + 1)) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = 2 - 2 / ((M : ℝ) + 1) := htel
    _ ≤ 2 := by
        have h0 : (0 : ℝ) ≤ 2 / ((M : ℝ) + 1) := by positivity
        linarith

theorem ss1_sum_inv_pow_le (M s : ℕ) (hs : 2 ≤ s) :
    ∑ ℓ ∈ Finset.Icc 1 M, (1 : ℝ) / (ℓ : ℝ) ^ s ≤ 2 := by
  have hstep : ∑ ℓ ∈ Finset.Icc 1 M, (1 : ℝ) / (ℓ : ℝ) ^ s
      ≤ ∑ ℓ ∈ Finset.Icc 1 M, (1 : ℝ) / (ℓ : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro ℓ hℓ
    obtain ⟨h1, _⟩ := Finset.mem_Icc.mp hℓ
    have hpos : (0 : ℝ) < (ℓ : ℝ) ^ 2 := by
      have hlt : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h1)
      positivity
    have hpow : (ℓ : ℝ) ^ 2 ≤ (ℓ : ℝ) ^ s :=
      pow_le_pow_right₀ (by exact_mod_cast h1) hs
    exact one_div_le_one_div_of_le hpos hpow
  have hmid : ∑ ℓ ∈ Finset.Icc 1 M, (1 : ℝ) / (ℓ : ℝ) ^ 2
      = ∑ i ∈ Finset.range M, (1 : ℝ) / ((i : ℝ) + 1) ^ 2 := by
    have hIcc : (Finset.Icc 1 M : Finset ℕ) = Finset.Ico 1 (M + 1) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring_nf
  calc ∑ ℓ ∈ Finset.Icc 1 M, (1 : ℝ) / (ℓ : ℝ) ^ s
      ≤ ∑ ℓ ∈ Finset.Icc 1 M, (1 : ℝ) / (ℓ : ℝ) ^ 2 := hstep
    _ = ∑ i ∈ Finset.range M, (1 : ℝ) / ((i : ℝ) + 1) ^ 2 := hmid
    _ ≤ 2 := sum_range_inv_succ_sq_le M

end Work.HP.MM2
