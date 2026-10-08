import Mathlib

namespace Work.BG

/-- For a nonzero integer `n`, the square `n ^ 2` is either `1` or at least `4`. -/
lemma int_sq_eq_one_or_four_le (n : ℤ) (hn : n ≠ 0) : n ^ 2 = 1 ∨ 4 ≤ n ^ 2 := by
  rcases lt_or_ge (1:ℤ) n with h | h
  · right
    have h2 : (2:ℤ) ≤ n := by omega
    nlinarith [sq_nonneg (n - 2)]
  · rcases lt_or_ge n (0:ℤ) with hlt | hge
    · have h' : n ≤ -1 := by omega
      rcases lt_or_ge n (-1) with h2 | h2
      · right
        have h3 : n ≤ -2 := by omega
        nlinarith [sq_nonneg (n + 2)]
      · left
        have : n = -1 := by omega
        rw [this]; norm_num
    · left
      have : n = 1 := by omega
      rw [this]; norm_num

theorem sumSqFourSplit {ι : Type*} [DecidableEq ι] {s : Finset ι} {c : ι → ℤ}
    (hne : ∀ a ∈ s, c a ≠ 0) (hsum : ∑ a ∈ s, c a ^ 2 = 4) :
    (∃ α : ι, s = {α} ∧ c α ^ 2 = 4) ∨
    ∃ S T : Finset ι, S ⊆ s ∧ T ⊆ s ∧ Disjoint S T ∧ S ∪ T = s ∧
      (∑ a ∈ S, c a ^ 2 = 2) ∧ (∑ a ∈ T, c a ^ 2 = 2) := by
  -- Every square is at least `1` and is either `1` or at least `4`.
  have hge : ∀ a ∈ s, (1:ℤ) ≤ c a ^ 2 := by
    intro a ha
    have h1 : 0 < c a ^ 2 := sq_pos_of_ne_zero (hne a ha)
    omega
  have hsq : ∀ a ∈ s, c a ^ 2 = 1 ∨ 4 ≤ c a ^ 2 :=
    fun a ha => int_sq_eq_one_or_four_le (c a) (hne a ha)
  -- Consequently `s` has at most four elements and is nonempty.
  have hcard_le : s.card ≤ 4 := by
    have h := Finset.sum_le_sum hge
    rw [hsum] at h
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact_mod_cast h
  have hge1 : 1 ≤ s.card := by
    rcases Nat.eq_zero_or_pos s.card with h | h
    · exfalso
      have hs : s = ∅ := Finset.card_eq_zero.mp h
      rw [hs] at hsum
      simp at hsum
    · omega
  rcases eq_or_lt_of_le hge1 with h1 | h2
  · -- Case `s.card = 1`: a single element whose square is `4`.
    left
    obtain ⟨α, hα⟩ := Finset.card_eq_one.mp h1.symm
    refine ⟨α, hα, ?_⟩
    rw [hα] at hsum
    simpa using hsum
  · -- Case `2 ≤ s.card`: every value is `1`, hence `s.card = 4` and we split evenly.
    right
    have hall : ∀ a ∈ s, c a ^ 2 = 1 := by
      intro a ha
      rcases hsq a ha with h | h
      · exact h
      · exfalso
        -- a single term is at most `4 - 1 = 3`, contradicting `4 ≤ c a ^ 2`
        have hmem := Finset.sum_erase_add s (fun x => c x ^ 2) ha
        rw [hsum] at hmem
        have hge' : ∀ x ∈ s.erase a, (1:ℤ) ≤ c x ^ 2 :=
          fun x hx => hge x (Finset.mem_of_mem_erase hx)
        have hse := Finset.sum_le_sum hge'
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hse
        have hce : 1 ≤ (s.erase a).card := by
          rw [Finset.card_erase_of_mem ha]; omega
        omega
    have hcard4 : s.card = 4 := by
      have hc : (∑ a ∈ s, c a ^ 2) = (∑ a ∈ s, (1:ℤ)) :=
        Finset.sum_congr rfl (fun a ha => hall a ha)
      rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
      omega
    obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq (s := s) (n := 2) h2
    refine ⟨S, s \ S, hS, Finset.sdiff_subset, Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hS, ?_, ?_⟩
    · have hc : (∑ a ∈ S, c a ^ 2) = (∑ a ∈ S, (1:ℤ)) :=
        Finset.sum_congr rfl (fun a ha => hall a (hS ha))
      rw [hc, Finset.sum_const, nsmul_eq_mul, mul_one, hScard]
      norm_num
    · have hc : (∑ a ∈ s \ S, c a ^ 2) = (∑ a ∈ s \ S, (1:ℤ)) :=
        Finset.sum_congr rfl (fun a ha => hall a (Finset.mem_sdiff.mp ha).1)
      rw [hc, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hcardT : (s \ S).card = 2 := by
        have hI : S ∩ s = S := Finset.inter_eq_left.mpr hS
        rw [Finset.card_sdiff, hI]
        omega
      rw [hcardT]; norm_num

end Work.BG
