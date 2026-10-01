import Mathlib

namespace Work.ZeroDensity.Ingham

/-- The number of divisors of `n` is at most `2 * √n`, in `ℕ`. -/
theorem divisors_card_le_two_mul_sqrt (n : ℕ) :
    n.divisors.card ≤ 2 * Nat.sqrt n := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := n.divisors)
    (p := fun d => d ≤ Nat.sqrt n)
  have hsmall : (n.divisors.filter (fun d => d ≤ Nat.sqrt n)).card ≤ Nat.sqrt n := by
    have hsub : n.divisors.filter (fun d => d ≤ Nat.sqrt n) ⊆ Finset.Icc 1 (Nat.sqrt n) := by
      intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdvd, hne⟩, hle⟩ := hd
      refine Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero ?_, hle⟩
      rintro rfl
      exact hne (zero_dvd_iff.mp hdvd)
    calc (n.divisors.filter (fun d => d ≤ Nat.sqrt n)).card
        ≤ (Finset.Icc 1 (Nat.sqrt n)).card := Finset.card_le_card hsub
      _ = Nat.sqrt n := by rw [Nat.card_Icc]; omega
  have hbig : (n.divisors.filter (fun d => ¬ d ≤ Nat.sqrt n)).card
      ≤ (n.divisors.filter (fun d => d ≤ Nat.sqrt n)).card := by
    refine Finset.card_le_card_of_injOn (fun d => n / d) ?_ ?_
    · intro d hd
      rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdvd, hne⟩, hgt⟩ := hd
      change n / d ∈ n.divisors.filter (fun d => d ≤ Nat.sqrt n)
      rw [Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨Nat.div_dvd_of_dvd hdvd, hne⟩, ?_⟩
      by_contra hcon
      rw [not_le] at hcon
      have hd1 : Nat.sqrt n + 1 ≤ d := by omega
      have hd2 : Nat.sqrt n + 1 ≤ n / d := by omega
      have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdvd
      have hnsq : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by
        simpa [pow_two] using Nat.lt_succ_sqrt' n
      have hge : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ d * (n / d) :=
        Nat.mul_le_mul hd1 hd2
      omega
    · intro d1 hd1 d2 hd2 heq
      rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd1 hd2
      obtain ⟨⟨hdvd1, hne1⟩, _⟩ := hd1
      obtain ⟨⟨hdvd2, _⟩, _⟩ := hd2
      have heq' : n / d1 = n / d2 := heq
      have hm1 : d1 * (n / d1) = n := Nat.mul_div_cancel' hdvd1
      have hm2 : d2 * (n / d2) = n := Nat.mul_div_cancel' hdvd2
      have hc : 0 < n / d1 := by
        rcases Nat.eq_zero_or_pos (n / d1) with h | h
        · rw [h, mul_zero] at hm1
          exact absurd hm1.symm hne1
        · exact h
      exact Nat.mul_right_cancel hc (by rw [hm1, heq', hm2])
  omega

/-- For every `n`, the number of divisors of `n` is at most `2 * Real.sqrt n`. (Pair each
divisor `d` of `n` with `n / d`: the divisors exceeding `√n` inject into those not exceeding
`√n`, and the latter number at most `⌊√n⌋`.) -/
theorem divisorsCardLeTwoSqrt (n : ℕ) :
    ((n.divisors.card : ℕ) : ℝ) ≤ 2 * Real.sqrt n := by
  have h := divisors_card_le_two_mul_sqrt n
  have hs : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt n := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast Nat.sqrt_le' n
  calc ((n.divisors.card : ℕ) : ℝ) ≤ ((2 * Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast h
    _ = 2 * ((Nat.sqrt n : ℕ) : ℝ) := by push_cast; ring
    _ ≤ 2 * Real.sqrt n := by linarith

end Work.ZeroDensity.Ingham
