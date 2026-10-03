import Mathlib

namespace Work.FIArea1

/-- Divisor-pairing bound: if `n ≤ D * D`, then every divisor `d` of `n` with
`d > D` has complementary divisor `n / d ≤ D`, and the map `d ↦ n / d` is
injective on those divisors.  Hence the number of divisors of `n` exceeds the
number of divisors `≤ D` by at most a factor `2`. -/
lemma divisors_card_le_two_mul_divisors_le (n D : ℕ) (h : n ≤ D * D) :
    n.divisors.card ≤ 2 * ((Finset.Icc 1 D).filter (fun d => d ∣ n)).card := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn, Nat.divisors_zero]; simp
  have key : ∀ d ∈ n.divisors, D < d → n / d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n) := by
    intro d hd hDd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdvd, _⟩ := hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
    have hdle : d ≤ n := Nat.le_of_dvd hn hdvd
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, Nat.div_dvd_of_dvd hdvd⟩
    · exact (Nat.le_div_iff_mul_le hdpos).mpr (by simpa using hdle)
    · apply Nat.lt_succ_iff.mp
      rw [Nat.div_lt_iff_lt_mul hdpos]
      have hdge : D + 1 ≤ d := by omega
      calc n ≤ D * D := h
        _ < (D + 1) * d := by nlinarith [hdge]
  have hinj : Set.InjOn (fun d => n / d) ↑(n.divisors.filter (fun d => D < d)) := by
    intro d hd d' hd' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hd hd'
    obtain ⟨hdd, _⟩ := hd
    obtain ⟨hdd', _⟩ := hd'
    rw [Nat.mem_divisors] at hdd hdd'
    obtain ⟨hdvd, _⟩ := hdd
    obtain ⟨hdvd', _⟩ := hdd'
    have heq' : n / d = n / d' := heq
    have hcpos : 0 < n / d' := by
      have : d' ≤ n := Nat.le_of_dvd hn hdvd'
      have hd'pos : 0 < d' := Nat.pos_of_dvd_of_pos hdvd' hn
      exact (Nat.le_div_iff_mul_le hd'pos).mpr (by simpa using this)
    have h1 : d * (n / d) = n := Nat.mul_div_cancel' hdvd
    have h2 : d' * (n / d') = n := Nat.mul_div_cancel' hdvd'
    rw [heq'] at h1
    exact Nat.eq_of_mul_eq_mul_right hcpos (by rw [h1, h2])
  have hA : (n.divisors.filter (fun d => D < d)).card
      ≤ ((Finset.Icc 1 D).filter (fun d => d ∣ n)).card := by
    apply Finset.card_le_card_of_injOn (fun d => n / d)
    · intro d hd
      rw [Finset.mem_coe, Finset.mem_filter] at hd
      simpa only [Finset.mem_coe, Finset.mem_filter] using key d hd.1 hd.2
    · exact hinj
  have hB : (n.divisors.filter (fun d => ¬ D < d)).card
      ≤ ((Finset.Icc 1 D).filter (fun d => d ∣ n)).card := by
    apply Finset.card_le_card
    intro d hd
    simp only [Finset.mem_filter] at hd ⊢
    obtain ⟨hdd, hle⟩ := hd
    rw [Nat.mem_divisors] at hdd
    obtain ⟨hdvd, _⟩ := hdd
    refine ⟨?_, hdvd⟩
    rw [Finset.mem_Icc]
    exact ⟨Nat.pos_of_dvd_of_pos hdvd hn, by omega⟩
  have hsplit : n.divisors.card
      = (n.divisors.filter (fun d => D < d)).card
        + (n.divisors.filter (fun d => ¬ D < d)).card :=
    (Finset.card_filter_add_card_filter_not (fun d => D < d)).symm
  calc n.divisors.card
      = (n.divisors.filter (fun d => D < d)).card
        + (n.divisors.filter (fun d => ¬ D < d)).card := hsplit
    _ ≤ _ := add_le_add hA hB
    _ = 2 * ((Finset.Icc 1 D).filter (fun d => d ∣ n)).card := by ring

lemma sum_divisors_card_le_two_sum_dvd (s : Finset (ℤ × ℤ)) (D : ℕ) (N : ℤ × ℤ → ℕ) (hN : ∀ p ∈ s, N p ≤ D * D) : (∑ p ∈ s, (N p).divisors.card) ≤ 2 * ∑ d ∈ Finset.Icc 1 D, (s.filter (fun p => d ∣ N p)).card := by
  have step1 : (∑ p ∈ s, (N p).divisors.card)
      ≤ ∑ p ∈ s, 2 * ((Finset.Icc 1 D).filter (fun d => d ∣ N p)).card :=
    Finset.sum_le_sum (fun p hp => divisors_card_le_two_mul_divisors_le (N p) D (hN p hp))
  have step2 : (∑ p ∈ s, 2 * ((Finset.Icc 1 D).filter (fun d => d ∣ N p)).card)
      = 2 * ∑ p ∈ s, ((Finset.Icc 1 D).filter (fun d => d ∣ N p)).card := by
    rw [Finset.mul_sum]
  have step3 : (∑ p ∈ s, ((Finset.Icc 1 D).filter (fun d => d ∣ N p)).card)
      = ∑ d ∈ Finset.Icc 1 D, (s.filter (fun p => d ∣ N p)).card := by
    rw [Finset.sum_congr rfl (fun p _ => Finset.card_filter (fun d => d ∣ N p) (Finset.Icc 1 D)),
        Finset.sum_comm]
    exact Finset.sum_congr rfl (fun d _ => (Finset.card_filter (fun p => d ∣ N p) s).symm)
  calc (∑ p ∈ s, (N p).divisors.card)
      ≤ ∑ p ∈ s, 2 * ((Finset.Icc 1 D).filter (fun d => d ∣ N p)).card := step1
    _ = 2 * ∑ p ∈ s, ((Finset.Icc 1 D).filter (fun d => d ∣ N p)).card := step2
    _ = 2 * ∑ d ∈ Finset.Icc 1 D, (s.filter (fun p => d ∣ N p)).card := by rw [step3]

end Work.FIArea1
