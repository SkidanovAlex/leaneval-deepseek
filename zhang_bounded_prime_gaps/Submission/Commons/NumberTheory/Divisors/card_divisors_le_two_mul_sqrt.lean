import Mathlib.NumberTheory.Divisors
import Submission.Commons.NumberTheory.DivisorBound.pair_lcm_count_bound

namespace Commons.NumberTheory.Divisors

/-- The number of divisors of `n` is at most `2 * sqrt n + 1`.  This follows by pairing each
divisor `d` with `n / d`: the map `d ↦ n / d` sends divisors `> sqrt n` injectively into
divisors `≤ sqrt n`, and there are at most `sqrt n` of the latter. -/
theorem card_divisors_le_two_mul_sqrt (n : ℕ) : n.divisors.card ≤ 2 * Nat.sqrt n + 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.divisors_zero]
  set s := Nat.sqrt n with hs
  have hsplit : n.divisors.card
      = (n.divisors.filter (fun d => d ≤ s)).card
        + (n.divisors.filter (fun d => ¬ d ≤ s)).card := by
    rw [Finset.card_filter_add_card_filter_not]
  have hA : (n.divisors.filter (fun d => d ≤ s)).card ≤ s := by
    have hsub : n.divisors.filter (fun d => d ≤ s) ⊆ Finset.Icc 1 s := by
      intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdvd, _⟩, hds⟩ := hd
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn), hds⟩
    calc (n.divisors.filter (fun d => d ≤ s)).card ≤ (Finset.Icc 1 s).card :=
          Finset.card_le_card hsub
      _ = s := by rw [Nat.card_Icc]; simp
  have hB : (n.divisors.filter (fun d => ¬ d ≤ s)).card
      ≤ (n.divisors.filter (fun d => d ≤ s)).card := by
    apply Finset.card_le_card_of_injOn (fun d => n / d)
    · intro d hd
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      obtain ⟨⟨hdvd, _⟩, hgt⟩ := hd
      have hlt : s < d := not_le.mp hgt
      refine ⟨⟨Nat.div_dvd_of_dvd hdvd, hn⟩, ?_⟩
      have hsd : s + 1 ≤ d := hlt
      have h1 : n / d ≤ n / (s + 1) := Nat.div_le_div_left hsd (Nat.succ_pos s)
      have h2 : n / (s + 1) ≤ s := by
        have h3 := Nat.lt_succ_sqrt n
        rw [← hs] at h3
        have h4 : n / (s + 1) < s + 1 :=
          (Nat.div_lt_iff_lt_mul (Nat.succ_pos s)).mpr h3
        exact Nat.lt_succ_iff.mp h4
      exact le_trans h1 h2
    · intro d1 hd1 d2 hd2 heq
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd1 hd2
      obtain ⟨⟨h1dvd, _⟩, _⟩ := hd1
      obtain ⟨⟨h2dvd, _⟩, _⟩ := hd2
      have e1 : n / (n / d1) = d1 := Nat.div_div_self h1dvd hn
      have e2 : n / (n / d2) = d2 := Nat.div_div_self h2dvd hn
      have h : n / d1 = n / d2 := heq
      calc d1 = n / (n / d1) := e1.symm
        _ = n / (n / d2) := by rw [h]
        _ = d2 := e2
  have h2s : n.divisors.card ≤ 2 * s := by omega
  omega

end Commons.NumberTheory.Divisors