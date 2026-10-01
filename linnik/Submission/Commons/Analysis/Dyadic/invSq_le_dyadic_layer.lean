import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Dyadic

open scoped BigOperators

/-- Per-point dyadic layer bound: for `0 ≤ d ≤ 2^K`, the inverse-square kernel
`1/(1+d²)` is bounded by the sum over `k ∈ {0,…,K}` of `4/4^k` on the event `d ≤ 2^k`. -/
theorem invSq_le_dyadic_layer (d : ℝ) (hd : 0 ≤ d) (K : ℕ) (hdK : d ≤ (2:ℝ)^K) :
    (1:ℝ) / (1 + d^2) ≤
      Finset.sum (Finset.range (K + 1))
        (fun k => if d ≤ (2:ℝ)^k then 4 / (4:ℝ)^k else 0) := by
  -- Let `j` be the least exponent with `d ≤ 2^j` (which exists since `d ≤ 2^K`).
  have hex : ∃ k : ℕ, d ≤ (2:ℝ)^k := ⟨K, hdK⟩
  obtain ⟨j, hjK, hjP, hjmin⟩ :
      ∃ j : ℕ, j ≤ K ∧ d ≤ (2:ℝ)^j ∧ ∀ i < j, ¬ (d ≤ (2:ℝ)^i) :=
    ⟨Nat.find hex, Nat.find_min' hex hdK, Nat.find_spec hex,
      fun i hi => Nat.find_min hex hi⟩
  -- The single term at index `j` already dominates `1/(1+d²)`.
  have hbound : (1:ℝ) / (1 + d^2) ≤ 4 / (4:ℝ)^j := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · -- `j = 0`: then `d ≤ 1`, so `1/(1+d²) ≤ 1 ≤ 4`.
      rw [h0]
      have h1 : (1:ℝ) / (1 + d^2) ≤ 1 := by
        have := one_div_le_one_div_of_le (show (0:ℝ) < 1 by norm_num)
          (show (1:ℝ) ≤ 1 + d^2 by nlinarith [sq_nonneg d])
        simpa using this
      have h2 : (4:ℝ) / (4:ℝ)^0 = 4 := by norm_num
      rw [h2]; linarith
    · -- `j ≥ 1`: write `j = m+1`. Then `d > 2^m`, hence `d² > 4^m`,
      -- so `1/(1+d²) ≤ 1/d² ≤ 1/4^m = 4/4^{m+1}`.
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      subst hm
      have hprev : ¬ (d ≤ (2:ℝ)^m) := hjmin m (Nat.lt_succ_self m)
      have hgt : (2:ℝ)^m < d := not_le.mp hprev
      have hb_pos : (0:ℝ) < (2:ℝ)^m := pow_pos (by norm_num) m
      have hdpos : (0:ℝ) < d := lt_trans hb_pos hgt
      have hsq : ((2:ℝ)^m)^2 < d^2 := by
        have h := mul_self_lt_mul_self (le_of_lt hb_pos) hgt
        simpa [pow_two] using h
      have hb2 : ((2:ℝ)^m)^2 = (4:ℝ)^m := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
      have h4m : (0:ℝ) < (4:ℝ)^m := pow_pos (by norm_num) m
      have hd2pos : (0:ℝ) < d^2 := pow_pos hdpos 2
      have h1 : (1:ℝ) / (1 + d^2) ≤ 1 / d^2 :=
        one_div_le_one_div_of_le hd2pos (by nlinarith [sq_nonneg d])
      have h2 : (1:ℝ) / d^2 ≤ 1 / (4:ℝ)^m :=
        one_div_le_one_div_of_le h4m (by rw [← hb2]; exact le_of_lt hsq)
      have htarget : (4:ℝ) / (4:ℝ)^(m+1) = 1 / (4:ℝ)^m := by
        rw [pow_succ]; field_simp
      calc (1:ℝ) / (1 + d^2) ≤ 1 / d^2 := h1
        _ ≤ 1 / (4:ℝ)^m := h2
        _ = 4 / (4:ℝ)^(m+1) := htarget.symm
  -- The term at index `j` is part of the sum, and all terms are nonnegative.
  have hjmem : j ∈ Finset.range (K + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hjK)
  have hnonneg : ∀ k ∈ Finset.range (K + 1),
      0 ≤ (if d ≤ (2:ℝ)^k then 4 / (4:ℝ)^k else 0) := by
    intro k _
    split_ifs with hk
    · positivity
    · exact le_refl 0
  have hsum : 4 / (4:ℝ)^j ≤
      Finset.sum (Finset.range (K + 1))
        (fun k => if d ≤ (2:ℝ)^k then 4 / (4:ℝ)^k else 0) := by
    simpa [if_pos hjP] using Finset.single_le_sum hnonneg hjmem
  exact le_trans hbound hsum

end Commons.Analysis.Dyadic