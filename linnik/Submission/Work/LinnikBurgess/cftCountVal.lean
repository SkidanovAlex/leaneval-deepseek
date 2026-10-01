import Mathlib

namespace Work.LinnikBurgess

/-- Among the natural numbers `t < p ^ M`, at most `p ^ (M - k)` have
`p`-adic valuation exactly `k` (for `p ≥ 2`).

Since `p ^ padicValNat p t ∣ t` always holds (`pow_padicValNat_dvd`), every `t`
in the filtered set is divisible by `p ^ k`, so the map `t ↦ t / p ^ k` is
injective on it.  Moreover `t < p ^ M` forces `t / p ^ k < p ^ (M - k)`:
if `k ≤ M` this is the identity `p ^ M = p ^ k * p ^ (M - k)` together with
`0 < p ^ k`; if `k > M`, then `p ^ (M - k) = p ^ 0 = 1` and it suffices that
`t / p ^ k = 0`, which follows from `t < p ^ M ≤ p ^ k`.  Hence the count is at
most the size of `Finset.range (p ^ (M - k))`. -/
lemma cftCountVal {p M k : ℕ} (hp : 2 ≤ p) :
    ((Finset.range (p ^ M)).filter (fun t : ℕ => padicValNat p t = k)).card
      ≤ p ^ (M - k) := by
  by_cases hk : k ≤ M
  · have hpkpos : 0 < p ^ k := pow_pos (by omega) k
    have hM : p ^ M = p ^ k * p ^ (M - k) := by
      conv_lhs => rw [← Nat.add_sub_of_le hk]
      rw [Nat.pow_add]
    rw [← Finset.card_range (p ^ (M - k))]
    refine Finset.card_le_card_of_injOn (fun t => t / p ^ k) ?_ ?_
    · intro t ht
      have ht' : t ∈ (Finset.range (p ^ M)).filter (fun t : ℕ => padicValNat p t = k) := by
        simpa using ht
      obtain ⟨hlt, hval⟩ := Finset.mem_filter.mp ht'
      have hlt' : t < p ^ M := Finset.mem_range.mp hlt
      have hdvd : p ^ k ∣ t := by
        have h := pow_padicValNat_dvd (p := p) (n := t)
        rwa [hval] at h
      have hmul : p ^ k * (t / p ^ k) < p ^ k * p ^ (M - k) := by
        rw [Nat.mul_div_cancel' hdvd, ← hM]; exact hlt'
      rw [Finset.mem_coe, Finset.mem_range]
      exact (Nat.mul_lt_mul_left hpkpos).mp hmul
    · intro t1 ht1 t2 ht2 heq
      have ht1' : t1 ∈ (Finset.range (p ^ M)).filter (fun t : ℕ => padicValNat p t = k) := by
        simpa using ht1
      have ht2' : t2 ∈ (Finset.range (p ^ M)).filter (fun t : ℕ => padicValNat p t = k) := by
        simpa using ht2
      have hval1 := (Finset.mem_filter.mp ht1').2
      have hval2 := (Finset.mem_filter.mp ht2').2
      have hd1 : p ^ k ∣ t1 := by
        have h := pow_padicValNat_dvd (p := p) (n := t1); rwa [hval1] at h
      have hd2 : p ^ k ∣ t2 := by
        have h := pow_padicValNat_dvd (p := p) (n := t2); rwa [hval2] at h
      calc t1 = p ^ k * (t1 / p ^ k) := (Nat.mul_div_cancel' hd1).symm
        _ = p ^ k * (t2 / p ^ k) := by
              exact congrArg (fun u => p ^ k * u) (show t1 / p ^ k = t2 / p ^ k from heq)
        _ = t2 := Nat.mul_div_cancel' hd2
  · have hempty : (Finset.range (p ^ M)).filter (fun t : ℕ => padicValNat p t = k) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro t hlt hval
      have hlt' : t < p ^ M := Finset.mem_range.mp hlt
      have hk1 : 1 ≤ k := by omega
      have htne : t ≠ 0 := by
        intro h0
        rw [h0] at hval
        simp at hval
        omega
      have hdvd : p ^ k ∣ t := by
        have h := pow_padicValNat_dvd (p := p) (n := t); rwa [hval] at h
      have hle : p ^ k ≤ t := Nat.le_of_dvd (Nat.pos_of_ne_zero htne) hdvd
      have hlt2 : p ^ M < p ^ k := Nat.pow_lt_pow_right (by omega : 1 < p) (by omega : M < k)
      omega
    rw [hempty]
    simp

end Work.LinnikBurgess
