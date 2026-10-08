import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- An odd divisor of a power of two equals one. -/
theorem p2a_odd_dvd_two_pow {a k : ℕ} (ha : Odd a) (h : a ∣ 2 ^ k) : a = 1 := by
  have hc : Nat.Coprime a (2 ^ k) := (Nat.coprime_two_right.mpr ha).pow_right k
  exact hc.eq_one_of_dvd h

/-- A geometric sum of an odd number of odd terms is odd. -/
theorem p2a_geom_sum_odd {f m : ℕ} (hf : Odd f) (hm : Odd m) :
    Odd (∑ i ∈ Finset.range m, f ^ i) := by
  rw [Finset.odd_sum_iff_odd_card_odd]
  have hfil : {x ∈ Finset.range m | Odd (f ^ x)} = Finset.range m := by
    apply Finset.filter_true_of_mem
    intro x _
    exact Odd.pow hf
  rw [hfil, Finset.card_range]
  exact hm

theorem p2a_arith {f m k : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hm : 2 ≤ m)
    (h : f ^ m = 2 ^ k + 1) : f = 3 := by
  have hf_odd : Odd f := hf.odd_of_ne_two hf2
  have hf3 : 3 ≤ f := by
    rcases hf_odd with ⟨j, hj⟩
    have h2 := hf.two_le
    omega
  have hf1 : 1 ≤ f := by omega
  rcases Nat.even_or_odd m with hm_even | hm_odd
  · -- `m` is even, write `m = n + n`; then `f ^ n` is odd with square `2 ^ k + 1`.
    obtain ⟨n, rfl⟩ := hm_even
    have hn : n ≠ 0 := by omega
    set a := f ^ n with ha
    have hsq : a ^ 2 = 2 ^ k + 1 := by
      rw [ha, pow_two, ← pow_add]; exact h
    have ha3 : 3 ≤ a := by
      rw [ha]
      exact le_trans hf3 (Nat.le_self_pow hn f)
    have hpred : a ^ 2 - 1 = 2 ^ k := by rw [hsq, Nat.add_sub_cancel]
    have hfac : (a + 1) * (a - 1) = 2 ^ k := by
      have h2 : a ^ 2 - 1 = (a + 1) * (a - 1) := by
        have h := Nat.sq_sub_sq a 1
        rw [one_pow] at h
        exact h
      rw [← h2]; exact hpred
    have hBdvd : a + 1 ∣ 2 ^ k := ⟨a - 1, hfac.symm⟩
    have hAdvd : a - 1 ∣ 2 ^ k :=
      ⟨a + 1, by rw [mul_comm (a - 1) (a + 1)]; exact hfac.symm⟩
    obtain ⟨p, -, hAp⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hAdvd
    obtain ⟨q, -, hBq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hBdvd
    have hp1 : 1 ≤ p := by
      rcases p with _ | p
      · simp only [pow_zero] at hAp; omega
      · omega
    have hsum : 2 ^ q = 2 ^ p + 2 := by omega
    have hpq : p < q := by
      have hlt : 2 ^ p < 2 ^ q := by omega
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    have hp_dvd : 2 ^ p ∣ 2 := by
      have h1 : 2 ^ p ∣ 2 ^ p + 2 := by
        have := pow_dvd_pow 2 (le_of_lt hpq)
        rwa [hsum] at this
      exact (Nat.dvd_add_iff_right (dvd_refl (2 ^ p))).mpr h1
    have hp_le1 : p ≤ 1 :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp (by simpa using hp_dvd)
    have hp_eq : p = 1 := by omega
    have ha_eq : a = 3 := by
      rw [hp_eq, pow_one] at hAp
      omega
    have hfdvd : f ∣ 3 := by
      have h1 : f ∣ f ^ n := dvd_pow_self f hn
      rw [← ha] at h1
      rwa [ha_eq] at h1
    have : f ≤ 3 := Nat.le_of_dvd (by norm_num) hfdvd
    omega
  · -- `m` odd: the geometric sum `S = f ^ (m-1) + ... + f + 1` is odd and divides `2 ^ k`.
    have hk : f ^ m - 1 = 2 ^ k := by rw [h, Nat.add_sub_cancel]
    set S := ∑ i ∈ Finset.range m, f ^ i with hS
    have hS_odd : Odd S := by rw [hS]; exact p2a_geom_sum_odd hf_odd hm_odd
    have hid : S * (f - 1) + 1 = f ^ m := by
      have hh := geom_sum_mul_add (f - 1) m
      rw [Nat.sub_add_cancel hf1] at hh
      rw [hS]; exact hh
    have hid2 : S * (f - 1) + 1 = 2 ^ k + 1 := by rw [hid, h]
    have hS_eq : S * (f - 1) = 2 ^ k := Nat.add_right_cancel hid2
    have hS_dvd : S ∣ 2 ^ k := ⟨f - 1, hS_eq.symm⟩
    have hS1 : S = 1 := p2a_odd_dvd_two_pow hS_odd hS_dvd
    have hmem : 1 ∈ Finset.range m := by simp only [Finset.mem_range]; omega
    have hSge : f ^ 1 ≤ S := by
      rw [hS]
      exact Finset.single_le_sum (fun i _ => Nat.zero_le _) hmem
    rw [hS1] at hSge
    simp only [pow_one] at hSge
    omega

end Work.NormalComplement
