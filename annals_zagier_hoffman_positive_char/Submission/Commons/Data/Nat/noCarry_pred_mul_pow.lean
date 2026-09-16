import Mathlib.Algebra.Order.Ring.Nat

namespace Commons.Data.Nat

/-- `(m * n - 1) / m = n - 1` for `0 < m`, `1 ≤ n`. -/
private lemma mul_sub_one_div (m n : ℕ) (hm : 0 < m) (hn : 1 ≤ n) :
    (m * n - 1) / m = n - 1 := by
  have hmul : m ≤ m * n := by
    calc m = m * 1 := (mul_one m).symm
      _ ≤ m * n := Nat.mul_le_mul_left m hn
  have hdec : m * n - 1 = m * (n - 1) + (m - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    omega
  rw [hdec]
  rw [Nat.mul_add_div hm]
  rw [Nat.div_eq_of_lt (show m - 1 < m by omega)]
  rw [add_zero]

/-- If `M ∣ N` with `M, N ≥ 1` then `(N - 1) % M = M - 1`. -/
private lemma sub_one_mod_of_dvd {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hd : M ∣ N) :
    (N - 1) % M = M - 1 := by
  obtain ⟨t, rfl⟩ := hd
  have ht : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h
      simp at hN
    · exact h
  have hMt : M ≤ M * t := by
    calc M = M * 1 := (mul_one M).symm
      _ ≤ M * t := Nat.mul_le_mul_left M ht
  have hdec : M * t - 1 = M * (t - 1) + (M - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    omega
  rw [hdec]
  rw [Nat.mul_add_mod_self_left]
  rw [Nat.mod_eq_of_lt (show M - 1 < M by omega)]

/-- If `s % M = M - 1` and `s ≤ 2 * (M - 1)` then `s = M - 1`. -/
private lemma eq_of_mod_eq_pred_of_le {M s : ℕ} (hM : 1 ≤ M) (h : s % M = M - 1)
    (hs : s ≤ 2 * (M - 1)) : s = M - 1 := by
  have hs' : s = M * (s / M) + (M - 1) := by
    have := Nat.div_add_mod s M
    rw [h] at this
    exact this.symm
  have hdiv : s / M = 0 := by
    by_contra hne
    have hge : 1 ≤ s / M := Nat.one_le_iff_ne_zero.mpr hne
    have hmul : M ≤ M * (s / M) := by
      calc M = M * 1 := (mul_one M).symm
        _ ≤ M * (s / M) := Nat.mul_le_mul_left M hge
    omega
  rw [hdiv, mul_zero, zero_add] at hs'
  exact hs'

/-- The floors obey `a / c + b / c ≤ (a + b) / c` for `0 < c`. -/
private lemma div_add_div_le {c : ℕ} (hc : 0 < c) (a b : ℕ) :
    a / c + b / c ≤ (a + b) / c := by
  have ha : a / c * c ≤ a := by
    have h := Nat.div_add_mod a c
    rw [Nat.mul_comm c (a / c)] at h
    omega
  have hb : b / c * c ≤ b := by
    have h := Nat.div_add_mod b c
    rw [Nat.mul_comm c (b / c)] at h
    omega
  rw [Nat.le_div_iff_mul_le hc, Nat.add_mul]
  exact Nat.add_le_add ha hb

theorem noCarry_pred_mul_pow (p f x : ℕ) (hp : 2 ≤ p) (hf : 1 ≤ f) (hx : 1 ≤ x) (hxq : x ≤ p ^ f) (i : ℕ) : (p ^ f - 1) * x / p ^ i % p + (x - 1) / p ^ i % p < p := by
  have _hf : 1 ≤ f := hf
  have hp0 : 0 < p := by omega
  have hp1 : 1 ≤ p := by omega
  rcases Nat.lt_or_ge i f with hif | hfi
  · -- Case `i < f`: the addition `(p^f - 1) * x + (x - 1) = p^f * x - 1` is carry-free
    -- at position `i`.
    have hMpos : 0 < p ^ (i + 1) := pow_pos hp0 _
    have hMeq : p ^ (i+1) = p ^ i * p := pow_succ p i
    have hdvd : p ^ (i+1) ∣ p ^ f := Nat.pow_dvd_pow p (by omega : i + 1 ≤ f)
    set A := (p ^ f - 1) * x with hA
    set B := x - 1 with hB
    have hpx1 : 1 ≤ p ^ f * x := by
      have : 1 ≤ p ^ f := Nat.one_le_pow f p hp0
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hAB : A + B = p ^ f * x - 1 := by
      rw [hA, hB]
      have hsub : (p ^ f - 1) * x = p ^ f * x - x := by rw [Nat.sub_mul, one_mul]
      rw [hsub]
      have hxle : x ≤ p ^ f * x := by
        calc x = 1 * x := (one_mul x).symm
          _ ≤ p ^ f * x := Nat.mul_le_mul_right x (Nat.one_le_pow f p hp0)
      omega
    have hABmod : (A + B) % p ^ (i+1) = p ^ (i+1) - 1 := by
      rw [hAB]
      exact sub_one_mod_of_dvd (Nat.one_le_pow (i+1) p hp0) hpx1 (dvd_mul_of_dvd_left hdvd x)
    -- The two remainders modulo `p^(i+1)` add up to `p^(i+1) - 1`.
    have hs_eq : A % p ^ (i+1) + B % p ^ (i+1) = p ^ (i+1) - 1 := by
      have hmod : (A % p ^ (i+1) + B % p ^ (i+1)) % p ^ (i+1) = p ^ (i+1) - 1 := by
        rw [← Nat.add_mod A B (p ^ (i+1)), hABmod]
      apply eq_of_mod_eq_pred_of_le (Nat.one_le_pow (i+1) p hp0) hmod
      have hAM : A % p ^ (i+1) ≤ p ^ (i+1) - 1 := by
        have := Nat.mod_lt A hMpos; omega
      have hBM : B % p ^ (i+1) ≤ p ^ (i+1) - 1 := by
        have := Nat.mod_lt B hMpos; omega
      omega
    have hAmod : A / p ^ i % p = A % p ^ (i+1) / p ^ i := by
      rw [hMeq]; exact (Nat.mod_mul_right_div_self A (p ^ i) p).symm
    have hBmod : B / p ^ i % p = B % p ^ (i+1) / p ^ i := by
      rw [hMeq]; exact (Nat.mod_mul_right_div_self B (p ^ i) p).symm
    rw [hAmod, hBmod]
    have hle : A % p ^ (i+1) / p ^ i + B % p ^ (i+1) / p ^ i ≤ p - 1 := by
      calc A % p ^ (i+1) / p ^ i + B % p ^ (i+1) / p ^ i
          ≤ (A % p ^ (i+1) + B % p ^ (i+1)) / p ^ i :=
            div_add_div_le (pow_pos hp0 i) _ _
        _ = (p ^ (i+1) - 1) / p ^ i := by rw [hs_eq]
        _ = p - 1 := by rw [hMeq]; exact mul_sub_one_div (p ^ i) p (pow_pos hp0 i) hp1
    omega
  · -- Case `f ≤ i`: the second term vanishes and the first is a digit.
    have hB0 : (x - 1) / p ^ i = 0 := by
      apply Nat.div_eq_of_lt
      have hxf : x - 1 < p ^ f := by
        have : 1 ≤ p ^ f := Nat.one_le_pow f p hp0
        omega
      have hfi' : p ^ f ≤ p ^ i := Nat.pow_le_pow_right hp0 hfi
      omega
    rw [hB0, Nat.zero_mod, add_zero]
    exact Nat.mod_lt _ hp0

end Commons.Data.Nat