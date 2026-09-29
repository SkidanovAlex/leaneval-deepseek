import Mathlib

namespace Work.TMC16Core.Assembly

/-- Arithmetic core of the exceptional case: if `Q = 2k` (as naturals) and
`Q^(8/9) = k` (as reals), with `Q > 0`, then necessarily `Q = 512`. -/
private lemma eq_512_of_eq_two_mul_rpow {Q k : ℕ}
    (hQ : (Q : ℝ) = 2 * (k : ℝ))
    (hk : (Q : ℝ) ^ ((8 : ℝ) / 9) = (k : ℝ))
    (hQpos : 0 < Q) : Q = 512 := by
  have hr : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
  have h : (Q : ℝ) = 2 * (Q : ℝ) ^ ((8 : ℝ) / 9) := by rw [hk]; exact hQ
  have hpow : (Q : ℝ) ^ 9 = (2 * (Q : ℝ) ^ ((8 : ℝ) / 9)) ^ 9 := by rw [← h]
  have hsq : ((Q : ℝ) ^ ((8 : ℝ) / 9)) ^ 9 = (Q : ℝ) ^ 8 := by
    rw [← Real.rpow_natCast ((Q : ℝ) ^ ((8 : ℝ) / 9)) 9]
    rw [← Real.rpow_mul (le_of_lt hr)]
    rw [show ((8 : ℝ) / 9) * ((9 : ℕ) : ℝ) = (8 : ℝ) by norm_num]
    exact Real.rpow_natCast (Q : ℝ) 8
  have h9 : (Q : ℝ) ^ 9 = 512 * (Q : ℝ) ^ 8 := by
    rw [hpow, mul_pow, hsq]; norm_num
  have hr9 : (Q : ℝ) ^ 9 = (Q : ℝ) ^ 8 * (Q : ℝ) := by ring
  have hne : (Q : ℝ) ^ 8 ≠ 0 := pow_ne_zero 8 (ne_of_gt hr)
  have heq : (Q : ℝ) ^ 8 * (Q : ℝ) = (Q : ℝ) ^ 8 * 512 := by
    rw [← hr9, h9]; ring
  have : (Q : ℝ) = 512 := mul_left_cancel₀ hne heq
  exact_mod_cast this

theorem nr_s_exists {Q qq k : ℕ}
    (hQ9 : 3 ^ 9 < Q) (hqq : 72 ≤ qq)
    (hk : 3 * qq + 1 ≤ k) (hkQ : 2 * k ≤ Q)
    (hkR : Real.rpow (Q : ℝ) ((8 : ℝ) / 9) ≤ (k : ℝ)) :
    ∃ s : ℕ, 3 ≤ s ∧ s * qq ≤ k ∧ 2 * (s * qq) < Q ∧
      Real.rpow (Q : ℝ) ((8 : ℝ) / 9) < (((s + 1) * qq : ℕ) : ℝ) := by
  have hqq_pos : 0 < qq := by omega
  set t : ℕ := k / qq with ht
  have ht_le : t * qq ≤ k := by rw [ht]; exact Nat.div_mul_le_self k qq
  have hkey : k = t * qq + k % qq := by
    rw [ht, mul_comm (k / qq) qq]
    exact (Nat.div_add_mod k qq).symm
  have hk_lt : k < (t + 1) * qq := by
    have hmod : k % qq < qq := Nat.mod_lt k hqq_pos
    calc k = t * qq + k % qq := hkey
      _ < t * qq + qq := by omega
      _ = (t + 1) * qq := by ring
  have ht_ge3 : 3 ≤ t := by
    rw [ht, Nat.le_div_iff_mul_le hqq_pos]
    omega
  by_cases hgood : 2 * (t * qq) < Q
  · refine ⟨t, ht_ge3, ht_le, hgood, ?_⟩
    have hcast : (k : ℝ) < (((t + 1) * qq : ℕ) : ℝ) := by exact_mod_cast hk_lt
    linarith
  · have h2t_le : 2 * (t * qq) ≤ Q := by
      have h2 : 2 * (t * qq) ≤ 2 * k := Nat.mul_le_mul_left 2 ht_le
      omega
    have hQeq : 2 * (t * qq) = Q := le_antisymm h2t_le (not_lt.mp hgood)
    have htq : t * qq = k := by
      have h2 : 2 * (t * qq) ≤ 2 * k := Nat.mul_le_mul_left 2 ht_le
      have h3 : 2 * k ≤ 2 * (t * qq) := by rw [hQeq]; exact hkQ
      have h4 : 2 * k = 2 * (t * qq) := le_antisymm h3 h2
      omega
    have hQ2k : Q = 2 * k := by rw [← hQeq, htq]
    by_cases hkbig : Real.rpow (Q : ℝ) ((8 : ℝ) / 9) < (k : ℝ)
    · have ht_ge4 : 4 ≤ t := by
        by_contra h
        have ht3 : t ≤ 3 := by omega
        have hle : t * qq ≤ 3 * qq := Nat.mul_le_mul_right qq ht3
        omega
      refine ⟨t - 1, by omega, ?_, ?_, ?_⟩
      · have hle : (t - 1) * qq ≤ t * qq := Nat.mul_le_mul_right qq (Nat.sub_le t 1)
        omega
      · have hlt : (t - 1) * qq < t * qq := by
          have htlt : t - 1 < t := by omega
          exact (Nat.mul_lt_mul_right hqq_pos).mpr htlt
        have h2lt : 2 * ((t - 1) * qq) < 2 * (t * qq) :=
          (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).mpr hlt
        omega
      · have hs1 : t - 1 + 1 = t := Nat.sub_one_add_one_eq_of_pos (by omega)
        rw [hs1]
        have hcast : (((t * qq : ℕ)) : ℝ) = (k : ℝ) := by rw [htq]
        rw [hcast]
        exact hkbig
    · exfalso
      have hkQ9 : (Q : ℝ) ^ ((8 : ℝ) / 9) = (k : ℝ) := le_antisymm hkR (not_lt.mp hkbig)
      have hQpos : 0 < Q := by omega
      have h512 : Q = 512 :=
        eq_512_of_eq_two_mul_rpow (by exact_mod_cast hQ2k) hkQ9 hQpos
      rw [h512] at hQ9
      norm_num at hQ9

end Work.TMC16Core.Assembly
