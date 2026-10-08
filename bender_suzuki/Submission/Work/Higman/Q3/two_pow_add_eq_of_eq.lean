import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3

private lemma one_le_two_pow (n : ℕ) : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)

private lemma even_two_pow {n : ℕ} (hn : 1 ≤ n) : Even (2 ^ n) := by
  rw [Nat.even_pow]; exact ⟨even_two, by omega⟩

private lemma even_two_pow_iff (n : ℕ) : Even (2 ^ n) ↔ n ≠ 0 := by
  rw [Nat.even_pow]; exact ⟨fun h => h.2, fun h => ⟨even_two, h⟩⟩

private lemma odd_two_pow_iff (n : ℕ) : Odd (2 ^ n) ↔ n = 0 := by
  rw [← Nat.not_even_iff_odd, even_two_pow_iff]; simp

private lemma even_two_pow_add_iff (c d : ℕ) : Even (2 ^ c + 2 ^ d) ↔ (c ≠ 0 ↔ d ≠ 0) := by
  rw [Nat.even_add, even_two_pow_iff, even_two_pow_iff]

private lemma odd_two_pow_add_iff (c d : ℕ) : Odd (2 ^ c + 2 ^ d) ↔ (c = 0 ↔ d ≠ 0) := by
  rw [Nat.odd_add, odd_two_pow_iff, even_two_pow_iff]

private lemma two_le_two_pow {n : ℕ} (hn : 1 ≤ n) : 2 ≤ 2 ^ n := by
  have h : n ≠ 0 := by omega
  have := Nat.one_lt_two_pow h
  omega

private lemma two_pow_inj {m n : ℕ} (h : 2 ^ m = 2 ^ n) : m = n :=
  Nat.pow_right_injective (le_refl 2) h

private lemma pow_succ_div_two (n : ℕ) (hn : 0 < n) : 2 ^ n = 2 * 2 ^ (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  rw [pow_succ']; congr 1

theorem two_pow_add_eq_of_eq {a b c d : ℕ} (h : 2 ^ a + 2 ^ b = 2 ^ c + 2 ^ d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have key : ∀ n, ∀ a b c d, a + b = n → 2 ^ a + 2 ^ b = 2 ^ c + 2 ^ d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b c d hab h
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha
        rcases Nat.eq_zero_or_pos b with hb | hb
        · -- a = 0, b = 0
          subst hb
          have h2 : 2 ^ c + 2 ^ d = 2 := by rw [← h]; norm_num
          have hcl : 1 ≤ 2 ^ c := one_le_two_pow c
          have hdl : 1 ≤ 2 ^ d := one_le_two_pow d
          have hc1 : 2 ^ c = 1 := by omega
          have hd1 : 2 ^ d = 1 := by omega
          have hc0 : c = 0 := two_pow_inj (by rw [hc1, pow_zero])
          have hd0 : d = 0 := two_pow_inj (by rw [hd1, pow_zero])
          left; exact ⟨hc0.symm, hd0.symm⟩
        · -- a = 0, b > 0
          have hoddL : Odd (2 ^ 0 + 2 ^ b) := by
            have := (odd_one : Odd (1 : ℕ)).add_even (even_two_pow (by omega : 1 ≤ b))
            simpa using this
          have hodd : Odd (2 ^ c + 2 ^ d) := h ▸ hoddL
          have hiff : (c = 0 ↔ d ≠ 0) := (odd_two_pow_add_iff c d).mp hodd
          rcases eq_or_ne c 0 with hc | hc
          · have hbd : b = d := by
              have h2 := h; rw [hc] at h2
              exact two_pow_inj (Nat.add_left_cancel h2)
            left; exact ⟨hc.symm, hbd⟩
          · have hd : d = 0 := by by_contra hd; exact hc (hiff.mpr hd)
            have hbc : b = c := by
              have h2 : 2 ^ b + 2 ^ 0 = 2 ^ c + 2 ^ 0 := by
                rw [Nat.add_comm (2 ^ b) (2 ^ 0), h, hd]
              exact two_pow_inj (Nat.add_right_cancel h2)
            right; exact ⟨hd.symm, hbc⟩
      · rcases Nat.eq_zero_or_pos b with hb | hb
        · -- a > 0, b = 0
          subst hb
          have hoddL : Odd (2 ^ a + 2 ^ 0) := by
            rw [Nat.add_comm]
            exact (odd_one : Odd (1 : ℕ)).add_even (even_two_pow (by omega : 1 ≤ a))
          have hodd : Odd (2 ^ c + 2 ^ d) := h ▸ hoddL
          have hiff : (c = 0 ↔ d ≠ 0) := (odd_two_pow_add_iff c d).mp hodd
          rcases eq_or_ne d 0 with hd | hd
          · have hac : a = c := by
              have h2 := h; rw [hd] at h2
              exact two_pow_inj (Nat.add_right_cancel h2)
            left; exact ⟨hac, hd.symm⟩
          · have hc0 : c = 0 := hiff.mpr hd
            have had : a = d := by
              have h2 : 2 ^ a + 2 ^ 0 = 2 ^ d + 2 ^ 0 := by
                rw [h, hc0, Nat.add_comm (2 ^ 0) (2 ^ d)]
              exact two_pow_inj (Nat.add_right_cancel h2)
            right; exact ⟨had, hc0.symm⟩
        · -- a > 0, b > 0
          have hevL : Even (2 ^ a + 2 ^ b) :=
            (even_two_pow (by omega : 1 ≤ a)).add (even_two_pow (by omega : 1 ≤ b))
          have hev : Even (2 ^ c + 2 ^ d) := h ▸ hevL
          have hiff := (even_two_pow_add_iff c d).mp hev
          have hcb : c ≠ 0 := by
            intro hc0
            have hd0 : d = 0 := by by_contra hd; exact (hiff.mpr hd) hc0
            exfalso
            have hR : 2 ^ c + 2 ^ d = 2 := by rw [hc0, hd0]; norm_num
            have hL : 4 ≤ 2 ^ a + 2 ^ b := by
              have ha2 := two_le_two_pow (by omega : 1 ≤ a)
              have hb2 := two_le_two_pow (by omega : 1 ≤ b)
              omega
            rw [h, hR] at hL
            omega
          have hdb : d ≠ 0 := hiff.mp hcb
          have hdiv : 2 ^ (a - 1) + 2 ^ (b - 1) = 2 ^ (c - 1) + 2 ^ (d - 1) := by
            have hh : 2 * (2 ^ (a - 1) + 2 ^ (b - 1)) =
                2 * (2 ^ (c - 1) + 2 ^ (d - 1)) := by
              have h2 := h
              rw [pow_succ_div_two a ha, pow_succ_div_two b hb,
                  pow_succ_div_two c (Nat.pos_of_ne_zero hcb),
                  pow_succ_div_two d (Nat.pos_of_ne_zero hdb)] at h2
              rw [Nat.mul_add, Nat.mul_add]
              exact h2
            exact Nat.mul_left_cancel (by norm_num) hh
          have hlt : a - 1 + (b - 1) < n := by omega
          rcases ih (a - 1 + (b - 1)) hlt (a - 1) (b - 1) (c - 1) (d - 1) rfl hdiv with
            ⟨h1, h2⟩ | ⟨h1, h2⟩
          · left; exact ⟨by omega, by omega⟩
          · right; exact ⟨by omega, by omega⟩
  exact key (a + b) a b c d rfl h

end Work.Higman.Q3
