import Mathlib
import Submission.Work.ZassenhausSuzuki.pow_two_defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- If `2 * oddPart (p² - 1) ≤ p - 1` for an odd prime `p`, then `p` is a Mersenne prime:
`p + 1` is a power of two.

Write `p - 1 = 2 ^ c * t` and `p + 1 = 2 ^ b * s` with `t, s` odd (the odd parts).  Since
`oddPart (p² - 1) = oddPart (p - 1) * oddPart (p + 1) = t * s` and `p - 1 = 2 ^ c * t`, the
hypothesis becomes `2 * s ≤ 2 ^ c`.  Since `p + 1 - (p - 1) = 2` gives `2 ^ b * s = 2 ^ c * t + 2`,
`b` and `c` cannot both be `≥ 2` (a multiple of `4` would equal `2`).  Hence `c = 1` (giving
`s ≤ 1`, so `s = 1`) or else `c ≥ 2`, forcing `b ≤ 1`, so `2 ^ c * t + 2 ≤ 2 ^ b * s ≤ 2 * s ≤ 2 ^ c`,
which is impossible since `t ≥ 1`. -/
theorem p_add_one_eq_pow_two_of_oddPart_bound {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : 2 * oddPart (p ^ 2 - 1) ≤ p - 1) : ∃ j, p + 1 = 2 ^ j := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpm1 : p - 1 ≠ 0 := by omega
  have hpp1 : p + 1 ≠ 0 := by omega
  -- Factorization of `p - 1` and `p + 1` into a power of two times an odd number.
  have hfac_m : 2 ^ ((p - 1).factorization 2) * oddPart (p - 1) = p - 1 :=
    Nat.ordProj_mul_ordCompl_eq_self (p - 1) 2
  have hfac_p : 2 ^ ((p + 1).factorization 2) * oddPart (p + 1) = p + 1 :=
    Nat.ordProj_mul_ordCompl_eq_self (p + 1) 2
  -- `p ^ 2 - 1 = (p - 1) * (p + 1)`
  have hsq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have h' := Nat.sq_sub_sq p 1
    simp only [one_pow] at h'
    rw [h', mul_comm]
  -- hence the odd part is multiplicative here
  have hodd : oddPart (p ^ 2 - 1) = oddPart (p - 1) * oddPart (p + 1) := by
    rw [hsq, oddPart_mul]
  have htpos : 0 < oddPart (p - 1) := oddPart_pos hpm1
  have hspos : 0 < oddPart (p + 1) := oddPart_pos hpp1
  -- `2 * oddPart (p + 1) ≤ 2 ^ (p - 1).factorization 2`
  have h2s : 2 * oddPart (p + 1) ≤ 2 ^ ((p - 1).factorization 2) := by
    have hmain : oddPart (p - 1) * (2 * oddPart (p + 1)) ≤
        2 ^ ((p - 1).factorization 2) * oddPart (p - 1) := by
      calc oddPart (p - 1) * (2 * oddPart (p + 1))
          = 2 * oddPart (p ^ 2 - 1) := by rw [hodd]; ring
        _ ≤ p - 1 := h
        _ = 2 ^ ((p - 1).factorization 2) * oddPart (p - 1) := hfac_m.symm
    rw [mul_comm (2 ^ ((p - 1).factorization 2)) (oddPart (p - 1))] at hmain
    exact Nat.le_of_mul_le_mul_left hmain htpos
  -- `2 ^ b * s = 2 ^ c * t + 2`
  have hrel : 2 ^ ((p + 1).factorization 2) * oddPart (p + 1) =
      2 ^ ((p - 1).factorization 2) * oddPart (p - 1) + 2 := by
    rw [hfac_p, hfac_m]
    omega
  -- `b` and `c` cannot both be `≥ 2`
  have hnotboth : ¬ (2 ≤ (p + 1).factorization 2 ∧ 2 ≤ (p - 1).factorization 2) := by
    rintro ⟨hb, hc⟩
    have h4b : 4 ∣ 2 ^ ((p + 1).factorization 2) * oddPart (p + 1) := by
      obtain ⟨k, hk⟩ := Nat.pow_dvd_pow 2 hb
      exact ⟨k * oddPart (p + 1), by rw [hk]; ring⟩
    have h4c : 4 ∣ 2 ^ ((p - 1).factorization 2) * oddPart (p - 1) := by
      obtain ⟨k, hk⟩ := Nat.pow_dvd_pow 2 hc
      exact ⟨k * oddPart (p - 1), by rw [hk]; ring⟩
    have h4 : 4 ∣ 2 ^ ((p - 1).factorization 2) * oddPart (p - 1) + 2 := by
      rw [← hrel]; exact h4b
    have hsub := Nat.dvd_sub h4 h4c
    rw [Nat.add_sub_cancel_left] at hsub
    exact absurd hsub (by norm_num)
  have hs1 : oddPart (p + 1) = 1 := by
    rcases lt_or_ge ((p - 1).factorization 2) 1 with hc0 | hc1
    · -- `c = 0` is impossible: `2 * s ≤ 1`
      have hc0' : (p - 1).factorization 2 = 0 := by omega
      rw [hc0', pow_zero] at h2s
      omega
    · rcases eq_or_lt_of_le hc1 with hc1' | hc2
      · -- `c = 1`: `2 * s ≤ 2`
        have hc1'' : (p - 1).factorization 2 = 1 := hc1'.symm
        rw [hc1'', pow_one] at h2s
        omega
      · -- `c ≥ 2`: then `b ≤ 1`, and `2 ^ c * t + 2 ≤ 2 ^ b * s ≤ 2 * s ≤ 2 ^ c`
        have hb1 : (p + 1).factorization 2 ≤ 1 := by
          rcases lt_or_ge ((p + 1).factorization 2) 2 with h | h
          · omega
          · exact absurd ⟨h, hc2⟩ hnotboth
        have h2b : 2 ^ ((p + 1).factorization 2) ≤ 2 := by
          calc 2 ^ ((p + 1).factorization 2) ≤ 2 ^ 1 :=
                Nat.pow_le_pow_right (by norm_num) hb1
            _ = 2 := pow_one 2
        have hlt : 2 ^ ((p - 1).factorization 2) * oddPart (p - 1) + 2 ≤
            2 ^ ((p - 1).factorization 2) := by
          rw [← hrel]
          calc 2 ^ ((p + 1).factorization 2) * oddPart (p + 1)
              ≤ 2 * oddPart (p + 1) := Nat.mul_le_mul_right _ h2b
            _ ≤ 2 ^ ((p - 1).factorization 2) := h2s
        have hle : 2 ^ ((p - 1).factorization 2) ≤
            2 ^ ((p - 1).factorization 2) * oddPart (p - 1) :=
          Nat.le_mul_of_pos_right _ htpos
        omega
  exact exists_pow_two_of_oddPart_eq_one hs1

end Work.ZassenhausSuzuki
