import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A lifting-the-exponent computation

For an odd prime `p` the `p`-adic valuation of `(1 + m * p) ^ p - 1` is `2 + v_p(m)`.
Equivalently, `p ^ n` divides `(1 + m * p) ^ p - 1` iff `p ^ (n - 2)` divides `m`.

This is the arithmetic input controlling the `p`-adic order of `1 + m * p` in a cyclic group
of `p`-power order (used in the analysis of the symplectic-type `p`-groups, FT 3.5).
-/

set_option linter.style.haveILetI false

namespace Work.PGroup.Symplectic

/-- For an odd prime `p`, `p ^ n ∣ (1 + m * p) ^ p - 1 ↔ p ^ (n - 2) ∣ m`
(equivalently `v_p ((1 + m * p) ^ p - 1) = v_p m + 2`). -/
theorem prime_pow_dvd_pow_pred_one_iff {p n m : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hn : 2 ≤ n) :
    p ^ n ∣ (1 + m * p) ^ p - 1 ↔ p ^ (n - 2) ∣ m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hodd
  have hm' : m ≠ 0 := hm.ne'
  -- the base `1 + m * p` is congruent to `1` mod `p` but strictly bigger than `1`
  have h1 : 1 < 1 + m * p := by
    have : 0 < m * p := Nat.mul_pos hm hp.pos
    omega
  have h2 : p ∣ (1 + m * p) - 1 := by
    rw [show (1 + m * p) - 1 = m * p by omega]
    exact dvd_mul_left p m
  have h3 : ¬ p ∣ 1 + m * p := by
    intro hd
    have h4 : p ∣ (1 + m * p) - m * p := Nat.dvd_sub hd (dvd_mul_left p m)
    rw [show (1 + m * p) - m * p = 1 by omega] at h4
    exact hp.not_dvd_one h4
  -- the `p`-adic valuation of the difference `x - 1`
  have hbase : padicValNat p ((1 + m * p) - 1) = padicValNat p m + 1 := by
    rw [show (1 + m * p) - 1 = m * p by omega, mul_comm m p,
      padicValNat_base_mul hp.one_lt hm']
  -- lifting the exponent (`padicValNat.pow_sub_pow`) with `n = p`
  have hval : padicValNat p ((1 + m * p) ^ p - 1) = padicValNat p m + 2 := by
    have h := padicValNat.pow_sub_pow (p := p) hpodd h1 h2 h3 hp.ne_zero
    rw [one_pow] at h
    rw [h, hbase, padicValNat_base hp.one_lt]
  have hNne : (1 + m * p) ^ p - 1 ≠ 0 := by
    have : 1 < (1 + m * p) ^ p := Nat.one_lt_pow hp.ne_zero h1
    omega
  rw [Nat.pow_dvd_iff_le_padicValNat hp.ne_one hNne,
      Nat.pow_dvd_iff_le_padicValNat hp.ne_one hm', hval]
  omega

end Work.PGroup.Symplectic
