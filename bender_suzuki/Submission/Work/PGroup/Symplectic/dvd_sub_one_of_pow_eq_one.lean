import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Lifting the exponent for an odd prime: `p ^ m ∣ κ ^ p - 1`

For an odd prime `p`, if `p ^ m` divides `κ ^ p - 1` but `p ^ m` does not divide `κ - 1`,
then `p ^ (m - 1)` divides `κ - 1`.

This is the `n = 1` case of the classical *lifting the exponent* lemma (LTE) for odd primes:
if `p ∣ κ - 1` then `padicValNat p (κ ^ p - 1) = padicValNat p (κ - 1) + 1`.  The occurrence
in the odd-order theorem is Feit–Thompson 3.5 / P. Hall's classification of `p`-groups of
symplectic type.
-/

set_option linter.style.haveILetI false

namespace Work.PGroup.Symplectic

theorem dvd_sub_one_of_pow_eq_one {p m κ : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (h1 : p ^ m ∣ κ ^ p - 1) (h2 : ¬ p ^ m ∣ κ - 1) : p ^ (m - 1) ∣ κ - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- If `m ≤ 1` the conclusion is `1 ∣ κ - 1`.
  by_cases hm : m ≤ 1
  · have : m - 1 = 0 := by omega
    rw [this, pow_zero]; exact one_dvd _
  · push Not at hm
    -- `h2` forces `κ ≥ 2`.
    have hκ2 : 2 ≤ κ := by
      by_contra h
      have hk : κ - 1 = 0 := by omega
      exact h2 (by rw [hk]; exact dvd_zero _)
    have h1κ : 1 < κ := by omega
    have hκsub : κ - 1 ≠ 0 := by omega
    have hpow_ne : κ ^ p - 1 ≠ 0 := by
      have : 1 < κ ^ p := Nat.one_lt_pow hp.ne_zero h1κ
      omega
    -- `p ∣ κ ^ p - 1`.
    have hpdm : p ∣ p ^ m := dvd_pow_self p (by omega)
    have hpd1 : p ∣ κ ^ p - 1 := dvd_trans hpdm h1
    -- Fermat: `κ ^ p ≡ κ [MOD p]`.
    have hfermat : κ ^ p ≡ κ [MOD p] := by
      have h : ((κ ^ p : ℕ) : ZMod p) = ((κ : ℕ) : ZMod p) := by
        rw [Nat.cast_pow]; exact ZMod.pow_card (κ : ZMod p)
      exact (ZMod.natCast_eq_natCast_iff (κ ^ p) κ p).mp h
    have h1mod : κ ^ p ≡ 1 [MOD p] := by
      have h1le : 1 ≤ κ ^ p := (Nat.one_lt_pow hp.ne_zero h1κ).le
      exact ((Nat.modEq_iff_dvd' h1le).mpr hpd1).symm
    have hκ1 : κ ≡ 1 [MOD p] := hfermat.symm.trans h1mod
    -- Hence `p ∣ κ - 1`, and `¬ p ∣ κ`.
    have hpd_sub : p ∣ κ - 1 := (Nat.modEq_iff_dvd' (show 1 ≤ κ by omega)).mp hκ1.symm
    have h2p : 2 ≤ p := hp.two_le
    have hnpk : ¬ p ∣ κ := by
      intro hpk
      have h1d : p ∣ 1 := by
        have := Nat.dvd_sub hpk hpd_sub
        rwa [show κ - (κ - 1) = 1 by omega] at this
      have := Nat.le_of_dvd (by norm_num) h1d
      omega
    -- Lifting the exponent: `v_p (κ ^ p - 1) = v_p (κ - 1) + 1`.
    have hpodd : Odd p := hp.odd_of_ne_two hodd
    have hLTE := padicValNat.pow_sub_pow (x := κ) (y := 1) (p := p) hpodd h1κ hpd_sub hnpk
      hp.ne_zero
    rw [one_pow, padicValNat_self] at hLTE
    have hv : m ≤ padicValNat p (κ ^ p - 1) := (padicValNat_dvd_iff_le hpow_ne).mp h1
    rw [hLTE] at hv
    have hm1v : m - 1 ≤ padicValNat p (κ - 1) := by omega
    exact (padicValNat_dvd_iff_le hκsub).mpr hm1v

end Work.PGroup.Symplectic
