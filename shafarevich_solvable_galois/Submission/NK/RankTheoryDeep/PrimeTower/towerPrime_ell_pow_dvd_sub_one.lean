import Mathlib
import Submission.NK.RankTheoryDeep.PrimeTower.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.RankTheoryDeep.PrimeTower

/-- **The `ℓ`-adic valuation of a tower-prime divisor.**

If a prime `p` divides `towerNum ℓ k = ∑_{i < ℓ} ℓ ^ (i * ℓ ^ (k - 1))` and `k ≥ 1`, then the
multiplicative order of `ℓ` in `(ZMod p)ˣ` is exactly `ℓ ^ k`; hence `ℓ ^ k ∣ p - 1` by Lagrange.
Applying this with `p = towerPrime ℓ n = (towerNum ℓ (n + 1)).minFac` and `k = n + 1` gives the
statement. -/
theorem towerPrime_ell_pow_dvd_sub_one (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    ℓ ^ (n + 1) ∣ towerPrime ℓ n - 1 := by
  have hℓprime : ℓ.Prime := Fact.out
  haveI : Fact (towerPrime ℓ n).Prime := ⟨towerPrime_prime ℓ n⟩
  have hdiv : towerPrime ℓ n ∣ towerNum ℓ (n + 1) := towerPrime_dvd ℓ n
  -- `p = towerPrime ℓ n` is not `ℓ`, since `ℓ ∤ towerNum ℓ (n + 1)`.
  have hpne : towerPrime ℓ n ≠ ℓ := by
    intro h
    have hh : towerPrime ℓ n ∣ towerNum ℓ (n + 1) := hdiv
    rw [h] at hh
    exact not_dvd_towerNum ℓ (n + 1) hh
  -- hence `ℓ` is a unit modulo `p`.
  have hℓne : (ℓ : ZMod (towerPrime ℓ n)) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    rcases (Nat.dvd_prime hℓprime).mp h0 with h1 | h1
    · exact (towerPrime_prime ℓ n).ne_one h1
    · exact hpne h1
  obtain ⟨u, huval⟩ : ∃ u : (ZMod (towerPrime ℓ n))ˣ,
      (u : ZMod (towerPrime ℓ n)) = (ℓ : ZMod (towerPrime ℓ n)) :=
    ⟨Units.mk0 _ hℓne, by rw [Units.val_mk0]⟩
  -- `towerNum ℓ (n+1) ≡ 0 (mod p)`.
  have hsum0 : ((towerNum ℓ (n + 1) : ℕ) : ZMod (towerPrime ℓ n)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact hdiv
  have hk : 1 ≤ n + 1 := Nat.le_add_left 1 n
  -- the geometric-sum identity: `towerNum ℓ (n+1) * (ℓ ^ (ℓ ^ n) - 1) = ℓ ^ (ℓ ^ (n+1)) - 1`.
  have hgeom := cast_towerNum_mul (ℓ := ℓ) (k := n + 1) (p := towerPrime ℓ n) hk
  rw [hsum0, zero_mul] at hgeom
  have hpow : (ℓ : ZMod (towerPrime ℓ n)) ^ (ℓ ^ (n + 1)) = 1 :=
    sub_eq_zero.mp hgeom.symm
  have hupow : u ^ (ℓ ^ (n + 1)) = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, huval]
    exact hpow
  have hdvd : orderOf u ∣ ℓ ^ (n + 1) := orderOf_dvd_of_pow_eq_one hupow
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow hℓprime).mp hdvd
  -- `orderOf u` does not divide `ℓ ^ n`: otherwise `ℓ ^ (ℓ ^ n) = 1`, so `towerNum ℓ (n+1) ≡ ℓ`
  -- modulo `p`, contradicting `p ∣ towerNum ℓ (n+1)` in view of `p ≠ ℓ`.
  have hjnot : ¬ (j ≤ n) := by
    intro hjn
    have hdvdn : orderOf u ∣ ℓ ^ n := by rw [hj]; exact pow_dvd_pow ℓ hjn
    have hu1 : u ^ (ℓ ^ n) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvdn
    have hr : (ℓ : ZMod (towerPrime ℓ n)) ^ (ℓ ^ n) = 1 := by
      have := congrArg (fun x : (ZMod (towerPrime ℓ n))ˣ => (x : ZMod (towerPrime ℓ n))) hu1
      rwa [Units.val_pow_eq_pow_val, Units.val_one, huval] at this
    have hsumℓ : ((towerNum ℓ (n + 1) : ℕ) : ZMod (towerPrime ℓ n))
        = (ℓ : ZMod (towerPrime ℓ n)) := by
      rw [cast_towerNum ℓ (n + 1) (towerPrime ℓ n), show (n + 1) - 1 = n from by omega]
      have h1 : ∀ i ∈ Finset.range ℓ, ((ℓ : ZMod (towerPrime ℓ n)) ^ (ℓ ^ n)) ^ i = 1 :=
        fun i _ => by rw [hr, one_pow]
      rw [Finset.sum_congr rfl h1]
      simp [Finset.sum_const, Finset.card_range]
    have : (ℓ : ZMod (towerPrime ℓ n)) = 0 := by rw [← hsumℓ, hsum0]
    exact hℓne this
  have hjeq : j = n + 1 := by omega
  have horder : orderOf u = ℓ ^ (n + 1) := by rw [hj, hjeq]
  -- Lagrange: `orderOf u ∣ #(ZMod p)ˣ = p - 1`.
  have hcard : orderOf u ∣ Fintype.card (ZMod (towerPrime ℓ n))ˣ := orderOf_dvd_card
  rw [ZMod.card_units] at hcard
  rw [horder] at hcard
  exact hcard

end NK.RankTheoryDeep.PrimeTower
