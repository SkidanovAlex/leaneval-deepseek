import Mathlib

namespace Work.LinnikBurgess

/-- For a prime `p` and `a ≠ 0` with `padicValNat p a < K`, the complement
`p ^ K - a % p ^ K` of the residue `a % p ^ K` in `[0, p ^ K)` has the same
`p`-adic valuation as `a`.

Indeed `a = q · p ^ K + b` with `b = a % p ^ K < p ^ K`, and `p ^ K - b` is
congruent to `-b` modulo `p ^ K`; since none of the `p`-power dividing `a`
can divide `p ^ K` (as `padicValNat p a < K`), the valuation is unchanged. -/
lemma padicValNat_pow_sub_mod {p K a : ℕ} [Fact p.Prime] (ha : a ≠ 0)
    (h : padicValNat p a < K) :
    padicValNat p (p ^ K - a % p ^ K) = padicValNat p a := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  set v := padicValNat p a with hv
  set b := a % p ^ K with hb
  have hb_lt : b < p ^ K := Nat.mod_lt _ (pow_pos hp0 K)
  -- `p ^ v` is the exact `p`-power dividing `a`
  have hpv_a : p ^ v ∣ a := by rw [hv]; exact pow_padicValNat_dvd
  have hpv1_not_a : ¬ p ^ (v + 1) ∣ a := by
    rw [hv]; exact pow_succ_padicValNat_not_dvd ha
  -- reduction of `a` modulo `p ^ K`
  have hmad : b + p ^ K * (a / p ^ K) = a := by
    have := Nat.mod_add_div a (p ^ K)
    rwa [← hb] at this
  -- the valuation of the residue is the same as that of `a`
  have hpv_pk : p ^ v ∣ p ^ K := pow_dvd_pow p (le_of_lt h)
  have hsub : a - p ^ K * (a / p ^ K) = b := Nat.sub_eq_of_eq_add hmad.symm
  have hpv_b : p ^ v ∣ b := by
    rw [← hsub]
    exact Nat.dvd_sub hpv_a (dvd_mul_of_dvd_left hpv_pk _)
  have hpv1_not_b : ¬ p ^ (v + 1) ∣ b := by
    intro hb1
    apply hpv1_not_a
    have hpv1_pk : p ^ (v + 1) ∣ p ^ K := pow_dvd_pow p (by omega)
    have : p ^ (v + 1) ∣ b + p ^ K * (a / p ^ K) :=
      dvd_add hb1 (dvd_mul_of_dvd_left hpv1_pk _)
    rwa [hmad] at this
  -- `p ^ K - b` is nonzero, so the `dvd`-characterisation of `padicValNat` applies
  have hne : p ^ K - b ≠ 0 := by omega
  have hlow : v ≤ padicValNat p (p ^ K - b) :=
    (padicValNat_dvd_iff_le hne).mp (Nat.dvd_sub hpv_pk hpv_b)
  have hup : padicValNat p (p ^ K - b) ≤ v := by
    by_contra hc
    have hdiv : p ^ (v + 1) ∣ p ^ K - b :=
      (padicValNat_dvd_iff_le hne).mpr (by omega)
    have hpv1_pk : p ^ (v + 1) ∣ p ^ K := pow_dvd_pow p (by omega)
    have : p ^ (v + 1) ∣ b := by
      have := Nat.dvd_sub hpv1_pk hdiv
      rwa [Nat.sub_sub_self (le_of_lt hb_lt)] at this
    exact hpv1_not_b this
  exact le_antisymm hup hlow

end Work.LinnikBurgess
