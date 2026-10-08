import Mathlib
import Submission.Work.PSU3.StageA.geom_sum_modEq_prime_sq
import Submission.Work.PSU3.StageA.geom_sum_modEq_sub_one
import Submission.Work.PSU3.StageA.geom_sum_gt_prime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

open Finset

/-- For `A ≥ 2`, `p` an odd prime, there exists a prime `t` dividing `A ^ p - 1`
which does not divide `A - 1`.

The proof works with `S = ∑ i ∈ range p, A ^ i = (A ^ p - 1) / (A - 1)`:
`(A - 1) * S = A ^ p - 1`, and `gcd S (A - 1) ∣ p`, so a prime dividing `S`
that is not `p` cannot divide `A - 1`.

* If `p ∤ A - 1`, any prime divisor of `S` works.
* If `p ∣ A - 1`, then `p` is the only possible common prime; using the
  congruence `S ≡ p [MOD p ^ 2]` one finds a prime divisor of `S` other than `p`. -/
theorem exists_prime_dvd_pow_sub_one_not_dvd {A p : ℕ} (hA : 2 ≤ A) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ t : ℕ, t.Prime ∧ t ∣ A ^ p - 1 ∧ ¬ t ∣ A - 1 := by
  have hA1 : 1 ≤ A := by omega
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  set S := ∑ i ∈ range p, A ^ i with hSdef
  -- `(A - 1) * S = A ^ p - 1`
  have hSmul : S * (A - 1) = A ^ p - 1 := by
    have h := geom_sum_mul_add (A - 1) p
    rw [Nat.sub_add_cancel hA1] at h
    exact Nat.eq_sub_of_add_eq h
  -- `S ≡ p [MOD (A - 1)]`, hence `gcd S (A - 1) ∣ p`
  have hSmod : Nat.ModEq (A - 1) S p := geom_sum_modEq_sub_one hA1
  have hpS : p < S := geom_sum_gt_prime hA hp hp2
  have hSgt1 : 1 < S := lt_trans (by omega) hpS
  have hSdvd : S ∣ A ^ p - 1 := ⟨A - 1, hSmul.symm⟩
  have hgcd : Nat.gcd S (A - 1) ∣ p := by
    rw [Nat.ModEq.gcd_eq hSmod]
    exact Nat.gcd_dvd_left p (A - 1)
  by_cases hcase : p ∣ A - 1
  · -- Case `p ∣ A - 1`: find a prime `≠ p` dividing `S`.
    have hpdvdS : p ∣ S := by
      have h := Nat.ModEq.of_dvd hcase hSmod
      exact Nat.modEq_zero_iff_dvd.mp (h.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl p)))
    have hnotsq : ¬ p ^ 2 ∣ S := by
      intro h
      have hmod := geom_sum_modEq_prime_sq hA hp hp2 hcase
      have : p ≡ 0 [MOD p ^ 2] := hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr h)
      have hpp : p ^ 2 ∣ p := Nat.modEq_zero_iff_dvd.mp this
      have hle : p ^ 2 ≤ p := Nat.le_of_dvd (by omega) hpp
      nlinarith [hp.two_le]
    obtain ⟨k, hk⟩ := hpdvdS
    have hk2 : 2 ≤ k := by
      have : p * 1 < p * k := by rw [mul_one, ← hk]; exact hpS
      have := Nat.lt_of_mul_lt_mul_left this
      omega
    obtain ⟨t, htprime, htk⟩ := Nat.exists_prime_and_dvd (n := k) (by omega)
    refine ⟨t, htprime, ?_, ?_⟩
    · have htkS : t ∣ S := dvd_trans htk (by rw [hk]; exact dvd_mul_left k p)
      exact dvd_trans htkS hSdvd
    · intro htdvd
      have htgcd : t ∣ Nat.gcd S (A - 1) :=
        Nat.dvd_gcd (dvd_trans htk (by rw [hk]; exact dvd_mul_left k p)) htdvd
      have htp : t ∣ p := dvd_trans htgcd hgcd
      have ht_eq : t = p := (Nat.dvd_prime_two_le hp htprime.two_le).mp htp
      have hpk : p ∣ k := ht_eq ▸ htk
      refine hnotsq ?_
      rw [hk, pow_two]
      exact mul_dvd_mul_left p hpk
  · -- Case `p ∤ A - 1`: any prime divisor of `S` works.
    obtain ⟨t, htprime, htS⟩ := Nat.exists_prime_and_dvd (n := S) (by omega)
    refine ⟨t, htprime, dvd_trans htS hSdvd, ?_⟩
    intro htdvd
    have htgcd : t ∣ Nat.gcd S (A - 1) := Nat.dvd_gcd htS htdvd
    have htp : t ∣ p := dvd_trans htgcd hgcd
    have ht_eq : t = p := (Nat.dvd_prime_two_le hp htprime.two_le).mp htp
    exact hcase (ht_eq ▸ htdvd)

end Work.PSU3.StageA
