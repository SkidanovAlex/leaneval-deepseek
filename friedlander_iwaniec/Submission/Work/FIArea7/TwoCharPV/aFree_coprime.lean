import Mathlib
import Submission.Work.FIArea7.TwoCharPV.Basic

namespace Work.FIArea7.TwoCharPV

/-- For a prime `p` dividing `A`, the exponent of `p` in `aFree A m` is zero (when `m > 0`):
the whole `p`-part of `m` is already absorbed by `gcd m (A ^ m)`, because `A ^ m` contains
`p ^ m` and `p ^ m` is at least the exponent of `p` in `m`. -/
lemma aFree_factorization_eq_zero {A m p : ℕ} (hm : 0 < m) (hA : A ≠ 0) (hp : p.Prime)
    (hpA : p ∣ A) : (aFree A m).factorization p = 0 := by
  have hm0 : m ≠ 0 := hm.ne'
  have hpow : A ^ m ≠ 0 := pow_ne_zero _ hA
  -- `p ^ m ∣ A ^ m`, so `m ≤ v_p (A ^ m)`, which beats `v_p m < m`.
  have hge : m ≤ (A ^ m).factorization p := by
    rw [← hp.pow_dvd_iff_le_factorization hpow]
    exact pow_dvd_pow_of_dvd hpA m
  have hle : m.factorization p ≤ (A ^ m).factorization p :=
    (Nat.factorization_lt p hm0).le.trans hge
  calc (aFree A m).factorization p
      = (m / m.gcd (A ^ m)).factorization p := rfl
    _ = (m.factorization - (m.gcd (A ^ m)).factorization) p := by
          rw [Nat.factorization_div (Nat.gcd_dvd_left m (A ^ m))]
    _ = (m.factorization - (m.factorization ⊓ (A ^ m).factorization)) p := by
          rw [Nat.factorization_gcd hm0 hpow]
    _ = 0 := by
          simp only [Finsupp.tsub_apply, Finsupp.inf_apply]
          rw [min_eq_left hle, tsub_self]

/-- `aFree A m = m / m.gcd (A ^ m)` (declared in `Submission/Work/FIArea7/TwoCharPV/Basic.lean`)
is the part of `m` supported on the primes **not** dividing `A`; it is therefore coprime to `A`
when `m > 0`.  Suggested proof: `Nat.factorization_div` with `aCore_dvd`, `Nat.factorization_gcd`
and `Nat.factorization_pow` show `v_p (aFree A m) = 0` for every prime `p ∣ A` (since
`v_p (A^m) = m·v_p A ≥ v_p m` there); conclude with `Nat.Prime.not_coprime_iff_dvd`. -/
theorem aFree_coprime (A m : ℕ) (hm : 0 < m) : Nat.Coprime (aFree A m) A := by
  rcases eq_or_ne A 0 with rfl | hA
  · -- `A = 0`: then `aFree 0 m = m / gcd m 0 = m / m = 1`.
    rw [show aFree 0 m = 1 by simp [aFree, hm.ne', Nat.div_self hm]]
    exact Nat.coprime_one_left 0
  · -- A prime dividing both `aFree A m` and `A` would have a non-zero exponent in `aFree A m`,
    -- contradicting `aFree_factorization_eq_zero`.
    by_contra hcon
    obtain ⟨p, hp, hpaFree, hpA⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
    have hfac : (aFree A m).factorization p = 0 := aFree_factorization_eq_zero hm hA hp hpA
    rw [hp.dvd_iff_one_le_factorization (aFree_pos hm).ne', hfac] at hpaFree
    omega

end Work.FIArea7.TwoCharPV
