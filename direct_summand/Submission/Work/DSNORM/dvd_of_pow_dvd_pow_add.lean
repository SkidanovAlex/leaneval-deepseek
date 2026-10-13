import Mathlib

/-!
# Asymptotic divisibility of powers in a unique factorization monoid

If `f ^ m ∣ g ^ (m + K)` for all `m` (with `f ≠ 0 ≠ g`), then `f ∣ g`.

Needed by `Submission/Work/DSNORM/Integral.lean` (the step from the integrality relation for `a / b`
to the divisibility `inForm b ∣ inForm a` of initial forms).
-/

namespace Work.DSNORM

/-- Elementary arithmetic: if `m * n ≤ (m + K) * n'` for all `m`, then `n ≤ n'`. -/
theorem le_of_forall_mul_le_mul_add {n n' K : ℕ}
    (h : ∀ m : ℕ, m * n ≤ (m + K) * n') : n ≤ n' := by
  by_contra hcon
  push Not at hcon
  have h1 := h (K * n' + 1)
  have hsub : 1 ≤ n - n' := by omega
  have hmul : (K * n' + 1) * 1 ≤ (K * n' + 1) * (n - n') := Nat.mul_le_mul_left _ hsub
  rw [mul_one] at hmul
  have h2 : (K * n' + 1) * (n - n') ≤ K * n' := by
    have h3 : (K * n' + 1) * n = (K * n' + 1) * ((n - n') + n') := by
      rw [Nat.sub_add_cancel (le_of_lt hcon)]
    have h4 : (K * n' + 1) * ((n - n') + n')
        = (K * n' + 1) * (n - n') + (K * n' + 1) * n' := by ring
    have h5 : (K * n' + 1 + K) * n' = (K * n' + 1) * n' + K * n' := by ring
    nlinarith [h1, h3, h4, h5]
  omega

/-- In a unique factorization monoid, asymptotic divisibility of powers implies divisibility. -/
theorem dvd_of_pow_dvd_pow_add {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
    {f g : R} (hf : f ≠ 0) (hg : g ≠ 0) (K : ℕ)
    (h : ∀ m : ℕ, f ^ m ∣ g ^ (m + K)) : f ∣ g := by
  classical
  rw [UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hf]
  intro p hp
  have hf' : FiniteMultiplicity p f := FiniteMultiplicity.of_prime_left hp hf
  have hg' : FiniteMultiplicity p g := FiniteMultiplicity.of_prime_left hp hg
  rw [hf'.emultiplicity_eq_multiplicity, hg'.emultiplicity_eq_multiplicity,
    ENat.natCast_le_natCast]
  by_contra hcon
  push Not at hcon
  have hle : ∀ m : ℕ, m * multiplicity p f ≤ (m + K) * multiplicity p g := by
    intro m
    have hdvd := (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le (pow_ne_zero m hf)).mp
      (h m) p hp
    rw [emultiplicity_pow hp, emultiplicity_pow hp,
      hf'.emultiplicity_eq_multiplicity, hg'.emultiplicity_eq_multiplicity] at hdvd
    exact_mod_cast hdvd
  exact absurd (le_of_forall_mul_le_mul_add hle) (not_le.mpr hcon)

end Work.DSNORM
