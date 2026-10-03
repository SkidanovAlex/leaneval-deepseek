import Mathlib.Tactic.IntervalCases
import Submission.Commons.NumberTheory.GaussianInt.irreducible_norm_prime_pow

namespace Commons.NumberTheory.GaussianInt

open Zsqrtd

theorem irreducible_norm_eq_prime_or_sq {z : GaussianInt} (hz : Irreducible z) :
    ∃ p : ℕ, p.Prime ∧ (z.norm.natAbs = p ∨ z.norm.natAbs = p ^ 2) := by
  obtain ⟨p, k, hpprime, hk1, hnorm⟩ := irreducible_norm_prime_pow hz
  have hz0 : z ≠ 0 := hz.ne_zero
  have hnorm_pos : 0 < z.norm := (GaussianInt.norm_pos).mpr hz0
  have hnat_int : ((z.norm.natAbs : ℕ) : ℤ) = z.norm :=
    Int.natAbs_of_nonneg (le_of_lt hnorm_pos)
  -- z divides its natural norm, viewed as a Gaussian integer
  have hdvd_natnorm : z ∣ ((z.norm.natAbs : ℕ) : GaussianInt) := by
    refine ⟨star z, ?_⟩
    have h1 : ((z.norm : ℤ) : GaussianInt) = z * star z := Zsqrtd.norm_eq_mul_conj z
    have h2 : ((z.norm.natAbs : ℕ) : GaussianInt) = ((z.norm : ℤ) : GaussianInt) := by
      have h := congrArg (fun t : ℤ => (t : GaussianInt)) hnat_int
      simpa using h
    rw [h2, h1]
  -- hence z ∣ (p : ℤ[i]) ^ k
  have hdvd_pk : z ∣ (p : GaussianInt) ^ k := by
    have h := hdvd_natnorm
    rw [hnorm] at h
    simpa using h
  have hzprime : Prime z := (UniqueFactorizationMonoid.irreducible_iff_prime).mp hz
  have hdvd_p : z ∣ (p : GaussianInt) := hzprime.dvd_of_dvd_pow hdvd_pk
  obtain ⟨w, hw⟩ := hdvd_p
  -- compare norms: p * p = z.norm * w.norm, and z.norm = p ^ k
  have hz_norm : z.norm = (p : ℤ) ^ k := by
    rw [← hnat_int, hnorm]
    push_cast
    ring
  have hnorm_eq : (p : ℤ) * (p : ℤ) = z.norm * w.norm := by
    have h := congrArg Zsqrtd.norm hw
    rw [Zsqrtd.norm_natCast, Zsqrtd.norm_mul] at h
    exact h
  have hmul : p ^ 2 = p ^ k * w.norm.natAbs := by
    have h := congrArg Int.natAbs hnorm_eq
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at h
    rw [hnorm] at h
    simpa [pow_two] using h
  have hdvd : p ^ k ∣ p ^ 2 := ⟨w.norm.natAbs, hmul⟩
  have hk2 : k ≤ 2 := (Nat.pow_dvd_pow_iff_le_right hpprime.one_lt).mp hdvd
  interval_cases k
  · exact ⟨p, hpprime, Or.inl (by simpa using hnorm)⟩
  · exact ⟨p, hpprime, Or.inr (by simpa using hnorm)⟩

end Commons.NumberTheory.GaussianInt