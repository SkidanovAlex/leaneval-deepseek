import Mathlib
import Submission.Work.FIPlan.Interface

namespace Work.FIArea5.S16Hecke

/-- `star π` is irreducible when `π` is: conjugation is an involutive ring automorphism of `ℤ[i]`,
so it permutes units and reverses the factorisation relation. -/
theorem irreducible_star {π : GaussianInt} (hirr : Irreducible π) :
    Irreducible (star π) := by
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · rw [isUnit_star]; exact (irreducible_iff.mp hirr).1
  · intro x y hxy
    have h' : π = star y * star x := by
      have hstar := congrArg star hxy
      rwa [star_mul, star_star] at hstar
    rcases (irreducible_iff.mp hirr).2 h' with hh | hh
    · exact Or.inr (isUnit_star.mp hh)
    · exact Or.inl (isUnit_star.mp hh)

/-- **Uniqueness of the exponent class `π^a (star π)^(ν-a)`.**

If `π` is an irreducible Gaussian integer that is not associated to its conjugate `star π`
(so `π` and `star π` are two distinct prime classes of `ℤ[i]`), then the exponent `a` in
`π^a (star π)^(ν-a)` is determined by the element up to the range `0 ≤ a ≤ ν`. -/
theorem powClassUnique (π : GaussianInt) (ν a b : ℕ)
    (hirr : Irreducible π) (hnassoc : ¬ Associated π (star π))
    (ha : a ≤ ν) (hb : b ≤ ν)
    (h : π ^ a * (star π) ^ (ν - a) = π ^ b * (star π) ^ (ν - b)) : a = b := by
  have hqirr : Irreducible (star π) := irreducible_star hirr
  have hpprime : Prime π := (UniqueFactorizationMonoid.irreducible_iff_prime).mp hirr
  -- The core: for `m ≤ n`, the equality forces `m = n`.
  have key : ∀ m n : ℕ, m ≤ n → n ≤ ν →
      π ^ m * (star π) ^ (ν - m) = π ^ n * (star π) ^ (ν - n) → m = n := by
    intro m n hmn hnν hm
    by_contra hne
    have hlt : m < n := lt_of_le_of_ne hmn hne
    have hp0 : π ≠ 0 := hirr.ne_zero
    have hq0 : star π ≠ 0 := star_ne_zero.mpr hp0
    -- cancel the lower power of `π`
    have hn' : π ^ n = π ^ m * π ^ (n - m) := by
      rw [← pow_add, Nat.add_sub_cancel' hmn]
    have h1 : π ^ m * (star π) ^ (ν - m)
        = π ^ m * (π ^ (n - m) * (star π) ^ (ν - n)) := by
      rw [hm, hn', mul_assoc]
    have h2 : (star π) ^ (ν - m) = π ^ (n - m) * (star π) ^ (ν - n) :=
      mul_left_cancel₀ (pow_ne_zero m hp0) h1
    -- rewrite the remaining power of `star π` and cancel it
    have hνm : ν - m = (ν - n) + (n - m) := by omega
    have h3 : (star π) ^ (ν - m) = (star π) ^ (ν - n) * (star π) ^ (n - m) := by
      rw [hνm, pow_add]
    have hEq : (star π) ^ (ν - n) * (star π) ^ (n - m)
        = π ^ (n - m) * (star π) ^ (ν - n) := h3.symm.trans h2
    have h4 : (star π) ^ (n - m) = π ^ (n - m) := by
      have h4a : (star π) ^ (n - m) * (star π) ^ (ν - n)
          = π ^ (n - m) * (star π) ^ (ν - n) := by
        rw [mul_comm ((star π) ^ (n - m)) ((star π) ^ (ν - n))]
        exact hEq
      exact mul_right_cancel₀ (pow_ne_zero (ν - n) hq0) h4a
    -- hence `π ∣ star π`, contradicting non-associativity
    have hdvdq : π ∣ (star π) ^ (n - m) := by
      rw [h4]
      exact dvd_pow_self π (by omega)
    exact hnassoc (hpprime.irreducible.associated_of_dvd hqirr (hpprime.dvd_of_dvd_pow hdvdq))
  rcases le_total a b with hab | hba
  · exact key a b hab hb h
  · exact (key b a hba ha h.symm).symm

end Work.FIArea5.S16Hecke
