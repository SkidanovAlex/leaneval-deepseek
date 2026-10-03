import Mathlib
import Submission.Work.FIArea7.TwoCharPV.Basic

namespace Work.FIArea7.TwoCharPV

open Work.FIArea7

/-- If `m` has a prime `p ∤ A` occurring to an odd power, then the `A`-free part
`aFree A m = m / m.gcd (A ^ m)` of `m` (see `Submission/Work/FIArea7/TwoCharPV/Basic.lean`) is
not a perfect square (for `m > 0`).  Such a `p` does not divide `aCore A m = m.gcd (A^m)` (else
`p ∣ A^m`, so `p ∣ A`), hence `v_p (aFree A m) = v_p m` is odd (`Nat.factorization_mul` with
`aCore_mul_aFree`, `Nat.factorization_eq_zero_of_not_dvd`); if `aFree A m = k^2` then that
valuation would be `2·v_p k`, an even number (`Nat.factorization_pow`). -/
theorem aFree_nonsquare (A m : ℕ) (hm : 0 < m)
    (h : ∃ p : ℕ, p.Prime ∧ ¬ p ∣ A ∧ Odd (m.factorization p)) :
    ∀ k : ℕ, aFree A m ≠ k ^ 2 := by
  obtain ⟨p, hp, hpA, hodd⟩ := h
  intro k hk
  -- `p ∤ aCore A m`, since `aCore A m ∣ A ^ m` and `p ∤ A` forces `p ∤ A ^ m`.
  have hpAcore : ¬ p ∣ aCore A m := fun hdvd => hpA (aCore_prime_dvd hp hdvd)
  have hcore : aCore A m ≠ 0 := (aCore_pos (A := A) hm).ne'
  have hfree : aFree A m ≠ 0 := (aFree_pos (A := A) hm).ne'
  -- `v_p m = v_p (aCore A m) + v_p (aFree A m)`, and `v_p (aCore A m) = 0`.
  have hfac : m.factorization p
      = (aCore A m).factorization p + (aFree A m).factorization p := by
    have h1 := Nat.factorization_mul (a := aCore A m) (b := aFree A m) hcore hfree
    have h2 := congrArg (fun f : ℕ →₀ ℕ => f p) h1
    rw [Finsupp.add_apply, aCore_mul_aFree A m] at h2
    exact h2
  rw [Nat.factorization_eq_zero_of_not_dvd hpAcore, zero_add] at hfac
  -- If `aFree A m = k ^ 2` then `v_p m = 2 · v_p k` would be even, contradicting `Odd`.
  rw [hk, Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul] at hfac
  obtain ⟨t, ht⟩ := hodd
  omega

end Work.FIArea7.TwoCharPV
