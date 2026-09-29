import Mathlib
import Submission.Work.Params.defs
import Submission.Work.Params.uparfacts
import Submission.Work.Params.nt1
import Submission.Work.Params.basic
import Submission.Work.Params.PrimeNotDvdUparAdd
import Submission.Work.Params.PrimeDvdFfacOfDvdMulSub

/-!
`G₁`-coprimality of §5.1: the numbers `u₀ + F·a` (`1 ≤ a < d`) are pairwise coprime.

`u₀ = upar n = Q·(1 + mF)` satisfies `u₀ ≡ 1 (mod F)`, so `u₀ + F·a ≡ 1 (mod p)` for every prime
`p ∣ F`; in particular no prime divisor of `F` divides `u₀ + F·a`. If a prime `p` divided
`gcd (u₀ + F·a) (u₀ + F·b)` it would divide the difference `F·(b - a)`; but `b - a ≤ D - 1`, so
either way `p ∣ F`, whence `p ∤ u₀ + F·a`, a contradiction.
-/

set_option autoImplicit false

namespace Work.Params

open HvdH

theorem CoprimeG1 (n : ℕ) {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b < D) :
    Nat.Coprime (upar n + Ffac * a) (upar n + Ffac * b) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hp1 : p ∣ upar n + Ffac * a := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
  have hp2 : p ∣ upar n + Ffac * b := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
  -- the difference of the two numbers is exactly `Ffac * (b - a)`
  have hdiff : p ∣ Ffac * (b - a) := by
    have h := Nat.dvd_sub hp2 hp1
    rwa [show upar n + Ffac * b - (upar n + Ffac * a) = Ffac * (b - a) from by
          rw [Nat.add_sub_add_left, ← Nat.mul_sub_left_distrib]] at h
  -- `b - a ≤ D - 1`, so every prime divisor of `Ffac * (b - a)` divides `Ffac`
  have hF : p ∣ Ffac := PrimeDvdFfacOfDvdMulSub ha hab hb hp hdiff
  exact absurd hp1 (PrimeNotDvdUparAdd n a hp hF)

end Work.Params
