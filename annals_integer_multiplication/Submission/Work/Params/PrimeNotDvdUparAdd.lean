import Mathlib
import Submission.Work.Params.defs
import Submission.Work.Params.qall
import Submission.Work.Params.basic
import Submission.Work.Params.uparfacts
import Submission.Work.Params.nt1

namespace Work.Params

/-- `u₀ ≡ 1 (mod F)`, so `u₀ + F·a ≡ 1 (mod p)` for every prime `p ∣ F`; a number `≡ 1`
modulo `p ≥ 2` is never divisible by `p`. -/
theorem PrimeNotDvdUparAdd (n a : ℕ) {p : ℕ} (hp : Nat.Prime p) (hpF : p ∣ Ffac) :
    ¬ p ∣ (upar n + Ffac * a) := by
  intro h
  have hp2 : 2 ≤ p := hp.two_le
  have hup : upar n ≡ 1 [MOD Ffac] := (uparfacts n).2.2.2.1
  have h1 : upar n ≡ 1 [MOD p] := Nat.ModEq.of_dvd hpF hup
  have h2 : Ffac * a ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hpF a)
  have h3 : upar n + Ffac * a ≡ 1 + 0 [MOD p] := Nat.ModEq.add h1 h2
  rw [add_zero] at h3
  have h4 : upar n + Ffac * a ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h
  have h5 : (1 : ℕ) ≡ 0 [MOD p] := h3.symm.trans h4
  rw [Nat.modEq_zero_iff_dvd] at h5
  have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) h5
  omega

end Work.Params
