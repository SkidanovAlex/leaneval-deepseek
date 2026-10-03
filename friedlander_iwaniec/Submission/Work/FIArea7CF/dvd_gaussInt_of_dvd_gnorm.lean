/-
# `Submission.Work.FIArea7CF.dvd_gaussInt_of_dvd_gnorm` — clash-free copy of `Submission.Work.FIArea7.dvd_gaussInt_of_dvd_gnorm`

Imports redirected to the `FIArea7CF` copies; renamed: mem_gBox_iff→r2c_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7CF.R2countDefs

set_option linter.style.haveILetI false

namespace Work.FIArea7

/-- For a natural prime `p ≡ 3 (mod 4)`, if `p` divides the Gaussian norm `gnorm z = |z|²`
of a Gaussian integer `z`, then `p` divides `z` as a Gaussian integer.

Indeed `p ≡ 3 (mod 4)` stays prime in `ℤ[i]`, and `z * star z = ((gnorm z : ℕ) : GaussianInt)`;
since `p` is a prime element of `ℤ[i]` and divides `z * star z`, it divides `z` or `star z`,
and `p ∣ star z` implies `p ∣ z`. -/
lemma dvd_gaussInt_of_dvd_gnorm {p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) {z : GaussianInt}
    (h : p ∣ Work.FIPlan.gnorm z) : ((p : ℕ) : GaussianInt) ∣ z := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hprime : Prime (p : GaussianInt) :=
    GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p h3
  obtain ⟨m, hm⟩ := h
  have hzn : z * star z = ((Work.FIPlan.gnorm z : ℕ) : GaussianInt) :=
    mul_star_eq_gnorm z
  have hdvd : (p : GaussianInt) ∣ z * star z := by
    rw [hzn, hm, Nat.cast_mul]
    exact dvd_mul_right _ _
  rcases hprime.dvd_mul.mp hdvd with hd | hd
  · exact hd
  · obtain ⟨c, hc⟩ := hd
    refine ⟨star c, ?_⟩
    rw [← star_star z, hc, star_mul, star_natCast]
    exact mul_comm _ _

end Work.FIArea7
