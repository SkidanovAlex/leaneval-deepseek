/-
# `Submission.Work.FIArea7CF.exists_gaussPrime_gnorm_eq` — clash-free copy of `Submission.Work.FIArea7.exists_gaussPrime_gnorm_eq`

Imports redirected to the `FIArea7CF` copies; renamed: mem_gBox_iff→r2c_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7CF.R2countDefs

/-!
# Gaussian primes of prescribed (rational) prime norm

Fermat's theorem on the sum of two squares (`Nat.Prime.sq_add_sq`) says that every prime
`p ≢ 3 (mod 4)` is a sum of two squares `p = a ^ 2 + b ^ 2`.  Taking `π = a + b i`, the
Gaussian integer `π` then satisfies `gnorm π = |π| ^ 2 = a ^ 2 + b ^ 2 = p`; and since
`Z[i]` is a unique factorization domain, an element whose norm is a rational prime is
irreducible, hence prime.

These facts are the input, used throughout §5 of Friedlander–Iwaniec, that every prime
`p ≡ 1 (mod 4)` has a Gaussian prime above it of index `p`; concretely they provide the
nonempty family of prime ideals of norm `p` that the area-7 counting of Gaussian integers
of prescribed norm runs over.
-/

set_option autoImplicit false

namespace Work.FIArea7

open GaussianInt

/-- `gnorm` of `a + b i` for natural `a`, `b` is `a ^ 2 + b ^ 2`. -/
lemma gnorm_pair_natCast (a b : ℕ) :
    Work.FIPlan.gnorm ((⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt)) = a ^ 2 + b ^ 2 := by
  rw [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq]
  simp only [Int.natAbs_natCast]
  ring

/-- A Gaussian integer whose norm `gnorm` is a rational prime is a **prime** of `ℤ[i]`.

Indeed `ℤ[i]` is a Euclidean domain, hence a unique factorization domain, so irreducible
elements are prime; and if `z.norm = p` is a rational prime then `z` is irreducible: for
`z = x * y` multiplicativity of the norm gives `gnorm x * gnorm y = p`, so one factor has
`gnorm = 1`, i.e. is a unit. -/
lemma prime_of_gnorm_prime {z : GaussianInt} {p : ℕ} (hp : p.Prime)
    (h : Work.FIPlan.gnorm z = p) : Prime z := by
  rw [← irreducible_iff_prime]
  have hunit : ¬ IsUnit z := by
    intro hu
    have h1 : Work.FIPlan.gnorm z = 1 := Zsqrtd.norm_eq_one_iff.mpr hu
    rw [h] at h1
    exact hp.ne_one h1
  refine ⟨hunit, ?_⟩
  intro x y hxy
  have hmul : Work.FIPlan.gnorm x * Work.FIPlan.gnorm y = p := by
    rw [← h, ← gnorm_mul, hxy]
  rcases hp.eq_one_or_self_of_dvd (Work.FIPlan.gnorm x) ⟨_, hmul.symm⟩ with h1 | h1
  · left
    exact Zsqrtd.norm_eq_one_iff.mp h1
  · right
    rw [h1] at hmul
    have hy : Work.FIPlan.gnorm y = 1 :=
      Nat.mul_left_cancel hp.pos (by rw [mul_one]; exact hmul)
    exact Zsqrtd.norm_eq_one_iff.mp hy

/-- **A prime `p ≡ 1 (mod 4)` is the norm of a Gaussian prime.**  This is the Gaussian-prime
form of Fermat's two-squares theorem: `p = a ^ 2 + b ^ 2` and `π = a + b i` has `gnorm π = p`,
while multiplicativity of the norm forces `π` to be prime in `ℤ[i]`. -/
lemma exists_gaussPrime_gnorm_eq (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) :
    ∃ π : GaussianInt, Prime π ∧ Work.FIPlan.gnorm π = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by rw [hp4]; norm_num)
  refine ⟨⟨(a : ℤ), (b : ℤ)⟩, ?_, ?_⟩
  · exact prime_of_gnorm_prime hp (by rw [gnorm_pair_natCast, hab])
  · rw [gnorm_pair_natCast, hab]

end Work.FIArea7
