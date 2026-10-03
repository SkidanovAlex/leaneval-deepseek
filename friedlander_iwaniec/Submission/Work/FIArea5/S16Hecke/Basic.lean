/-
# `Submission.Work.FIArea5.S16Hecke.Basic`

Elementary consequences of the definitions of `S16Hecke.Defs` in terms of the already available
modules: multiplicativity of `λ` on coprime arguments (`heckeEigenvalue_mul`), and the vanishing
of `λ` at `0` and at even `n`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.heckeEigenvalue_mul

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- **(16.30), multiplicativity**: `λ(mn) = λ(m)λ(n)` for coprime `m, n > 0`, from multiplicativity
of `χ`. This is the Hecke eigenvalue multiplicativity; the local recursion (16.30) refines it at
prime powers. -/
theorem heckeLam_mul (chi : GaussianInt → ℂ) (k : ℤ)
    (hchi : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hcop : Nat.Coprime m n) :
    heckeLam chi k (m * n) = heckeLam chi k m * heckeLam chi k n := by
  classical
  simp only [heckeLam, psi]
  exact heckeEigenvalue_mul chi k m n hchi hm hn hcop

/-- `λ(0) = 0`: no primary Gaussian integer has norm zero. -/
theorem heckeLam_zero (chi : GaussianInt → ℂ) (k : ℤ) : heckeLam chi k 0 = 0 := by
  classical
  unfold heckeLam
  refine Finset.sum_eq_zero ?_
  intro z hz
  rw [Finset.mem_filter] at hz
  obtain ⟨-, hprim, hgn⟩ := hz
  have hz0 : z = 0 := by
    have h1 : z.re * z.re - -1 * z.im * z.im = 0 := by
      have := Int.natAbs_eq_zero.mp hgn
      rwa [Zsqrtd.norm_def] at this
    have hre : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    have him : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    exact Zsqrtd.ext hre him
  rw [hz0] at hprim
  exact absurd hprim.1 (by simp)

end

end Work.FIArea5.S16Hecke
