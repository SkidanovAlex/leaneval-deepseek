import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Work.FIArea5.S16Hecke

/-- `|z·w|² = |z|²·|w|²` for the Gaussian norm: the norm is multiplicative. -/
lemma gnorm_mul'' (z w : GaussianInt) : Work.FIPlan.gnorm (z * w) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- `|1+i|² = 2`. -/
lemma gnorm_oneAddI' : Work.FIPlan.gnorm oneAddI = 2 := by decide

/-- **Even (i.e. `1+i`-) substitution in the Hecke theta lattice sum.**  Summing
`ψ(w)·|w|^{-s}` over the sublattice `(1+i)ℤ[i]` — written as `w ↦ (1+i)·w` — factors out the
values of `ψ` and of the norm at `1+i`: since `ψ` is multiplicative and `|1+i|² = 2`,

  `Σ_w ψ((1+i)w)·|(1+i)w|^{-s} = ψ(1+i)·2^{-s}·Σ_w ψ(w)·|w|^{-s}`.

This is the `ψ`-level bookkeeping behind the Hecke functional equation: it relates the theta
series of the weight `χ` to that of the weight `z ↦ χ(1+i)ψ(z)`, an averaging over the index-2
sublattice `(1+i)`. -/
theorem evenSubstLattice (chi : GaussianInt → ℂ) (m : ℤ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hbd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    ∀ s : ℂ, 1 < s.re →
      tsum (fun w : GaussianInt =>
          Work.FIArea5.S16Hecke.psi chi m (Work.FIArea5.S16Hecke.oneAddI * w) *
            (((Work.FIPlan.gnorm (Work.FIArea5.S16Hecke.oneAddI * w) : ℕ) : ℂ) ^ (-s)))
        = Work.FIArea5.S16Hecke.psi chi m Work.FIArea5.S16Hecke.oneAddI *
            ((2 : ℂ) ^ (-s)) *
            tsum (fun w : GaussianInt =>
              Work.FIArea5.S16Hecke.psi chi m w * (((Work.FIPlan.gnorm w : ℕ) : ℂ) ^ (-s))) := by
  intro s hs
  have hgn (w : GaussianInt) :
      Work.FIPlan.gnorm (Work.FIArea5.S16Hecke.oneAddI * w) = 2 * Work.FIPlan.gnorm w := by
    rw [gnorm_mul'', gnorm_oneAddI']
  have hterm (w : GaussianInt) :
      Work.FIArea5.S16Hecke.psi chi m (Work.FIArea5.S16Hecke.oneAddI * w) *
          (((Work.FIPlan.gnorm (Work.FIArea5.S16Hecke.oneAddI * w) : ℕ) : ℂ) ^ (-s))
        = (Work.FIArea5.S16Hecke.psi chi m Work.FIArea5.S16Hecke.oneAddI * (2 : ℂ) ^ (-s)) *
            (Work.FIArea5.S16Hecke.psi chi m w *
              (((Work.FIPlan.gnorm w : ℕ) : ℂ) ^ (-s))) := by
    rw [Work.FIArea5.S16Hecke.psi_mul chi m hmul, hgn w, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
    ring_nf
  rw [funext hterm, tsum_mul_left]

end Work.FIArea6Hecke.R
