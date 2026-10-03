/-
# `Submission.Work.FIArea6V.CleanVDefs` — vocabulary of the clean §16 V-lane reduction

This module fixes the objects of the *clean* (§16 Lemma 16.2) reduction from the §16 heart
`Work.FIArea6.S16TsumHeart` to `Work.FIArea6V.S16CleanCoreTwoA`:

* `SuppClean` — the clean support `IsPrimary ∧ NoSmallPrimes` (5.3)+(5.8) (no (5.9) divisor
  bound, no axis clause);
* `boxTermSumClean` — the clean §16 box sum
  `Σ_{z ∈ boxN} [SuppClean z]·q(arg z − φ)·p(|z|²)·μ(|z|²)·γ(|z|²;C)·χ(z)(z/|z|)^j`, i.e. the
  sum bounded by `S16CleanCoreTwoA` (with `s16Term` of `FIArea6Road/TauHeartDefs.lean`);
* `winTauSq` — the norm-window mass `Σ_{⌊N⌋+1 ≤ n ≤ ⌊(1+θ)N⌋} τ(n)²`, the trivial (no-cancellation)
  size of the Möbius-twisted Hecke sum `Tsum` (`Work.FIArea6Road.norm_Tsum_le_suppWindow`).

The reduction itself (the clean analogue of `Work.FIArea6Road.TauCoreOfTauHeart`) is
`Submission/Work/FIArea6V/S16CleanCoreTwoA_of_heart.lean`: the angular weight `q` is
Fourier-expanded (`fcoef`, absolutely convergent by `TauHeartFserEqQ`), each mode is regrouped into
`Tsum`, and the sum over the retained frequencies `|ℓ| ≤ L = freqL Pa` is bounded by the heart. -/
import Mathlib
import Submission.Work.FIArea6V.Defs
import Submission.Work.FIArea6Road.TauCoreOfTauHeart
import Submission.Work.FIArea6.S16CleanSum_eq_Tsum
import Submission.Work.FIArea5.S16Hecke.ThetaDefs

set_option autoImplicit false

namespace Work.FIArea6V

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The clean §16 support** (5.3)+(5.8): primary Gaussian integers free of primes `≤ Pz`. -/
def SuppClean (Pa : Work.FITop.Params) (z : GaussianInt) : Prop :=
  Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z

/-- **The clean §16 box sum**: the sum bounded by `Work.FIArea6V.S16CleanCoreTwoA`, written with
the summand `Work.FIArea6Road.s16Term` of the pinned §16 bookkeeping lane. -/
def boxTermSumClean (Pa : Work.FITop.Params) (φ : ℝ) (j : ℤ) (chi : GaussianInt → ℂ)
    (q p : ℝ → ℝ) : ℂ :=
  ∑ z ∈ Work.FITop.boxN Pa,
    (if SuppClean Pa z then Work.FIArea6Road.s16Term Pa φ j chi q p z else 0)

/-- Unfolding of `boxTermSumClean` into the literal summand of `S16CleanCoreTwoA`. -/
theorem boxTermSumClean_eq (Pa : Work.FITop.Params) (φ : ℝ) (j : ℤ) (chi : GaussianInt → ℂ)
    (q p : ℝ → ℝ) :
    boxTermSumClean Pa φ j chi q p
      = ∑ z ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z then
            ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j
          else 0) := by
  unfold boxTermSumClean
  refine Finset.sum_congr rfl (fun z _ => ?_)
  by_cases h : Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z
  · rw [if_pos h, if_pos (show SuppClean Pa z from h)]
    rfl
  · rw [if_neg h, if_neg (fun hh : SuppClean Pa z => h hh)]

/-- **The norm-window mass** `Σ_{⌊N⌋+1 ≤ n ≤ ⌊(1+θ)N⌋} τ(n)²`.  By
`Work.FIArea6Road.norm_Tsum_le_suppWindow`, `‖Tsum Pa χ m p‖ ≤ 4·winTauSq Pa` for every frequency
`m` and every mollifier `p` of the class (4.12)/(4.14). -/
def winTauSq (Pa : Work.FITop.Params) : ℝ :=
  ∑ n ∈ Finset.Icc (⌊Pa.N⌋₊ + 1) ⌊(1 + Pa.θ) * Pa.N⌋₊, ((n.divisors.card : ℝ)) ^ 2

/-! ## Glue lemmas for the clean support -/

/-- The clean summand with the `(j+ℓ)`-th angle mode removed: for `z` in the clean support,
`e^{iℓ·arg z}·(p·μ·γ·χ·(z/|z|)^j)(z) = (p·μ·γ·ψ_{j+ℓ})(z)`. -/
theorem SuppClean_exp_mul_s16Core (Pa : Work.FITop.Params) (j ℓ : ℤ) (chi : GaussianInt → ℂ)
    (p : ℝ → ℝ) {z : GaussianInt} (hz : SuppClean Pa z) :
    Complex.exp ((ℓ : ℂ) * Complex.I * ((Complex.arg z.toComplex : ℝ) : ℂ))
        * Work.FIArea6Road.s16Core Pa j chi p z
      = (p (Work.FIPlan.gnorm z) : ℂ) * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
          * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
          * Work.FIArea5.S16Hecke.psi chi (j + ℓ) z :=
  Work.FIArea6Road.s16Core_mul_exp_eq Pa j ℓ chi p hz.1

/-- The clean summand is `Work.FIArea6.S16CleanSummand` (the summand of
`Work.FIArea6.TauPieces.CleanSumEqTsum`), written with `SuppClean`. -/
theorem SuppClean_summand_eq (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ)
    (z : GaussianInt) :
    (if SuppClean Pa z then
        (p (Work.FIPlan.gnorm z) : ℂ) * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
          * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
          * Work.FIArea5.S16Hecke.psi chi m z
      else 0)
      = Work.FIArea6.S16CleanSummand Pa chi m p z := by
  have hcond : (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z) ↔ SuppClean Pa z :=
    Iff.rfl
  by_cases h : SuppClean Pa z
  · rw [if_pos h]
    unfold Work.FIArea6.S16CleanSummand
    rw [if_pos (hcond.mpr h)]
  · rw [if_neg h]
    unfold Work.FIArea6.S16CleanSummand
    rw [if_neg (fun hh => h (hcond.mp hh))]

end

end Work.FIArea6V
