import Mathlib
import Submission.Work.FITop4.Areas6
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea6Hecke.S16CoreDefs
import Submission.Work.FIArea6Hecke.area5_6_of_S16Core
import Submission.Work.FIArea6.S16MellinInversion
import Submission.Work.FIArea6.TauPieces.TsumHeartDefs
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Work.FIArea6.S16TsumHeart_of_invBound
import Submission.Work.FIArea6.S16TsumHeartDefs
import Submission.Work.FIArea6Hecke.S16CleanDefs
import Submission.Work.FIArea5.S16.fourier_truncation
import Submission.Work.FIArea6.S16CleanSum_eq_Tsum
import Submission.Work.FIArea6.TauPieces.CleanSumEqTsum
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea6Road.TauHeartDefs
import Submission.Work.FIArea6.fourier_coeff_decay
import Submission.Work.FIArea4.S15prim_defs
import Submission.Work.FIArea6Road.TauHeartArith
import Submission.Work.FIPlan.Interface
import Submission.Work.FITop4.Defs6
import Submission.Work.FIArea6.ClassDetectDefs
import Submission.Work.FIArea6.char8Of_isCharMod4dStrict
import Submission.Work.FIArea6.classDetect8Gauss
import Submission.Work.FIArea6.s16RadialSupportMass

set_option autoImplicit false

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The summand identity of the `β`-indexed and radial forms.**  On the support of a coefficient
of (4.13)+(5.13)+(5.7) the polar-box indicator is redundant: the angular support of `q` (the
sector (5.12), together with `q 0 = 0` when the angle vanishes) and the radial support of `p`
(the segment (4.12)) already give the sector and the norm range of `InPolarBox`.  Hence
`β_z χ(z)(z/|z|)^k` is exactly the radial summand of `S16RadialCoreTwo`. -/
theorem betaSummand_eq_radial (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt)
    (k : ℤ) (chi : GaussianInt → ℂ) (q p : ℝ → ℝ) {β : GaussianInt → ℂ}
    (hqC : ContDiff ℝ 2 q)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * Pa.θ)
    (hpsupp : ∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hβdef : ∀ z : GaussianInt, β z =
      (if Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
          (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧
          Work.FITop4.SameClass8 z z0 ∧ Work.FITop4.IsAxisFree Pa z
       then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
       else 0))
    (z : GaussianInt) :
    β z * chi z * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ k
      = (if Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z
              ∧ (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
              ∧ Work.FITop4.SameClass8 z z0 ∧ Work.FITop4.IsAxisFree Pa z then
            ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ k
          else 0) := by
  rw [hβdef z]
  by_cases hA : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧
      Work.FITop4.SameClass8 z z0 ∧ Work.FITop4.IsAxisFree Pa z
  · rw [if_pos hA]
    have hB : Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
        (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧
        Work.FITop4.SameClass8 z z0 ∧ Work.FITop4.IsAxisFree Pa z := ⟨hA.1.1, hA.2⟩
    rw [if_pos hB]
  · rw [if_neg hA]
    by_cases hB : Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
        (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧
        Work.FITop4.SameClass8 z z0 ∧ Work.FITop4.IsAxisFree Pa z
    · rw [if_pos hB]
      have hz : q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) = 0 := by
        by_contra hne
        have hqne : q (Complex.arg z.toComplex - φ) ≠ 0 := fun h => hne (by rw [h, zero_mul])
        have hpne : p (Work.FIPlan.gnorm z) ≠ 0 := fun h => hne (by rw [h, mul_zero])
        have hs := hqsupp _ hqne
        have hn := hpsupp _ hpne
        have hbox : Work.FITop4.InPolarBox Pa φ z := by
          refine ⟨hB.1, hn.1, hn.2, ?_, ?_⟩
          · have hne0 : Complex.arg z.toComplex - φ ≠ 0 := fun h =>
              hqne (by rw [h]; exact Work.FIArea6Hecke.mollQ_zero hqC hqsupp)
            have hpos : 0 < Complex.arg z.toComplex - φ := lt_of_le_of_ne hs.1 hne0.symm
            linarith
          · linarith [hs.2]
        exact hA ⟨hbox, hB.2⟩
      simp [hz]
    · rw [if_neg hB]; ring

end

end Work.FIArea6
