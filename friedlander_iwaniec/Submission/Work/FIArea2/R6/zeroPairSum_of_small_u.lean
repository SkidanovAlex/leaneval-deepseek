/-
# `Submission.Work.FIArea2.R6.zeroPairSum_of_small_u`

The pair sum of *FI* (10.6)/(10.7) at the sector scale is **identically zero** once the smoothing
parameter is small, `u := θ√N < 1/10`.  This is the elementary regime that the §10 chain discards
before the hard work: no estimate is needed, the sum has no non-zero term.

The reason is purely geometric and has nothing to do with the arithmetic weights:

* the support of a round-6 coefficient is the polar box (5.14) (`Defs6.IsBetaCoeff6.support`),
  `InPolarBox Pa φ z` ⟺ primary, `N < |z|² ≤ (1+θ)N`, `φ < arg z ≤ φ + 2πθ`;
* that box lies in a disc of radius `5θ√N` (`FIArea4.dist_polarBox_le`), and a disc of radius
  `< 1/2` contains at most **one** Gaussian integer, since distinct Gaussian integers are at
  distance `≥ 1` — this is `FIArea3.polarBoxCardLeOne`, which applies verbatim to our hypothesis
  `hu : θ√N < 1/10`;
* hence for a pair `(z₁,z₂)` with `β z₁ ≠ 0` and `β z₂ ≠ 0` we get `z₁ = z₂`, and the coprimality
  indicator `copInd` of a *diagonal* pair vanishes: `(z,z) = 1` in `ℤ[i]` forces `z` to be a unit,
  i.e. `|z|² = 1` (`Zsqrtd.norm_eq_one_iff`), while the polar box forces `|z|² > N ≥ 1`.

So every summand of the double sum has a factor `copInd z₁ z₂ = 0` or a factor `‖β zᵢ‖ = 0`, and
the whole sum vanishes.
-/
import Mathlib
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.polarBoxCardLeOne
import Submission.Work.FITop4.Defs6
import Submission.Work.FIArea4.polarBox_card_le

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- **The (10.6)/(10.7) pair sum vanishes in the small-`u` regime `θ√N < 1/10`.**

The polar box (5.14) supporting `β` contains at most one lattice point
(`FIArea3.polarBoxCardLeOne`), so the only pair whose two coefficients could both be non-zero is
the diagonal one; and `copInd z z = 0` there, because `(z,z) = 1` forces `|z|² = 1` while the box
forces `|z|² > N ≥ 1`. -/
theorem zeroPairSum_of_small_u {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β)
    (hu : Pa.θ * Real.sqrt Pa.N < (1 : ℝ) / 10) :
    (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        Work.FIArea2.R6.copInd z1 z2 * (‖β z1‖ * ‖β z2‖
          * (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
          * (((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
          * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ))) = 0 := by
  -- the polar box contains at most one point
  have hcard : (Work.FIArea3.polarBoxFinset Pa φ).card ≤ 1 :=
    Work.FIArea3.polarBoxCardLeOne Pa φ hu
  refine Finset.sum_eq_zero fun z1 hz1 => Finset.sum_eq_zero fun z2 hz2 => ?_
  by_cases hcop : Work.FIPlan.GaussCoprime z1 z2
  · -- the pair is coprime: then one of the two coefficients must vanish
    rw [Work.FIArea2.R6.copInd, if_pos hcop, one_mul]
    by_cases hb1 : β z1 = 0
    · simp [hb1]
    · by_cases hb2 : β z2 = 0
      · simp [hb2]
      · -- both coefficients non-zero: both points lie in the polar box, hence coincide
        exfalso
        have hp1 : Work.FITop3.InPolarBox Pa φ z1 := Work.FITop4.IsBetaCoeff6.support hβ hb1
        have hp2 : Work.FITop3.InPolarBox Pa φ z2 := Work.FITop4.IsBetaCoeff6.support hβ hb2
        have hm1 : z1 ∈ Work.FIArea3.polarBoxFinset Pa φ := by
          rw [Work.FIArea3.mem_polarBoxFinset]; exact ⟨hz1, hp1⟩
        have hm2 : z2 ∈ Work.FIArea3.polarBoxFinset Pa φ := by
          rw [Work.FIArea3.mem_polarBoxFinset]; exact ⟨hz2, hp2⟩
        have hz12 : z1 = z2 := (Finset.card_le_one.mp hcard) z1 hm1 z2 hm2
        -- `(z,z) = 1` makes `z` a unit, i.e. `|z|² = 1`
        have hunit : IsUnit z2 := isCoprime_self.mp (hz12 ▸ hcop)
        have hnorm : Work.FIPlan.gnorm z2 = 1 := Zsqrtd.norm_eq_one_iff.mpr hunit
        -- while the polar box forces `|z|² > N ≥ 1`
        have hNlt : Pa.N < (Work.FIPlan.gnorm z2 : ℝ) := hp2.2.1
        rw [hnorm] at hNlt
        push_cast at hNlt
        linarith [Pa.hN1]
  · -- the pair is not coprime: the indicator kills the summand
    rw [Work.FIArea2.R6.copInd, if_neg hcop, zero_mul]

end Work.FIArea2.R6
