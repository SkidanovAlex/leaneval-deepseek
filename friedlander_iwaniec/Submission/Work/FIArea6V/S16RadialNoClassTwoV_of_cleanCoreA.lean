import Mathlib
import Submission.Work.FIArea6V.Defs
import Submission.Work.FIArea6Hecke.S16CoreDefs

namespace Work.FIArea6V

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The τ/axis-restricted summand equals the clean summand, pointwise.**

For a fixed `z`, the radial §16 summand (support `IsPrimary ∧ NoSmallPrimes ∧ τ(|z|²) ≤ Pa.τ ∧
IsAxisFree`) and the clean §16 summand (support `IsPrimary ∧ NoSmallPrimes`) agree.

The only non-trivial case is `IsPrimary ∧ NoSmallPrimes` with the τ- or axis-clause failing: there
the clean summand is the full §16 term and the radial one is `0`, so one must show the §16 term
vanishes.  If it did not, then both mollifiers would be non-zero at `z`, so `|z|² ∈ (N, (1+θ)N]`
and — using `q(0) = 0` (`Work.FIArea6Hecke.mollQ_zero`, since `q` is supported on `[0, 2πθ]`) —
`φ < arg z ≤ φ + 2πθ`, i.e. `z` lies in the polar box; `TauVac` then gives `τ(|z|²) ≤ Pa.τ` and
the axis-free hypothesis gives `IsAxisFree`, contradicting the failure of the radial clause. -/
private lemma radialSummand_eq_cleanSummand (Pa : Work.FITop.Params) (φ : ℝ) (j : ℤ)
    (chi : GaussianInt → ℂ) (q p : ℝ → ℝ)
    (hqC : ContDiff ℝ 2 q)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * Pa.θ)
    (hpsupp : ∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hTau : Work.FIArea6V.TauVac Pa φ)
    (hAxis : ∀ z, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z)
    (z : GaussianInt) :
    (if Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z
        ∧ (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
        ∧ Work.FITop4.IsAxisFree Pa z then
      ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
        * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
        * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
        * chi z
        * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j
    else 0)
    = (if Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z then
      ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
        * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
        * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
        * chi z
        * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j
    else 0) := by
  by_cases hC : Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z
  · by_cases hR : (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧
        Work.FITop4.IsAxisFree Pa z
    · rw [if_pos ⟨hC.1, hC.2, hR.1, hR.2⟩, if_pos hC]
    · rw [if_neg (fun hh => hR ⟨hh.2.2.1, hh.2.2.2⟩), if_pos hC]
      by_contra hE
      have hqne : q (Complex.arg z.toComplex - φ) ≠ 0 := by
        intro hq
        exact hE (by simp [hq])
      have hpne : p (Work.FIPlan.gnorm z) ≠ 0 := by
        intro hp
        exact hE (by simp [hp])
      have hβ := hqsupp _ hqne
      have hn := hpsupp _ hpne
      have hq0 : q 0 = 0 := Work.FIArea6Hecke.mollQ_zero hqC hqsupp
      have hstrict : φ < (Complex.arg z.toComplex : ℝ) := by
        rcases lt_or_eq_of_le hβ.1 with h | h
        · linarith
        · exact absurd (h.symm ▸ hq0) hqne
      have hIPB : Work.FITop4.InPolarBox Pa φ z :=
        ⟨hC.1, hn.1, hn.2, hstrict, by linarith [hβ.2]⟩
      exact hR ⟨hTau z hIPB hC.2, hAxis z hIPB⟩
  · rw [if_neg (fun hh => hC ⟨hh.1, hh.2.1⟩), if_neg hC]

/-- **`S16RadialNoClassTwoV` from the clean §16 core `S16CleanCoreTwoA`.**

Both statements differ only in their support indicator: the radial sum carries the extra clauses
`τ(|z|²) ≤ Pa.τ` (5.9) and `IsAxisFree` inside the `if`, and receives `TauVac Pa φ` as a
hypothesis.  By `radialSummand_eq_cleanSummand` the two box sums are *equal* as finite sums, so
the clean core's bound transports verbatim, with the same constants `c, C, x0`. -/
theorem S16RadialNoClassTwoV_of_cleanCoreA (h : Work.FIArea6V.S16CleanCoreTwoA) :
    Work.FIArea6V.S16RadialNoClassTwoV := by
  intro ε hε0 hε4
  obtain ⟨c, C, x0, hc, hC, hx0, hbound⟩ := h ε hε0 hε4
  refine ⟨c, C, x0, hc, hC, hx0, ?_⟩
  intro Pa hx φ ν d j chi q p hTau hAxis hν0 hν1 hd1 hdν hj hchi hqC hpC hq0 hq1 hqsupp hqd
    hpu0 hpu1 hpsupp hpd
  have hclean := hbound Pa hx φ ν d j chi q p hAxis hν0 hν1 hd1 hdν hj hchi hqC hpC hq0 hq1
    hqsupp hqd hpu0 hpu1 hpsupp hpd
  have hEq :
      (∑ z ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z
              ∧ (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
              ∧ Work.FITop4.IsAxisFree Pa z then
            ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j
          else 0))
        = (∑ z ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z then
            ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j
          else 0)) :=
    Finset.sum_congr rfl (fun z _ =>
      radialSummand_eq_cleanSummand Pa φ j chi q p hqC hqsupp hpsupp hTau hAxis z)
  rw [hEq]
  exact hclean

end

end Work.FIArea6V
