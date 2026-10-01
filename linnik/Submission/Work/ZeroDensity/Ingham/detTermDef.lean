import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs

/-!
# A named summand for the detector sums

The summand of the detector sums of `Work.ZeroDensity.Ingham.zetaDetectorDefs` is
`a_K(n) n^{-ρ} e^{-n/Y}` with `a_K(n) = mCoef K n`.  This module gives it a name,
`detTerm`, and records the (definitional) rewriting lemmas expressing `detSum`,
`detTail` and `detFarTail` in terms of it.
-/

open scoped Classical BigOperators
open MeasureTheory

namespace Work.ZeroDensity.Ingham

/-- The summand `a_K(n) n^{-ρ} e^{-n/Y}` of the detector sums. -/
noncomputable def detTerm (K : ℕ) (Y : ℝ) (ρ : ℂ) (n : ℕ) : ℂ :=
  mCoef K n * (n : ℂ) ^ (-ρ) * Complex.exp (-(n : ℂ) / Y)

lemma detSum_eq_tsum (K : ℕ) (Y : ℝ) (ρ : ℂ) :
    detSum K Y ρ = ∑' n, detTerm K Y ρ n := rfl

lemma detTail_eq_sum (K : ℕ) (Y Z : ℝ) (ρ : ℂ) :
    detTail K Y Z ρ = ∑ n ∈ Finset.Ioc K ⌊Z⌋₊, detTerm K Y ρ n := rfl

lemma detFarTail_eq_tsum (K : ℕ) (Y Z : ℝ) (ρ : ℂ) :
    detFarTail K Y Z ρ = ∑' n, (if ⌊Z⌋₊ < n then detTerm K Y ρ n else 0) := rfl

end Work.ZeroDensity.Ingham
