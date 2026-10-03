import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.prop172defs
import Submission.Work.FIArea7.SepDiv
import Submission.Work.FIArea7.sum_sqfree_peel

set_option autoImplicit false

namespace Work.FIArea7.smallCInner2EpsAux

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The summand of the inner `ℓ`-sum of *FI* (25.3), with the smooth weight `P` kept inside:
`[ℓ coprime to c] · nspInd(ℓ) · μ(ℓ) · P(c ℓ) · λ(c ℓ)`. -/
def cTerm (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (k : ℤ) (c : ℕ)
    (P : ℝ → ℝ) (ℓ : ℕ) : ℂ :=
  if Nat.Coprime c ℓ then
    Work.FIArea7.nspInd Pa ℓ * (ArithmeticFunction.moebius ℓ : ℂ)
      * ((P ((c : ℝ) * (ℓ : ℝ)) : ℝ) : ℂ)
      * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * ℓ)
  else 0

/-- The `q ≤ z` part of `peelSum` (the peeled linear part of *FI* (24.13)). -/
def peelSmall2 (u z : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ p ∈ (Finset.Icc 1 u).filter (fun p => p.Prime ∧ z < p),
    ∑ q ∈ (Finset.Icc 1 u).filter (fun q => q ≤ z),
      (if Squarefree (p * q) ∧ p * q ≤ u
        then f (p * q) / ((Work.FIArea7.largePrimeCount u z (p * q) : ℕ) : ℂ) else 0)

/-- The `q > z` part of `peelSum` (the peeled bilinear part of *FI* (24.13)). -/
def peelBig2 (u z : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ p ∈ (Finset.Icc 1 u).filter (fun p => p.Prime ∧ z < p),
    ∑ q ∈ (Finset.Icc 1 u).filter (fun q => z < q),
      (if Squarefree (p * q) ∧ p * q ≤ u
        then f (p * q) / ((Work.FIArea7.largePrimeCount u z (p * q) : ℕ) : ℂ) else 0)

/-- `peelSum` splits into its `q ≤ z` and `q > z` parts. -/
lemma peelSum_eq_small2_add_big2 (u z : ℕ) (f : ℕ → ℂ) :
    Work.FIArea7.peelSum u z f = peelSmall2 u z f + peelBig2 u z f := by
  rw [peelSmall2, peelBig2, Work.FIArea7.peelSum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  unfold Work.FIArea7.peelInner
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 u) (fun q => z < q), add_comm]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr ?_) fun q _ => rfl
  intro q _
  exact not_lt

end

end Work.FIArea7.smallCInner2EpsAux
