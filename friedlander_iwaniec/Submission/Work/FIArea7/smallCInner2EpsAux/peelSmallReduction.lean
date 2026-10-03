/-
# `peelSmallReduction` — the peeled small part of the inner `ℓ`-sum, rewritten as a
double sum over `(q ≤ z, p > z prime)` with the smooth weight `P(c·pq)`.

This is the `peelSmall2`/`cTerm` analogue of `peelSmall_eq` of
`Submission/Work/FIArea7/smallCInner.lean`.
-/
import Mathlib
import Submission.Work.FIArea7.smallCInner2EpsAux.peelSmallAux

set_option autoImplicit false

namespace Work.FIArea7.smallCInner2EpsAux

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem peelSmallReduction (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (k : ℤ)
    (c u z : ℕ) (P : ℝ → ℝ) :
    Work.FIArea7.smallCInner2EpsAux.peelSmall2 u z
        (Work.FIArea7.smallCInner2EpsAux.cTerm Pa chi k c P)
      = ∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
          ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pPrimeSet u z,
            (if p * q ≤ u then
              Work.FIArea7.nspInd Pa (p * q) * (ArithmeticFunction.moebius (p * q) : ℂ)
                * (if Nat.Coprime c (p * q) then (1 : ℂ) else 0)
                * ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
                * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))
              else 0) := by
  have hinner : ∀ p ∈ Work.FIArea7.smallCInner2EpsAux.pPrimeSet u z,
      ∀ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
      (if Squarefree (p * q) ∧ p * q ≤ u
        then Work.FIArea7.smallCInner2EpsAux.cTerm Pa chi k c P (p * q)
          / ((Work.FIArea7.largePrimeCount u z (p * q) : ℕ) : ℂ) else 0)
      = (if p * q ≤ u then
            Work.FIArea7.nspInd Pa (p * q) * (ArithmeticFunction.moebius (p * q) : ℂ)
              * (if Nat.Coprime c (p * q) then (1 : ℂ) else 0)
              * ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))
          else 0) := by
    intro p hp q hq
    have hp' : p ∈ (Finset.Icc 1 u).filter (fun p => p.Prime ∧ z < p) := hp
    have hq' : q ∈ (Finset.Icc 1 u).filter (fun q => q ≤ z) := hq
    obtain ⟨hpp, hzp⟩ := (Finset.mem_filter.mp hp').2
    have hzq : q ≤ z := (Finset.mem_filter.mp hq').2
    by_cases h : Squarefree (p * q) ∧ p * q ≤ u
    · rw [if_pos h, if_pos h.2,
        largePrimeCount_eq_one hpp hzp h.2 hzq h.1, Nat.cast_one, div_one]
      unfold Work.FIArea7.smallCInner2EpsAux.cTerm
      by_cases hc : Nat.Coprime c (p * q)
      · rw [if_pos hc, if_pos hc]; ring
      · rw [if_neg hc, if_neg hc]; ring
    · rw [if_neg h]
      by_cases hle : p * q ≤ u
      · rw [if_pos hle]
        have hnsq : ¬ Squarefree (p * q) := fun hsq => h ⟨hsq, hle⟩
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
        ring
      · rw [if_neg hle]
  calc Work.FIArea7.smallCInner2EpsAux.peelSmall2 u z
        (Work.FIArea7.smallCInner2EpsAux.cTerm Pa chi k c P)
      = ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pPrimeSet u z,
          ∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
            (if Squarefree (p * q) ∧ p * q ≤ u
              then Work.FIArea7.smallCInner2EpsAux.cTerm Pa chi k c P (p * q)
                / ((Work.FIArea7.largePrimeCount u z (p * q) : ℕ) : ℂ) else 0) := rfl
    _ = ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pPrimeSet u z,
          ∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
            (if p * q ≤ u then
              Work.FIArea7.nspInd Pa (p * q) * (ArithmeticFunction.moebius (p * q) : ℂ)
                * (if Nat.Coprime c (p * q) then (1 : ℂ) else 0)
                * ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
                * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))
              else 0) :=
        Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => hinner p hp q hq))
    _ = ∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
          ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pPrimeSet u z,
            (if p * q ≤ u then
              Work.FIArea7.nspInd Pa (p * q) * (ArithmeticFunction.moebius (p * q) : ℂ)
                * (if Nat.Coprime c (p * q) then (1 : ℂ) else 0)
                * ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
                * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))
              else 0) := Finset.sum_comm

end

end Work.FIArea7.smallCInner2EpsAux
