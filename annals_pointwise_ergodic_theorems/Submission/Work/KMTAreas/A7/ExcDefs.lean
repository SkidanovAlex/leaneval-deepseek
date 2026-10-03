/-
# The exceptional regime of the KMT large-scale estimate: vocabulary

This module fixes the predicate describing the *exceptional regime* of the paper's large-scale
analysis, together with the explicit bound `excBnd` on the parameters occurring in it, and the
unfolding of the exceptional part `exceptionalPart` in terms of that predicate.

The exceptional part of §6--§8 is

  `exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n = colTuple n - mainPartTuple n`,

i.e. the contribution of the admissible, large scales `N = ⌊a n⌋` which are *not* in the main
regime `k₁ + 2u ≤ Log N ∧ k₂ + 2u ≤ Log N` (`u = ⌊2^{2ρ max k₁ k₂}⌋`).  Unfolding the two
clamped families gives

  `exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
     = if ExcPred ρ C₀ l₁ l₂ k₁ k₂ ⌊a n⌋ then
         varpPiece (kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂ x
       else 0`,

the predicate `ExcPred` being the conjunction of the three conditions

* `inIndexSet C₀ (max l₁ l₂) k₁ k₂ N` (admissibility, i.e. `l₁,l₂,k₁,k₂ ≤ l_(N) = C₀ LogLog N`),
* `¬ mainRegime ρ k₁ k₂ N` (the exceptional regime),
* `splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < N` (the scale is large).

**The one structural fact.**  Together these force the parameters to be bounded in terms of `C₀`
alone (uniformly in `ρ ∈ (0,1]`): see `Work.KMTAreas.A7.excBnd` and the (delegated) estimate
`ExceptionalSupport` in `KMTAreas/A7/ExceptionalSupport.lean`.  Consequently only `O_{C₀}(1)`
lacunary scales are exceptional, which is what makes the crude bound `ExceptionalBound` available.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract
open Work.Analysis.EndVar

/-- The explicit bound `B(C₀)` on the parameters `N, l₁, l₂, k₁, k₂` of the exceptional regime.
It is deliberately generous: only its existence matters for the final constant. -/
def excBnd (C₀ : ℕ) : ℕ := 8 * (C₀ + 2) ^ 2 + 64

/-- **The exceptional regime at the scale `N`.** -/
def ExcPred (ρ : ℝ) (C₀ : ℕ) (l₁ l₂ k₁ k₂ : ℕ) (N : ℕ) : Prop :=
  inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) N ∧
    ¬ mainRegime ρ k₁ k₂ N ∧
    splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < N

/-- The exceptional regime predicate is decidable (the components are decidable, `mainRegime`
being a conjunction of decidable comparisons). -/
instance decidableExcPred (ρ : ℝ) (C₀ : ℕ) (l₁ l₂ k₁ k₂ N : ℕ) :
    Decidable (ExcPred ρ C₀ l₁ l₂ k₁ k₂ N) := by
  unfold ExcPred; infer_instance

/-- **Unfolding of the exceptional part.**  The difference of the clamped family and its main part
is the paraproduct piece at the exceptional scales, and vanishes elsewhere. -/
theorem exceptionalPart_apply (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) (x : ℤ) :
    exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x =
      if ExcPred ρ C₀ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
        varpPiece (kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂ x else 0 := by
  unfold exceptionalPart colTuple mainPartTuple varpCol ExcPred
  by_cases hI : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
  <;> by_cases hS : splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n)
  <;> by_cases hM : mainRegime ρ k₁ k₂ (Nat.floor (a n))
  <;> simp only [hI, hS, hM, if_true, if_false, and_true, and_false, true_and, false_and,
        not_true_eq_false, not_false_eq_true, not_false_eq_true]
  <;> ring

/-- The exceptional part vanishes off the exceptional regime. -/
theorem exceptionalPart_eq_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) (h : ¬ ExcPred ρ C₀ l₁ l₂ k₁ k₂ (Nat.floor (a n))) :
    exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n = 0 := by
  funext x
  rw [exceptionalPart_apply, if_neg h]
  rfl

end

end Work.KMTAreas.A7
