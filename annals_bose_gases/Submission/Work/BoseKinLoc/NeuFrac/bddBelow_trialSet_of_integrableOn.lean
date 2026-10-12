import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.NeuFrac.bddBelow_trialSet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.NeuFrac.bddBelow_trialSet_of_integrableOn`

The defining trial functional of `neuFrac` (FS `eq:DefT`, first term),

`T_u(g) = ∫_{Λ(u)} ϕ² − 2a²∫_{Λ(u)} ϕ g
          + a²(Σ_k∫_{Λ(u)} (∂_k g)² + a²∫_{Λ(u)} g²)`,   `Λ(u) = lamBox ℓ u`,

over globally smooth compactly supported trials `g`, has a trial set that is **bounded
below** as soon as `ϕ²` is integrable **on the box** `Λ(u)` — no global integrability of
`ϕ²` is needed.  This is the box-restricted strengthening of
`Work.BoseKinLoc.NeuFrac.bddBelow_trialSet` (which assumes `ϕ²` integrable on all of `ℝ³`);
it is the precise hypothesis that the consumer `Work.BoseKinLoc.Kinetic.neuFrac_Qfree_bounds`
can supply for `ϕ = Q_uψ` (whose square is *not* globally integrable, since `Q_uψ` tends to
`−m_u(ψ) ≠ 0` at infinity).

## The argument

The lower bound is `0`.  For an admissible trial `g` write `Λ := lamBox ℓ u` and split the
value as

`T_u(g) = [∫_Λ ϕ² − 2a²∫_Λ ϕg + (a²)²∫_Λ g²] + a²(Σ_k∫_Λ (∂_k g)²)
          + [(a²)²∫_Λ g² − (a²)²∫_Λ g²]`,

where

* the first bracket is the completed square `∫_Λ (ϕ − a²g)² ≥ 0` whenever `ϕg` is
  integrable on the box (`integral_sq_sub_sq`, with `ϕ²` integrable on the box by
  hypothesis and `g²` integrable on the box because `g` is smooth of compact support on a
  box of finite measure, `integrableOn_sq_of_contDiff`);
* if `ϕg` is **not** integrable on the box, its Bochner integral is `0`
  (`integral_undef`) and the individual nonnegativity of `∫_Λ ϕ²` and `∫_Λ g²` suffices;
* the kinetic bracket `a²Σ_k∫_Λ (∂_k g)²` is `≥ 0` (sum of integrals of squares), and it
  dominates the leftover `(a²)²∫_Λ g² ≤ a²·(a²∫_Λ g²)` (with equality).

## Contents

* `bddBelow_trialSet_of_integrableOn` — the target, with lower bound `0`.
-/

noncomputable section

open MeasureTheory

open scoped Topology ENNReal

namespace Work.BoseKinLoc.NeuFrac

set_option linter.unusedVariables false

/-- **Boundedness below of the `neuFrac` trial set from box-restricted `L²`.**

The trial functional of `neuFrac` on `Λ = lamBox ℓ u`,

`T_Λ(g) = ∫_Λ ϕ² − 2a²∫_Λ ϕg + a²(Σ_k∫_Λ (∂_kg)² + a²∫_Λ g²)`,

satisfies `T_Λ(g) ≥ 0` for every smooth compactly supported `g` as soon as `ϕ²` is
integrable on the box; hence the set of trial values is bounded below (by `0`).

Completing the square under the box integral gives
`∫_Λ ϕ² − 2a²∫_Λ ϕg + (a²)²∫_Λ g² = ∫_Λ (ϕ − a²g)² ≥ 0`, and the remaining kinetic term
`a²Σ_k∫_Λ (∂_kg)²` is a sum of integrals of squares.  In the case that `ϕg` is not
integrable over the box its Bochner integral is `0` by convention (`integral_undef`) and
the completed square is not needed: the individual nonnegativity of `∫_Λ ϕ²` and
`∫_Λ g²` suffices.

This is `bddBelow_trialSet` with the hypothesis weakened from global `L²` of `ϕ` to the
box-restricted integrability of `ϕ²`, which is all the argument uses. -/
lemma bddBelow_trialSet_of_integrableOn {ℓ a2 : ℝ} (ha2 : 0 ≤ a2) (u : EuclideanSpace ℝ (Fin 3))
    {ϕ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hϕ : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (ϕ z) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Work.BoseKinLoc.lamBox ℓ u))) :
    BddBelow {c : ℝ | ∃ g : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiff ℝ (⊤ : ENat) g ∧ HasCompactSupport g ∧
      c = (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ϕ z) ^ 2)
          - 2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, ϕ z * g z)
          + a2 * ((∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ u,
                    (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
                  + a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2))} := by
  refine ⟨0, ?_⟩
  rintro c ⟨g, hg, hgs, hcval⟩
  rw [hcval]
  set Λ := Work.BoseKinLoc.lamBox ℓ u with hΛdef
  -- integrability of `ϕ²` over the box (the hypothesis, up to unfolding the `set`)
  have hAint : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (ϕ z) ^ 2)
      (MeasureTheory.volume.restrict Λ) := by
    simpa only [hΛdef] using hϕ
  -- integrability of `g²` over the box (smooth compact support on a finite-measure box)
  have hDint : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (g z) ^ 2)
      (MeasureTheory.volume.restrict Λ) :=
    integrableOn_sq_of_contDiff hg hgs u
  -- nonnegativity of the three quadratic pieces
  have hA_nn : 0 ≤ ∫ z in Λ, (ϕ z) ^ 2 := integral_nonneg (fun z => sq_nonneg _)
  have hD_nn : 0 ≤ ∫ z in Λ, (g z) ^ 2 := integral_nonneg (fun z => sq_nonneg _)
  have hK_nn : 0 ≤ ∑ k : Fin 3, ∫ z in Λ,
      (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
    Finset.sum_nonneg (fun k _ => integral_nonneg (fun z => sq_nonneg _))
  -- the completed square is nonnegative
  have key : 0 ≤ (∫ z in Λ, (ϕ z) ^ 2) - 2 * a2 * (∫ z in Λ, ϕ z * g z)
      + a2 ^ 2 * (∫ z in Λ, (g z) ^ 2) := by
    by_cases hint : MeasureTheory.Integrable
        (fun z : EuclideanSpace ℝ (Fin 3) => ϕ z * g z) (MeasureTheory.volume.restrict Λ)
    · rw [integral_sq_sub_sq hAint hint hDint]
      exact integral_nonneg (fun z => sq_nonneg _)
    · rw [integral_undef hint]
      nlinarith [hA_nn, hD_nn, ha2, sq_nonneg a2]
  -- the kinetic term absorbs the `(a²)²∫g²` correction
  have hle : a2 ^ 2 * (∫ z in Λ, (g z) ^ 2)
      ≤ a2 * ((∑ k : Fin 3, ∫ z in Λ,
            (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          + a2 * (∫ z in Λ, (g z) ^ 2)) := by
    have hmul : a2 * ((∑ k : Fin 3, ∫ z in Λ,
            (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          + a2 * (∫ z in Λ, (g z) ^ 2))
        = a2 * (∑ k : Fin 3, ∫ z in Λ,
              (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          + a2 * (a2 * (∫ z in Λ, (g z) ^ 2)) := by ring
    rw [hmul]
    nlinarith [mul_nonneg ha2 hK_nn]
  linarith [key, hle]

end Work.BoseKinLoc.NeuFrac
