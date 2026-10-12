import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.NeuFrac.bddBelow_trialSet`

The Dirichlet-principle trial functional of FS `eq:DefT`'s first term (the Neumann fraction
`neuFrac`) is

`T_u(g) = ∫_{Λ(u)} ψ² − 2a²∫_{Λ(u)} ψ g + a²(Σ_k∫_{Λ(u)} (∂_k g)² + a²∫_{Λ(u)} g²)`,

`Λ(u) = lamBox ℓ u`, over globally smooth compactly supported trials `g`.  This file proves
that the set of values of `T_u` is **bounded below**, for every integrable `ψ²` and every
`a² ≥ 0`.

The lower bound is `0`, and the mathematics is completing the square:

`∫_{Λ}ψ² − 2a²∫_{Λ}ψg + (a²)²∫_{Λ}g² = ∫_{Λ}(ψ − a²g)² ≥ 0`

(the three integrals being finite because `ψ²` is integrable by hypothesis and `g²` is
integrable as a continuous compactly supported function on a box of finite measure), while
the kinetic term `a²Σ_k∫_{Λ}(∂_k g)²` is a sum of integrals of squares, hence `≥ 0`.  In the
case that `ψg` is *not* integrable over the box its Bochner integral is `0` by convention
and the identity is not needed: the remaining terms are all `≥ 0` individually.

Consequences: `neuFrac ℓ a² u ψ = sInf` of this set is well defined, and `0` is a valid
lower bound in every `csInf`-based API lemma (`csInf_le`, `le_csInf`, ...).

## Contents

* `integral_sq_sub_sq` — completing the square under the integral sign;
* `integrableOn_sq_of_contDiff` — `g²` integrable over the box for `g` smooth of compact
  support;
* `bddBelow_trialSet` — the target.
-/

noncomputable section

open MeasureTheory

open scoped Topology ENNReal

namespace Work.BoseKinLoc.NeuFrac

set_option linter.unusedVariables false

/-- **Completing the square under the integral sign.**  If `ψ²`, `ψg` and `g²` are all
integrable then the quadratic form `∫ψ² − 2a²∫ψg + (a²)²∫g²` is the integral of the square
`(ψ − a²g)²`. -/
lemma integral_sq_sub_sq {μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))}
    {ψ g : EuclideanSpace ℝ (Fin 3) → ℝ} {a2 : ℝ}
    (hA : MeasureTheory.Integrable (fun z => (ψ z) ^ 2) μ)
    (hB : MeasureTheory.Integrable (fun z => ψ z * g z) μ)
    (hD : MeasureTheory.Integrable (fun z => (g z) ^ 2) μ) :
    (∫ z, (ψ z) ^ 2 ∂μ) - 2 * a2 * (∫ z, ψ z * g z ∂μ) + a2 ^ 2 * (∫ z, (g z) ^ 2 ∂μ)
      = ∫ z, (ψ z - a2 * g z) ^ 2 ∂μ := by
  have h2 : MeasureTheory.Integrable (fun z => -(2 * a2) * (ψ z * g z)) μ := hB.const_mul _
  have h3 : MeasureTheory.Integrable (fun z => a2 ^ 2 * (g z) ^ 2) μ := hD.const_mul _
  have hcongr : (∫ z, (ψ z - a2 * g z) ^ 2 ∂μ)
      = ∫ z, ((ψ z) ^ 2 + (-(2 * a2)) * (ψ z * g z) + a2 ^ 2 * (g z) ^ 2) ∂μ := by
    apply integral_congr_ae
    filter_upwards with z
    ring
  have hsplit1 : (∫ z, ((ψ z) ^ 2 + (-(2 * a2)) * (ψ z * g z) + a2 ^ 2 * (g z) ^ 2) ∂μ)
      = (∫ z, ((ψ z) ^ 2 + (-(2 * a2)) * (ψ z * g z)) ∂μ)
        + (∫ z, a2 ^ 2 * (g z) ^ 2 ∂μ) :=
    integral_add (hA.add h2) h3
  have hsplit2 : (∫ z, ((ψ z) ^ 2 + (-(2 * a2)) * (ψ z * g z)) ∂μ)
      = (∫ z, (ψ z) ^ 2 ∂μ) + (∫ z, (-(2 * a2)) * (ψ z * g z) ∂μ) :=
    integral_add hA h2
  have hcm : (∫ z, (-(2 * a2)) * (ψ z * g z) ∂μ) = -(2 * a2) * (∫ z, ψ z * g z ∂μ) :=
    integral_const_mul _ _
  have hcm2 : (∫ z, a2 ^ 2 * (g z) ^ 2 ∂μ) = a2 ^ 2 * (∫ z, (g z) ^ 2 ∂μ) :=
    integral_const_mul _ _
  rw [hcongr, hsplit1, hsplit2, hcm, hcm2]
  ring

/-- The square of a smooth compactly supported function is integrable over the moving box
(a box of finite Lebesgue measure). -/
lemma integrableOn_sq_of_contDiff {ℓ : ℝ} {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgs : HasCompactSupport g) (u : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable (fun z => (g z) ^ 2)
      (volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) := by
  have hgs2 : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) => (g z) ^ 2) := by
    have h := hgs.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
    simpa [Function.comp_def] using h
  exact ((hg.continuous.pow 2).integrable_of_hasCompactSupport hgs2).integrableOn

lemma bddBelow_trialSet {ℓ a2 : ℝ} (ha2 : 0 ≤ a2) (u : EuclideanSpace ℝ (Fin 3))
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z) ^ 2)) :
    BddBelow {c : ℝ | ∃ g : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiff ℝ (⊤ : ENat) g ∧ HasCompactSupport g ∧
      c = (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2)
          - 2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, ψ z * g z)
          + a2 * ((∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ u,
                    (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
                  + a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2))} := by
  refine ⟨0, ?_⟩
  rintro c ⟨g, hg, hgs, hcval⟩
  rw [hcval]
  set Λ := Work.BoseKinLoc.lamBox ℓ u with hΛdef
  -- integrability of `ψ²` over the box (the hypothesis, restricted)
  have hAint : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z) ^ 2)
      (volume.restrict Λ) := hψ.integrableOn
  -- integrability of `g²` over the box
  have hDint : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (g z) ^ 2)
      (volume.restrict Λ) := integrableOn_sq_of_contDiff hg hgs u
  -- nonnegativity of the three quadratic pieces
  have hA_nn : 0 ≤ ∫ z in Λ, (ψ z) ^ 2 := integral_nonneg (fun z => sq_nonneg _)
  have hD_nn : 0 ≤ ∫ z in Λ, (g z) ^ 2 := integral_nonneg (fun z => sq_nonneg _)
  have hK_nn : 0 ≤ ∑ k : Fin 3, ∫ z in Λ,
      (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
    Finset.sum_nonneg (fun k _ => integral_nonneg (fun z => sq_nonneg _))
  -- the tail `a²(Σ_k∫(∂_k g)² + a²∫g²)` is nonnegative
  have htail : 0 ≤ a2 * ((∑ k : Fin 3, ∫ z in Λ,
        (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2) + a2 * (∫ z in Λ, (g z) ^ 2)) :=
    mul_nonneg ha2 (add_nonneg hK_nn (mul_nonneg ha2 hD_nn))
  -- the completed square is nonnegative
  have key : 0 ≤ (∫ z in Λ, (ψ z) ^ 2) - 2 * a2 * (∫ z in Λ, ψ z * g z)
      + a2 ^ 2 * (∫ z in Λ, (g z) ^ 2) := by
    by_cases hint : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => ψ z * g z)
        (volume.restrict Λ)
    · rw [integral_sq_sub_sq hAint hint hDint]
      exact integral_nonneg (fun z => sq_nonneg _)
    · rw [integral_undef hint]
      nlinarith [hA_nn, hD_nn, ha2, sq_nonneg a2]
  -- and the fully expanded kinetic term dominates the remaining `(a²)²∫g²`
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
