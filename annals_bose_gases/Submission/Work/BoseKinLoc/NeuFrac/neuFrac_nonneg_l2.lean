import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
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
# `Work.BoseKinLoc.NeuFrac.neuFrac_nonneg_l2`

The box Neumann fraction `neuFrac ℓ a² u ϕ` (BS Lemma 3.7 / FS `eq:DefT`'s first term) is
the infimum, over globally smooth compactly supported trials `g`, of the variational
functional

`T(g) = ∫_{Λ(u)} ϕ² − 2a²∫_{Λ(u)} ϕ·g + a²(Σ_k∫_{Λ(u)} (∂_k g)² + a²∫_{Λ(u)} g²)`,
`Λ(u) = lamBox ℓ u`.

This file proves `0 ≤ neuFrac ℓ a² u ϕ` for every `a² ≥ 0` and every `ϕ` whose **square is
integrable on the box** `Λ(u)` (i.e. `IntegrableOn (ϕ²) (lamBox ℓ u)`, equivalently
`Integrable (ϕ²) (volume.restrict (lamBox ℓ u))`) — which is exactly the hypothesis under
which the defining `sInf` is bounded below (see `NeuFrac/bddBelow_trialSet.lean` for the
counterexamples showing that the hypothesis cannot be dropped).

## The mathematics

Completing the square **under the box integral**, for any admissible trial `g`,

`∫_{Λ} ϕ² − 2a²∫_{Λ} ϕg + (a²)²∫_{Λ} g² = ∫_{Λ} (ϕ − a²g)² ≥ 0`,

while the kinetic term `a² Σ_k ∫_{Λ} (∂_k g)²` is a sum of integrals of squares, hence `≥ 0`.
So **every** member of the defining trial set is `≥ 0`; the set is nonempty (`g = 0` is
admissible), whence `0 ≤ sInf`.

Two Lean conventions are respected in the proof (they are why the argument is phrased with
the case split on `Integrable (ϕ·g)`):

* the Bochner integral of a non-integrable real function is `0` (`integral_undef`); the
  completion of the square is an identity of integrals only when `ϕ·g` is integrable, and in
  the other case the middle term is `0` and the remaining terms are individually `≥ 0`;
* `sInf` of a set is only related to its members through `le_csInf`, which needs the set to
  be nonempty (it is) — no `BddBelow` is needed for that inequality.

No spectral theory is used: the "Neumann" content of the resolvent identity is *not* needed
here, only that the two mass terms combine into a square.

## Contents

* `integral_sq_sub_sq_l2` (private) — completing the square under the integral sign;
* `integrableOn_sq_of_contDiff_l2` (private) — `g²` is integrable over the box for a smooth
  compactly supported `g`;
* `neuFrac_nonneg_l2` — the requested statement.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.NeuFrac

open Submission.BoseGases

set_option linter.unusedVariables false

/-- **Completing the square under the integral sign.**  If `ϕ²`, `ϕ·g` and `g²` are all
integrable then `∫ϕ² − 2a²∫ϕg + (a²)²∫g² = ∫(ϕ − a²g)²`. -/
private lemma integral_sq_sub_sq_l2 {μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))}
    {ϕ g : EuclideanSpace ℝ (Fin 3) → ℝ} {a2 : ℝ}
    (hA : MeasureTheory.Integrable (fun z => (ϕ z) ^ 2) μ)
    (hB : MeasureTheory.Integrable (fun z => ϕ z * g z) μ)
    (hD : MeasureTheory.Integrable (fun z => (g z) ^ 2) μ) :
    (∫ z, (ϕ z) ^ 2 ∂μ) - 2 * a2 * (∫ z, ϕ z * g z ∂μ) + a2 ^ 2 * (∫ z, (g z) ^ 2 ∂μ)
      = ∫ z, (ϕ z - a2 * g z) ^ 2 ∂μ := by
  have h2 : MeasureTheory.Integrable (fun z => -(2 * a2) * (ϕ z * g z)) μ := hB.const_mul _
  have h3 : MeasureTheory.Integrable (fun z => a2 ^ 2 * (g z) ^ 2) μ := hD.const_mul _
  have hcongr : (∫ z, (ϕ z - a2 * g z) ^ 2 ∂μ)
      = ∫ z, ((ϕ z) ^ 2 + (-(2 * a2)) * (ϕ z * g z) + a2 ^ 2 * (g z) ^ 2) ∂μ := by
    apply integral_congr_ae
    filter_upwards with z
    ring
  have hsplit1 : (∫ z, ((ϕ z) ^ 2 + (-(2 * a2)) * (ϕ z * g z) + a2 ^ 2 * (g z) ^ 2) ∂μ)
      = (∫ z, ((ϕ z) ^ 2 + (-(2 * a2)) * (ϕ z * g z)) ∂μ)
        + (∫ z, a2 ^ 2 * (g z) ^ 2 ∂μ) :=
    integral_add (hA.add h2) h3
  have hsplit2 : (∫ z, ((ϕ z) ^ 2 + (-(2 * a2)) * (ϕ z * g z)) ∂μ)
      = (∫ z, (ϕ z) ^ 2 ∂μ) + (∫ z, (-(2 * a2)) * (ϕ z * g z) ∂μ) :=
    integral_add hA h2
  have hcm : (∫ z, (-(2 * a2)) * (ϕ z * g z) ∂μ) = -(2 * a2) * (∫ z, ϕ z * g z ∂μ) :=
    integral_const_mul _ _
  have hcm2 : (∫ z, a2 ^ 2 * (g z) ^ 2 ∂μ) = a2 ^ 2 * (∫ z, (g z) ^ 2 ∂μ) :=
    integral_const_mul _ _
  rw [hcongr, hsplit1, hsplit2, hcm, hcm2]
  ring

/-- The square of a smooth compactly supported function is integrable over the moving box
(a bounded set of finite Lebesgue measure). -/
private lemma integrableOn_sq_of_contDiff_l2 {ℓ : ℝ} {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) (u : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable (fun z => (g z) ^ 2)
      (volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) := by
  have hgs2 : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) => (g z) ^ 2) := by
    have h := hgs.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
    simpa [Function.comp_def] using h
  exact ((hg.continuous.pow 2).integrable_of_hasCompactSupport hgs2).integrableOn

/-- **The box Neumann fraction is nonnegative** for a state whose square is integrable on the
box: every value of the defining trial functional is `≥ 0`, so the infimum is `≥ 0`.

Completing the square: for a smooth compactly supported trial `g`,

`∫_Λ ϕ² − 2a²∫_Λ ϕg + a²(Σ_k∫_Λ(∂_kg)² + a²∫_Λ g²) = ∫_Λ(ϕ − a²g)² + a²Σ_k∫_Λ(∂_kg)² ≥ 0`. -/
lemma neuFrac_nonneg_l2 (ℓ a2 : ℝ) (ha2 : 0 ≤ a2) (u : ℝ³) (ϕ : ℝ³ → ℝ)
    (hϕ : MeasureTheory.IntegrableOn (fun z => (ϕ z) ^ 2) (Work.BoseKinLoc.lamBox ℓ u)) :
    0 ≤ Work.BoseKinLoc.neuFrac ℓ a2 u ϕ := by
  unfold Work.BoseKinLoc.neuFrac
  -- the defining trial set is nonempty: the zero trial is admissible
  refine le_csInf ⟨_, (0 : ℝ³ → ℝ), contDiff_const, HasCompactSupport.zero, rfl⟩ ?_
  -- and every member is `≥ 0` by completing the square
  rintro c ⟨g, hg, hgs, hcval⟩
  rw [hcval]
  -- integrability of `ϕ²` over the box is the hypothesis
  have hAint : MeasureTheory.Integrable (fun z : ℝ³ => (ϕ z) ^ 2)
      (volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) := hϕ
  -- integrability of `g²` over the box
  have hDint : MeasureTheory.Integrable (fun z : ℝ³ => (g z) ^ 2)
      (volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    integrableOn_sq_of_contDiff_l2 hg hgs u
  -- nonnegativity of the three quadratic pieces
  have hA_nn : 0 ≤ ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ϕ z) ^ 2 :=
    integral_nonneg (fun z => sq_nonneg _)
  have hD_nn : 0 ≤ ∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2 :=
    integral_nonneg (fun z => sq_nonneg _)
  have hK_nn : 0 ≤ ∑ k : Fin 3,
      ∫ z in Work.BoseKinLoc.lamBox ℓ u, (fderiv ℝ g z (kcStdBasis k)) ^ 2 :=
    Finset.sum_nonneg (fun k _ => integral_nonneg (fun z => sq_nonneg _))
  -- the completed square is nonnegative
  have key : 0 ≤ (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ϕ z) ^ 2)
      - 2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, ϕ z * g z)
      + a2 ^ 2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2) := by
    by_cases hint : MeasureTheory.Integrable
        (fun z : ℝ³ => ϕ z * g z) (volume.restrict (Work.BoseKinLoc.lamBox ℓ u))
    · rw [integral_sq_sub_sq_l2 hAint hint hDint]
      exact integral_nonneg (fun z => sq_nonneg _)
    · rw [integral_undef hint]
      nlinarith [hA_nn, hD_nn, ha2, sq_nonneg a2]
  -- and the kinetic term absorbs the `a²·a²∫g²` correction
  have hle : a2 ^ 2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2)
      ≤ a2 * ((∑ k : Fin 3,
            ∫ z in Work.BoseKinLoc.lamBox ℓ u, (fderiv ℝ g z (kcStdBasis k)) ^ 2)
          + a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2)) := by
    have hmul : a2 * ((∑ k : Fin 3,
            ∫ z in Work.BoseKinLoc.lamBox ℓ u, (fderiv ℝ g z (kcStdBasis k)) ^ 2)
          + a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2))
        = a2 * (∑ k : Fin 3,
              ∫ z in Work.BoseKinLoc.lamBox ℓ u, (fderiv ℝ g z (kcStdBasis k)) ^ 2)
          + a2 * (a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2)) := by ring
    rw [hmul]
    nlinarith [mul_nonneg ha2 hK_nn]
  linarith [key, hle]

end Work.BoseKinLoc.NeuFrac
