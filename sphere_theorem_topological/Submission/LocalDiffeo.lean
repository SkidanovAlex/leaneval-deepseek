import Submission.CutStep2
import Submission.CutStep
import Submission.CutStep3
import Submission.GExpRay2

/-!
# `GExp p` is a local diffeomorphism near the origin: local injectivity at small radii

The cut-point step needs `GExp p` to be **locally injective** at vectors of norm `inj(p)`
(`CutStep3.exists_two_minimising_of_hloc_sphere`).  The full statement is the classical
*"`exp_p` is a local diffeomorphism at non-conjugate vectors"*, whose proof needs the global
geodesic flow.  This file proves the **base case**: `GExp p` is locally injective on a ball around
the origin.

The argument is a three-line composition of already-proved results:

* `GlobalExp.exists_pos_GExp_eq_expMap` — on the fibre ball of radius `ρ₁`, `GExp p = expMap p`;
* `CutStep.exists_radius_not_locally_injective` — **Rauch's theorem** in the form "`expMap p` is
  injective on a neighbourhood of every `w` with *model* norm `< R`" (this is the contrapositive of
  the degenerate branch of the minimum-witness dichotomy, with `p` and the conjugate point excluded
  by Rauch below the conjugate radius `π/2`);
* `GExpRay2.exists_model_norm_le_fibre_div` — the model norm is controlled by the fibre norm,
  `‖(v : E)‖ ≤ ‖v‖/√lam`,

so it suffices to take the fibre ball of radius `min ρ₁ (R √lam)`.

## Contents

* `exists_pos_locallyInjectiveAtGExp` — `∃ ρ > 0, ∀ w, ‖w‖ < ρ → LocallyInjectiveAtGExp hmet p w`;
* `exists_two_minimising_of_not_injAtLeast_of_lt` — the cut-point step for injectivity radii below
  that `ρ`: a *fully proved* instance of the cut-point step.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.InjRadius
open Submission.CutStep
open Submission.CutStep2
open Submission.CutStep3
open Submission.GExpBoundary

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.LocalDiffeo

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **`GExp p` is locally injective near the origin.**  There is `ρ > 0` such that `GExp p` is
injective on a neighbourhood of every `w` with fibre norm `‖w‖ < ρ`.

This is the base case of the classical *"`exp_p` is a local diffeomorphism at non-conjugate
vectors"*: the radius `ρ` is the minimum of the chart-agreement radius of `GExp p` with `expMap p`
and of `R √lam`, where `R` is the radius up to which Rauch's theorem makes `expMap p` locally
injective (in the *model* norm) and `lam` is the chart-metric lower bound converting the model norm
into the fibre norm. -/
theorem exists_pos_locallyInjectiveAtGExp (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hpinch : QuarterPinched cov) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ w : TangentSpace I p, ‖w‖ < ρ →
      LocallyInjectiveAtGExp (I := I) hmet p w := by
  obtain ⟨ρ₁, hρ₁, hagree⟩ := exists_pos_GExp_eq_expMap (cov := cov) hmet p
  obtain ⟨R, hR, hRnl⟩ :=
    Submission.CutStep.exists_radius_not_locally_injective (cov := cov) hmet htor hpinch p
  obtain ⟨lam, hlam, hbnd⟩ :=
    Submission.GExpRay2.exists_model_norm_le_fibre_div (I := I) p
  have hsqrtlam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsqrtne : Real.sqrt lam ≠ 0 := ne_of_gt hsqrtlam
  refine ⟨min ρ₁ (R * Real.sqrt lam), lt_min hρ₁ (mul_pos hR hsqrtlam), fun w hw => ?_⟩
  have hwρ₁ : ‖w‖ < ρ₁ := lt_of_lt_of_le hw (min_le_left _ _)
  have hwR : ‖w‖ < R * Real.sqrt lam := lt_of_lt_of_le hw (min_le_right _ _)
  -- the *model* norm of `w` is below `R`
  have hmod : (fun z : E => ‖z‖) (show E from w) < R := by
    have h1 := hbnd w
    have h2 : ‖w‖ / Real.sqrt lam < R := by
      calc ‖w‖ / Real.sqrt lam < R * Real.sqrt lam / Real.sqrt lam :=
            div_lt_div_of_pos_right hwR hsqrtlam
        _ = R := by rw [mul_comm R (Real.sqrt lam), mul_div_cancel_left₀ R hsqrtne]
    exact lt_of_le_of_lt h1 h2
  -- the elementary form of the local injectivity of `expMap p` at `w` (in the model norm)
  have hP : ¬ (∀ ε : ℝ, 0 < ε → ∃ y z : E,
      (fun t : E => ‖t‖) (y - (show E from w)) < ε ∧
      (fun t : E => ‖t‖) (z - (show E from w)) < ε ∧ y ≠ z ∧
      Submission.Geodesic.expMap cov p y = Submission.Geodesic.expMap cov p z) :=
    hRnl (show E from w) hmod
  have hlocE : ∃ ε : ℝ, 0 < ε ∧ ∀ y z : E,
      (fun t : E => ‖t‖) (y - (show E from w)) < ε →
      (fun t : E => ‖t‖) (z - (show E from w)) < ε →
      Submission.Geodesic.expMap cov p y = Submission.Geodesic.expMap cov p z → y = z := by
    by_contra hcon
    push Not at hcon
    refine hP fun ε hε => ?_
    obtain ⟨y, z, hy, hz, heq, hyz⟩ := hcon ε hε
    exact ⟨y, z, hy, hz, hyz, heq⟩
  obtain ⟨ε, hε, hinjE⟩ := hlocE
  refine ⟨{v : TangentSpace I p | ‖v‖ < ρ₁} ∩
      {v : TangentSpace I p | ‖v - w‖ < ε * Real.sqrt lam}, ?_, ?_⟩
  · refine Filter.inter_mem ((isOpen_lt continuous_norm continuous_const).mem_nhds hwρ₁) ?_
    exact (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds
      (by show ‖w - w‖ < ε * Real.sqrt lam
          rw [sub_self, norm_zero]
          exact mul_pos hε hsqrtlam)
  · intro a ha b hb hab
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    have ha2' : (fun t : E => ‖t‖) ((show E from a) - (show E from w)) < ε := by
      have h1 := hbnd (a - w)
      have h2 : ‖a - w‖ / Real.sqrt lam < ε := by
        calc ‖a - w‖ / Real.sqrt lam < (ε * Real.sqrt lam) / Real.sqrt lam :=
              div_lt_div_of_pos_right ha2 hsqrtlam
          _ = ε := by rw [mul_comm ε (Real.sqrt lam), mul_div_cancel_left₀ ε hsqrtne]
      exact lt_of_le_of_lt h1 h2
    have hb2' : (fun t : E => ‖t‖) ((show E from b) - (show E from w)) < ε := by
      have h1 := hbnd (b - w)
      have h2 : ‖b - w‖ / Real.sqrt lam < ε := by
        calc ‖b - w‖ / Real.sqrt lam < (ε * Real.sqrt lam) / Real.sqrt lam :=
              div_lt_div_of_pos_right hb2 hsqrtlam
          _ = ε := by rw [mul_comm ε (Real.sqrt lam), mul_div_cancel_left₀ ε hsqrtne]
      exact lt_of_le_of_lt h1 h2
    have heq : Submission.Geodesic.expMap cov p (show E from a)
        = Submission.Geodesic.expMap cov p (show E from b) := by
      rw [← hagree a ha1, ← hagree b hb1]
      exact hab
    exact hinjE (show E from a) (show E from b) ha2' hb2' heq

/-- **The cut-point step below the local-diffeomorphism radius.**  If `m < ρ` for the radius `ρ`
of `exists_pos_locallyInjectiveAtGExp`, then the cut-point step needs no further hypothesis: two
distinct minimising vectors of norm `m` with the same image exist. -/
theorem exists_two_minimising_of_not_injAtLeast_of_lt
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m)
    (hfail : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r)
    {ρ : ℝ} (hρ : ∀ w : TangentSpace I p, ‖w‖ < ρ → LocallyInjectiveAtGExp (I := I) hmet p w)
    (hmρ : m < ρ) :
    ∃ u v : TangentSpace I p, u ≠ v ∧
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v ∧
      ‖u‖ = m ∧ ‖v‖ = m ∧
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) = ENNReal.ofReal m :=
  exists_two_minimising_of_hloc_sphere (cov := cov) hmet htor hinj hfail
    (fun w hw => hρ w (by rw [hw]; exact hmρ))

end

end Submission.LocalDiffeo
