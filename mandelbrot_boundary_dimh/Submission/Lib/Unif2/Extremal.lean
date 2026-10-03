import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.Holomorphic
import Mathlib.Analysis.Complex.Schwarz

/-!
# The extremal-derivative approach to uniformization (first steps)

An alternative route to the uniformization theorem avoids the Green function: let

`extremalFamily z₀ = {f : X → ℂ | f holomorphic on X, ‖f ·‖ ≤ 1, f z₀ = 0}`

and let `extremalDerivative z₀` be the supremum of `‖deriv (f ∘ (chartAt ℂ z₀).symm) (chartAt ℂ z₀ z₀)‖`
over this family.  The classical argument (Ahlfors): the supremum is finite (Schwarz), it is
attained by a holomorphic function obtained from a normal-family compactness argument, and the
extremal function is a biholomorphism `X → 𝔻` (the "square-root trick", which uses only that `X`
is simply connected in the form of the global logarithm theorem
`Submission.HolomorphicOnX.exists_log_of_ne_zero`).  If on the other hand the family is trivial
(every bounded holomorphic function on `X` is constant) then `X` should be biholomorphic to `ℂ`.

This module contains the first, elementary step: the **Schwarz bound** on the derivative, which
shows that `extremalDerivative z₀` is finite.  This is the uniform bound needed by the
compactness (Montel) argument.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Schwarz bound.**  A holomorphic function on `X` with values in the closed unit disc and
vanishing at `z₀` has derivative at `z₀` (measured in the chart at `z₀`) bounded by `1/ρ`, where
`ρ` is the radius of a chart disc around `z₀`. -/
theorem norm_deriv_le_of_bounded_holomorphicOnX {z₀ : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall (chartAt ℂ z₀ z₀) ρ ⊆ (chartAt ℂ z₀).target)
    {f : X → ℂ} (hf : HolomorphicOnX f univ) (hb : ∀ x : X, ‖f x‖ ≤ 1) (hz : f z₀ = 0) :
    ‖deriv (f ∘ (chartAt ℂ z₀).symm) (chartAt ℂ z₀ z₀)‖ ≤ 1 / ρ := by
  have hz₀src : z₀ ∈ (chartAt ℂ z₀).source := mem_chart_source ℂ z₀
  have hsymm : (chartAt ℂ z₀).symm (chartAt ℂ z₀ z₀) = z₀ := (chartAt ℂ z₀).left_inv hz₀src
  have hdiff : DifferentiableOn ℂ (f ∘ (chartAt ℂ z₀).symm)
      (Metric.ball (chartAt ℂ z₀ z₀) ρ) := by
    intro y hy
    have hytgt : y ∈ (chartAt ℂ z₀).target :=
      hsub (Metric.ball_subset_closedBall hy)
    have hysrc : (chartAt ℂ z₀).symm y ∈ (chartAt ℂ z₀).source :=
      (chartAt ℂ z₀).map_target hytgt
    have han : AnalyticAt ℂ (f ∘ (chartAt ℂ z₀).symm)
        ((chartAt ℂ z₀) ((chartAt ℂ z₀).symm y)) :=
      (HolomorphicOnXAt_iff_chart (f := f) (x := (chartAt ℂ z₀).symm y) (y := z₀) hysrc).mp
        (hf _ (mem_univ _))
    rw [(chartAt ℂ z₀).right_inv hytgt] at han
    exact han.differentiableWithinAt
  have hmaps : MapsTo (f ∘ (chartAt ℂ z₀).symm) (Metric.ball (chartAt ℂ z₀ z₀) ρ)
      (Metric.closedBall ((f ∘ (chartAt ℂ z₀).symm) (chartAt ℂ z₀ z₀)) 1) := by
    intro y hy
    have hval : (f ∘ (chartAt ℂ z₀).symm) (chartAt ℂ z₀ z₀) = 0 := by
      simp only [Function.comp_apply, hsymm]
      exact hz
    rw [Metric.mem_closedBall, dist_eq_norm, hval, sub_zero]
    exact hb _
  exact Complex.norm_deriv_le_div_of_mapsTo_ball hdiff hmaps hρ

/-- The **extremal family**: bounded holomorphic functions on `X` vanishing at `z₀`. -/
def extremalFamily (z₀ : X) : Set (X → ℂ) :=
  {f | HolomorphicOnX f univ ∧ (∀ x : X, ‖f x‖ ≤ 1) ∧ f z₀ = 0}

theorem extremalFamily_nonempty (z₀ : X) : (extremalFamily z₀).Nonempty :=
  ⟨fun _ => 0, fun x _ => analyticAt_const, (fun x => by simp), by simp⟩

theorem zero_mem_extremalFamily (z₀ : X) : (fun _ : X => 0) ∈ extremalFamily z₀ :=
  ⟨fun x _ => analyticAt_const, (fun x => by simp), rfl⟩

/-- The set of derivative norms of the members of the extremal family, measured in the chart at
`z₀`. -/
def extremalDerivativeSet (z₀ : X) : Set ℝ :=
  (fun f : X → ℂ => ‖deriv (f ∘ (chartAt ℂ z₀).symm) (chartAt ℂ z₀ z₀)‖) '' extremalFamily z₀

/-- The **extremal derivative**: the supremum of `‖f'(z₀)‖` over the extremal family. -/
def extremalDerivative (z₀ : X) : ℝ := sSup (extremalDerivativeSet z₀)

/-- The extremal derivative is bounded by the Schwarz bound, hence finite. -/
theorem extremalDerivative_le {z₀ : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall (chartAt ℂ z₀ z₀) ρ ⊆ (chartAt ℂ z₀).target) :
    extremalDerivative z₀ ≤ 1 / ρ := by
  refine csSup_le ((extremalFamily_nonempty z₀).image _) ?_
  rintro y ⟨f, hf, rfl⟩
  exact norm_deriv_le_of_bounded_holomorphicOnX hρ hsub hf.1 hf.2.1 hf.2.2

theorem extremalDerivative_bddAbove {z₀ : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall (chartAt ℂ z₀ z₀) ρ ⊆ (chartAt ℂ z₀).target) :
    BddAbove (extremalDerivativeSet z₀) :=
  ⟨1 / ρ, by
    rintro y ⟨f, hf, rfl⟩
    exact norm_deriv_le_of_bounded_holomorphicOnX hρ hsub hf.1 hf.2.1 hf.2.2⟩

theorem extremalDerivative_nonneg {z₀ : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall (chartAt ℂ z₀ z₀) ρ ⊆ (chartAt ℂ z₀).target) :
    0 ≤ extremalDerivative z₀ := by
  have hmem : (0 : ℝ) ∈ extremalDerivativeSet z₀ := by
    refine ⟨fun _ : X => 0, zero_mem_extremalFamily z₀, ?_⟩
    change ‖deriv ((fun _ : X => 0) ∘ (chartAt ℂ z₀).symm) (chartAt ℂ z₀ z₀)‖ = 0
    have h1 : ((fun _ : X => 0) ∘ (chartAt ℂ z₀).symm) = fun _ : ℂ => (0 : ℂ) := by
      funext w; rfl
    rw [h1, deriv_const, norm_zero]
  exact le_csSup (extremalDerivative_bddAbove hρ hsub) hmem

end Submission
