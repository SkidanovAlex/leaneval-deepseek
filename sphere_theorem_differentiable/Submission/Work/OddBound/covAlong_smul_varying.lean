import Mathlib
import Submission.Work.OddBound.Defs

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec
open Submission.JacobiCoords Submission.ChartCurv Submission.BonnetMyers Submission.SecondVariation

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The Leibniz rule for `covAlong` with a *varying* real coefficient.**  For a field `X` smooth
along `γ` at `t` and a scalar function `f` smooth on a *fixed open neighbourhood* `U ∋ t`,
`∇(f X) = f' X + f ∇X` at `t`.  (The hypothesis is `ContDiffOn ℝ ∞ f U` on an open `U`, not
`ContDiffAt ℝ ∞ f t`: for `n = ∞` a `ContDiffAt` statement only gives order-by-order shrinking
neighbourhoods, which is not enough to make the product `f · (chartCoords X)` `ContDiffOn` on a fixed
neighbourhood.)  Suggested route: `Submission.JacobiGlobal.covAlong_eq_chart` with the pointwise
linearity `chartCoords_smul`, `chrB_smul_snd` (unconditional in the second slot), the product rule
for `deriv`, and `frameVector_add`/`frameVector_smul` — the same chart-level route as
`Submission.IndexScale.covAlong_smul`. -/
theorem covAlong_smul_varying (htor : cov.torsion = 0)
    {γ : ℝ → M} {X : (t : ℝ) → TangentSpace I (γ t)} {f : ℝ → ℝ} {U : Set ℝ} {t : ℝ}
    (hU : IsOpen U) (htU : t ∈ U)
    (hX : SmoothAlongAt (I := I) γ X t)
    (hf : ContDiffOn ℝ ∞ f U)
    (hfX : SmoothAlongAt (I := I) γ (fun s => f s • X s) t) :
    covAlong cov (fun s : ℝ => f s • X s) t = deriv f t • X t + f t • covAlong cov X t := by
  obtain ⟨U₁, hU₁open, htU₁, hsrc₁, hcd₁⟩ := hX
  -- `chartCoords` is pointwise linear in the field
  have hcoords : (chartCoords (I := I) (γ t) γ fun s : ℝ => f s • X s)
      = fun s : ℝ => f s • chartCoords (I := I) (γ t) γ X s := by
    funext s
    exact map_smul ((trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt ℝ (γ s))
      (f s) (X s)
  -- differentiability of the two factors at `t`, from the `ContDiffOn` hypotheses on open sets
  have hdf : DifferentiableAt ℝ f t :=
    (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds htU)
  have hYd : DifferentiableAt ℝ (chartCoords (I := I) (γ t) γ X) t :=
    (hcd₁.differentiableOn (by simp)).differentiableAt (hU₁open.mem_nhds htU₁)
  -- product rule for `deriv`
  have hprod : deriv (fun s : ℝ => f s • chartCoords (I := I) (γ t) γ X s) t
      = deriv f t • chartCoords (I := I) (γ t) γ X t
        + f t • deriv (chartCoords (I := I) (γ t) γ X) t := by
    have h : HasDerivAt (fun s : ℝ => f s • chartCoords (I := I) (γ t) γ X s)
        (f t • deriv (chartCoords (I := I) (γ t) γ X) t
          + deriv f t • chartCoords (I := I) (γ t) γ X t) t :=
      hdf.hasDerivAt.smul hYd.hasDerivAt
    rw [h.deriv, add_comm]
  -- `chartCoords` of a tangent vector is the coordinate vector of `frameVector`
  have hXval : X t = frameVector (I := I) (γ t) (γ t) (chartCoords (I := I) (γ t) γ X t) :=
    (frameVector_chartCoords (I := I) (mem_chart_source H (γ t))).symm
  -- unfold `covAlong` (a definition in normal form) and use the chart formula `DtQ` at `s = 0`
  rw [covAlong, covAlong, hcoords]
  simp only [DtQ, covDsP, fam, famP, zero_smul, add_zero]
  -- the remaining identity is the linearity of `frameVector`, `chrB` and `deriv` in the field
  rw [hprod, hXval, chrB_smul_snd, add_assoc, ← smul_add, frameVector_add,
    frameVector_smul, frameVector_smul]

end Work.OddBound
