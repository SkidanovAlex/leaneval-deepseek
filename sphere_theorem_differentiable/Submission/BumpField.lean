import Submission.JacobiGlobal

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.JacobiCoords
open Submission.ChartCoordsTrans
open Submission.JacobiGlobal
open Submission.BonnetMyers
open Submission.Geodesic

/-!
# The bump field of the shortening argument

The perturbation `W` of the shortening argument for the global `σ ≤ κ` is a smoothly cut-off
constant field: in the chart at a point `z`, its coordinates are `χ • c` for a `C^∞` bump `χ` and a
constant vector `c`.  This module records its elementary properties (`bumpField_apply`,
`smoothAlongAt_bumpField`, `covAlong_bumpField_eq_chart`), which are the per-piece clauses needed to
feed it to `IndexIntrinsic3.IsBilPiece` together with its covariant derivative
`Submission.JacobiGlobal.covAlong`.
-/

namespace Submission.BumpField

noncomputable section

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

/-- **The bump field**: the field along `γ` whose coordinates in the chart at `z` are `χ • c`. -/
noncomputable def bumpField (z : M) (γ : ℝ → M) (χ : ℝ → ℝ) (c : E) :
    (t : ℝ) → TangentSpace I (γ t) :=
  fun t => frameVector (I := I) z (γ t) (χ t • c)

lemma bumpField_apply (z : M) (γ : ℝ → M) (χ : ℝ → ℝ) (c : E) (t : ℝ) :
    bumpField (I := I) z γ χ c t = χ t • frameVector (I := I) z (γ t) c :=
  frameVector_smul z (γ t) (χ t) c

/-- The bump field is smooth along the curve, in the form used by `covAlong`. -/
theorem smoothAlongAt_bumpField {z : M} {γ : ℝ → M} {χ : ℝ → ℝ} {c : E} {U : Set ℝ} {t : ℝ}
    (hU : IsOpen U) (htU : t ∈ U) (hχ : ContDiffOn ℝ ∞ χ U)
    (hγU : ContMDiffOn 𝓘(ℝ) I ∞ γ U)
    (hsrc : ∀ s ∈ U, γ s ∈ (chartAt H z).source)
    (hsrc' : ∀ s ∈ U, γ s ∈ (chartAt H (γ t)).source) :
    SmoothAlongAt (I := I) γ (bumpField (I := I) z γ χ c) t :=
  smoothAlongAt_frameVector (I := I) hU htU
    (hχ.smul_const c) hγU hsrc hsrc'

/-- The chart formula for the covariant derivative of the bump field. -/
theorem covAlong_bumpField_eq_chart (htor : cov.torsion = 0)
    {z : M} {γ : ℝ → M} {χ : ℝ → ℝ} {c : E} {t : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : curveVelocity (I := I) γ t ≠ 0)
    (hV : SmoothAlongAt (I := I) γ (bumpField (I := I) z γ χ c) t)
    {x₀ : M} {u w y y' : ℝ → E}
    (hsrc : γ t ∈ (chartAt H x₀).source)
    (hsrcEv : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H x₀).source)
    (huTgt : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target)
    (hγeq : γ =ᶠ[𝓝 t] fun s => (extChartAt I x₀).symm (u s))
    (hu : ∀ᶠ s in 𝓝 t, HasDerivAt u (w s) s)
    (hy : ∀ᶠ s in 𝓝 t, frameVector (I := I) x₀ (γ s) (y s) = bumpField (I := I) z γ χ c s)
    (hy' : ∀ᶠ s in 𝓝 t, HasDerivAt y (y' s) s) :
    covAlong cov (bumpField (I := I) z γ χ c) t
      = frameVector (I := I) x₀ (γ t) (DtQ cov x₀ u y w y' t) :=
  covAlong_eq_chart (cov := cov) htor hγ hne hV hsrc hsrcEv huTgt hγeq hu hy hy'

end

end Submission.BumpField
