import Submission.SyngeInput
import Submission.GExpPieceData

/-!
# The geodesic equation of the intrinsic family, for an arbitrary geodesic

`Submission.GExpPieceData.hasDerivAt_psiW_GExp` produces the hypothesis `hgeoB` of
`Submission.EnergyRay.energy_second_deriv_piece_scaled` (the chart geodesic equation, in the `psiW`
form) for a `GExp`-ray.  This module proves the same statement for an arbitrary `C^∞` geodesic given
on an open set — the input needed to run the per-piece second-variation machinery of
`Submission.EnergyRay` / `Submission.EnergyCover` along a general geodesic (a closed geodesic, in the
application). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.ChartConnection
open Submission.Jacobi
open Submission.GeoChartCurve
open Submission.ChartCurv
open Submission.Rauch
open Submission.JacobiTensor
open Submission.RauchGlobal
open Submission.GExpFlow
open Submission.JacobiCoords
open Submission.IntrinsicVariation
open Submission.SecondVarGlobal

namespace Submission.EnergyGeo

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
variable {z : M} {Z : Set M}

/-- **The geodesic equation `hgeoB` of the intrinsic family, for an arbitrary geodesic.**  This is
`Submission.GExpPieceData.hasDerivAt_psiW_GExp` with the `GExp`-ray replaced by a `C^∞` geodesic
given on an open set. -/
theorem hasDerivAt_psiW_geodesic (D : ChartFlowData (cov := cov) (I := I) z Z)
    {γ : ℝ → M} {u : ℝ → E} {a b ε : ℝ} (hε : 0 < ε) {V : Set ℝ} (hV : IsOpen V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V)
    (hgeo : ∀ t ∈ V, IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t ∈ V, curveVelocity (I := I) γ t ≠ 0)
    (hVsub : ∀ t ∈ Icc (a - ε) (b + ε), Ioo (t - 1) (t + 1) ⊆ V)
    (hZ : ∀ t ∈ Icc (a - ε) (b + ε), γ t ∈ Z)
    (hsrc : ∀ t ∈ Icc (a - ε) (b + ε), γ t ∈ (chartAt H z).source) :
    ∀ t ∈ Icc a b, HasDerivAt
      (fun t' : ℝ => psiW (cov := cov) D (chartCoord (I := I) z γ) u 0 t')
      (chartGeodesicVectorField cov z (chartCoord (I := I) z γ t,
        psiW (cov := cov) D (chartCoord (I := I) z γ) u 0 t)) t := by
  intro t ht
  have htI : t ∈ Ioo (a - ε) (b + ε) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hW' : (fun t' : ℝ => psiW (cov := cov) D (chartCoord (I := I) z γ) u 0 t')
      =ᶠ[𝓝 t] (fun t' : ℝ => deriv (chartCoord (I := I) z γ) t') := by
    refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htI) ?_
    intro t' ht'
    refine psiW_zero (cov := cov) D (x := chartCoord (I := I) z γ) (u := u) (t := t')
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds
        (show t' ∈ Ioo (a - ε) (b + ε) from ⟨ht'.1, ht'.2⟩)) ?_)
    intro s hs
    exact ⟨γ s, hZ s ⟨hs.1.le, hs.2.le⟩, rfl⟩
  have hWt : psiW (cov := cov) D (chartCoord (I := I) z γ) u 0 t
      = deriv (chartCoord (I := I) z γ) t := hW'.eq_of_nhds
  rw [hWt]
  have hVt : t ∈ V :=
    hVsub t ⟨by linarith [ht.1], by linarith [ht.2]⟩ ⟨by linarith, by linarith⟩
  refine ((Submission.HolDet.hasDerivAt_chartODE_of_isGeodesic (cov := cov) (x₀ := z) hV hVt hγ
    (hsrc t ⟨by linarith [ht.1], by linarith [ht.2]⟩) hgeo hne).2).congr_of_eventuallyEq hW'

end

end Submission.EnergyGeo
