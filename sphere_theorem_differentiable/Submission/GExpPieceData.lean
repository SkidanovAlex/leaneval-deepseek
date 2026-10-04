import Submission.JacobiCover

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

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


/-!
# Per-piece data of the intrinsic variation along a `GExp`-ray

Two of the hypotheses of `Submission.SecondVarGlobal.energy_second_deriv_piece` are produced here for
the case that the base curve is a `GExp`-ray (which is what `ConjCut.CutConjInequality` needs):

* `contDiffOn_chartCoord_GExp` — the chart coordinates of the ray are `C^∞` on any interval on which
  the ray stays in the chart source (the `hx` hypothesis);
* `hasDerivAt_psiW_GExp` — the chart **geodesic equation** in the form `hgeoB` expects
  (`HasDerivAt (fun t' ↦ psiW D x u 0 t') (chartGeodesicVectorField cov z (x t, psiW D x u 0 t)) t`),
  proved by rewriting `psiW D x u 0` to `deriv x` (`SecondVarGlobal.psiW_zero`, which needs the phase
  membership on a *neighbourhood* of each `t`, hence the radii `ε > 0` in the hypotheses) and applying
  `GeoChartCurve.hasDerivAt_deriv_chartCurve_GExp`.

Note the shape of the hypotheses of `hasDerivAt_psiW_GExp`: the compact set `Z` of the flow datum must
contain `γ` on the *larger* interval `Icc (a-ε) (b+ε)`, and `γ` must stay in the chart source there
too.  This is what the *rooms* of `Submission.JacobiCover.exists_partition_jacobiCoords` provide
(Roadmap §100.12).
-/

namespace Submission.GExpPieceData

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
variable {z : M} {Z : Set M}
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The chart coordinates of a `GExp`-ray are `C^∞`** wherever the ray stays in the chart source. -/
theorem contDiffOn_chartCoord_GExp (hmet : IsMetricCompatible cov) {z : M} {p : M}
    {ξ : TangentSpace I p} (hξ : ξ ≠ 0) {A B : ℝ}
    (hsrc : ∀ t ∈ Icc A B, GExp (cov := cov) hmet p (t • ξ) ∈ (chartAt H z).source) :
    ContDiffOn ℝ ∞ (chartCoord (I := I) z (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)))
      (Icc A B) :=
  (contDiffOn_chartCoord (I := I) (z₀ := z)
    ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hξ).mono (Set.subset_univ _))
    hsrc).mono (Subset.refl _)

/-- **The geodesic equation `hgeoB` of the intrinsic family, for a `GExp`-ray.** -/
theorem hasDerivAt_psiW_GExp (hmet : IsMetricCompatible cov)
    (D : ChartFlowData (cov := cov) (I := I) z Z) {p : M} {ξ : TangentSpace I p} (hξ : ξ ≠ 0)
    {u : ℝ → E} {a b ε : ℝ} (hε : 0 < ε)
    (hZ : ∀ t ∈ Icc (a - ε) (b + ε), GExp (cov := cov) hmet p (t • ξ) ∈ Z)
    (hsrc : ∀ t ∈ Icc (a - ε) (b + ε),
      GExp (cov := cov) hmet p (t • ξ) ∈ (chartAt H z).source) :
    ∀ t ∈ Icc a b, HasDerivAt
      (fun t' : ℝ => psiW (cov := cov) D
        (chartCoord (I := I) z (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ))) u 0 t')
      (chartGeodesicVectorField cov z
        (chartCoord (I := I) z (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t,
          psiW (cov := cov) D
            (chartCoord (I := I) z (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ))) u 0 t)) t := by
  intro t ht
  -- `psiW 0 = deriv (chartCoord …)` near `t`
  have hW' : (fun t' : ℝ => psiW (cov := cov) D
        (chartCoord (I := I) z (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ))) u 0 t')
      =ᶠ[𝓝 t] (fun t' : ℝ => deriv (chartCoord (I := I) z
        (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ))) t') := by
    refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds
      (show t ∈ Ioo (a - ε) (b + ε) from ⟨by linarith [ht.1], by linarith [ht.2]⟩)) ?_
    intro t' ht'
    refine psiW_zero (cov := cov) D (x := chartCoord (I := I) z
      (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ))) (u := u) (t := t')
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds
        (show t' ∈ Ioo (a - ε) (b + ε) from ⟨by linarith [ht'.1], by linarith [ht'.2]⟩)) ?_)
    intro s hs
    exact ⟨GExp (cov := cov) hmet p (s • ξ),
      hZ s ⟨by linarith [hs.1], by linarith [hs.2]⟩, rfl⟩
  have hWt : psiW (cov := cov) D
      (chartCoord (I := I) z (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ))) u 0 t
      = deriv (chartCoord (I := I) z (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ))) t :=
    hW'.eq_of_nhds
  rw [hWt]
  refine (hasDerivAt_deriv_chartCurve_GExp (cov := cov) hmet z hξ t
    (hsrc t ⟨by linarith [ht.1], by linarith [ht.2]⟩)).congr_of_eventuallyEq hW'

/-- **The phase condition from a bound on the field's coordinates.**  If `q ∈ Z` and the scaled
coordinate velocity is bounded by `1`, then the corresponding phase is an element of `chartData z Z`
— which is the hypothesis `hphaseC` of `energy_second_deriv_piece` (recall
`chartData z Z = ((extChartAt I z) '' Z) ×ˢ closedBall 0 1`). -/
theorem mem_chartData_phase (D : ChartFlowData (cov := cov) (I := I) z Z) {q : M} {u : E} {σ : ℝ}
    (hq : q ∈ Z) (hσ : |σ| ≤ 1) (hu : flowScale D * ‖u‖ ≤ 1) :
    ((extChartAt I z) q, flowScale D • (σ • u)) ∈ chartData (I := I) z Z := by
  refine ⟨⟨q, hq, rfl⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (flowScale_pos (cov := cov) (I := I) D)]
  rw [norm_smul, Real.norm_eq_abs]
  nlinarith [flowScale_pos (cov := cov) (I := I) D, abs_nonneg σ, norm_nonneg u, hu,
    abs_le.mp hσ |>.1, abs_le.mp hσ |>.2]

/-- The same, in the form needed when `σ` ranges over `Icc (-1) 1`. -/
theorem mem_chartData_phase' (D : ChartFlowData (cov := cov) (I := I) z Z) {q : M} {u : ℝ → E}
    {σ t : ℝ} (hq : q ∈ Z) (hσ : σ ∈ Icc (-1 : ℝ) 1) (hu : flowScale D * ‖u t‖ ≤ 1) :
    ((extChartAt I z) q, flowScale D • (σ • u t)) ∈ chartData (I := I) z Z :=
  mem_chartData_phase (cov := cov) D hq (abs_le.mpr ⟨hσ.1, hσ.2⟩) hu

end

end Submission.GExpPieceData
