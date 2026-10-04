import Mathlib
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.EXT.koszulPair_eq_sKz
import Submission.Work.Diff.STE.contDiffOn_chartComp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

/-- **The chart matrix of a smooth metric is `C^∞` at every point of the chart target**, without
the `[T2Space M]` hypothesis of `Work.Diff.EXT.kz_contDiffAt_chartMatFun` (which we cannot afford
here).

The only place where `T2Space` entered the proof of `kz_contDiffAt_chartMatFun` was the smoothness
of the metric pairing of two smooth sections of the tangent bundle
(`Work.Diff.GE.smooth_onframe_pairing`); here that pairing is obtained instead from
`ContMDiffWithinAt.clm_bundle_apply₂` followed by `contMDiffWithinAt_section`, neither of which
needs `M` to be Hausdorff.  The rest of the proof is copied verbatim from
`kz_contDiffAt_chartMatFun`: the coordinate frame vectors are smooth
(`Work.Diff.EXT.contMDiffAt_frameVector`, also `T2Space`-free), and one composes the pairing with
the smooth chart inverse. -/
theorem chartMatFun_contDiffAt_of_mem_target
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless]
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.EXT.chartMatFun (I := I) g x₀) y := by
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact PartialEquiv.map_target (extChartAt I x₀) hy
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm y :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x₀).contMDiffAt
      ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hy)
  have hframe : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffAt I I.tangent ∞
        (T% (fun z : M =>
          Submission.Geodesic.frameVector (I := I) x₀ z (Work.Diff.EXT.bB (E := E) k)))
        ((extChartAt I x₀).symm y) :=
    fun k => Work.Diff.EXT.contMDiffAt_frameVector (I := I) x₀ (Work.Diff.EXT.bB (E := E) k) hp
  refine contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => ?_))
  have hpair : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun z : M => g.inner z
        (Submission.Geodesic.frameVector (I := I) x₀ z (Work.Diff.EXT.bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ z (Work.Diff.EXT.bB (E := E) j)))
      ((extChartAt I x₀).symm y) := by
    have hψ : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun m : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) m (g.inner m))
        ((extChartAt I x₀).symm y) :=
      g.contMDiff _
    have hmain : ContMDiffWithinAt I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) m
          (g.inner m
            (Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) i))
            (Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) j))))
        univ ((extChartAt I x₀).symm y) :=
      ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x)
        (E₃ := Bundle.Trivial M ℝ) (b := fun m : M => m)
        (v := fun m : M =>
          Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) i))
        (w := fun m : M =>
          Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) j))
        (ψ := fun m : M => g.inner m) (s := univ) (x := (extChartAt I x₀).symm y)
        hψ.contMDiffWithinAt (hframe i).contMDiffWithinAt (hframe j).contMDiffWithinAt
    have hsec : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞
        (fun m : M => g.inner m
          (Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) i))
          (Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) j)))
        univ ((extChartAt I x₀).symm y) := by
      have := (contMDiffWithinAt_section (IB := I) (F := ℝ) (E := Bundle.Trivial M ℝ)
        (s := fun m : M => g.inner m
          (Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) i))
          (Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) j)))
        (a := univ) (x₀ := (extChartAt I x₀).symm y) (n := ∞)).mp hmain
      simpa using this
    simpa only [contMDiffWithinAt_univ] using hsec
  have hcomp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun x : E => g.inner ((extChartAt I x₀).symm x)
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm x)
          (Work.Diff.EXT.bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm x)
          (Work.Diff.EXT.bB (E := E) j))) y :=
    hpair.comp y hsymm
  have h := contMDiffAt_iff_contDiffAt.mp hcomp
  simpa only [Work.Diff.EXT.chartMatFun] using h

/-- `Work.Diff.STE.B3.densGood` without the `[T2Space M]` hypothesis: the chart volume density is smooth and positive in the flat coordinates, i.e. on the chart target.

ROUTE: the proof of `densGood` (`Submission/Work/Diff/STE/B3/densGood.lean`) uses only
* positivity of `√det` of the Gram matrix (`Work.Diff.STE.deTurck.posDef_gmat`, `Matrix.PosDef.det_pos`, `Real.sqrt_pos`),
* smoothness of `x ↦ (Matrix.of (Work.Diff.EXT.chartMatFun g₀ (D.x₀ i) x)).det` (`Work.Diff.EXT.kz_contDiffAt_chartMatFun`, `Work.Diff.STE.B3.contDiff_det_of`, `Real.contDiffAt_sqrt`) composed with `flatToE` (`Work.Diff.STE.B3.flatToE_contDiff`).
`T2Space` is not needed for any of these. The only place `T2Space` enters the chain is
`Work.Diff.EXT.kz_contDiffAt_chartMatFun` (`Diff/EXT/koszulPair_eq_sKz.lean`), through
`Work.Diff.GE.smooth_onframe_pairing`. Redo that smoothness without `T2Space` by
`ContMDiffWithinAt.clm_bundle_apply₂`: with
`hψ : ContMDiffAt I (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))) ⊤
  (fun m : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
    (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) m (g.inner m)) x`
(from `g.contMDiff x`) and the total-space smoothness of the two fields `X`, `Y`
(`Work.Diff.EXT.contMDiffAt_frameVector` for the chart-frame fields, which needs no `T2Space`),
`ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
 (E₁ := fun x : M => TangentSpace I x) (E₂ := …) (E₃ := Bundle.Trivial M ℝ) (b := fun m => m)
 (v := X) (w := Y) (ψ := fun m => g.inner m) (s := Set.univ) hψ.contMDiffWithinAt hX hY`
followed by `contMDiffWithinAt_section` gives the `T2Space`-free smoothness of
`x ↦ g.inner x (X x) (Y x)`; then copy the rest of `kz_contDiffAt_chartMatFun` verbatim.
(`Work.Diff.STE.contDiffOn_chartComp.contMDiffOn_metricComp` in the workspace already uses exactly this `T2Space`-free route for the same pairing and can be used as a template.) -/
theorem densGood_noT2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) : D.DensGood i := by
  intro z hz
  -- The point of `M` whose flat coordinate is `z`, lying in the chart at `x₀ i`.
  have hsymm : (extChartAt I (D.x₀ i)).symm (flatToE (I := I) (D.x₀ i) z)
      ∈ (chartAt H (D.x₀ i)).source := by
    rw [← extChartAt_source (I := I) (D.x₀ i)]
    exact PartialEquiv.map_target (extChartAt I (D.x₀ i)) hz
  -- The chart matrix is the Gram matrix of the coordinate frame, hence positive definite.
  have hpd : (Matrix.of (Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ i)
      ((extChartAt I (D.x₀ i)).symm (flatToE (I := I) (D.x₀ i) z)))).PosDef :=
    Work.Diff.STE.deTurck.posDef_gmat (I := I) g₀ (D.x₀ i) hsymm
  have hdetpos : 0 < (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
      (flatToE (I := I) (D.x₀ i) z))).det := by
    have := hpd.det_pos
    rwa [show Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ i)
          ((extChartAt I (D.x₀ i)).symm (flatToE (I := I) (D.x₀ i) z))
        = Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (flatToE (I := I) (D.x₀ i) z) from rfl] at this
  refine ⟨?_, ?_⟩
  · -- positivity of the density
    simpa only [Work.Diff.STE.B3Data.dens] using Real.sqrt_pos.mpr hdetpos
  · -- smoothness of the density in the flat coordinate
    have hflat : ContDiffAt ℝ (⊤ : ℕ∞) (flatToE (I := I) (D.x₀ i)) z :=
      (flatToE_contDiff (I := I) (x₀ := D.x₀ i)).contDiffAt
    have hchart : ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i))
        (flatToE (I := I) (D.x₀ i) z) :=
      chartMatFun_contDiffAt_of_mem_target (I := I) g₀ (D.x₀ i) hz
    have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z => Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (flatToE (I := I) (D.x₀ i) z)) z :=
      hchart.comp z hflat
    have hdet : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z => (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (flatToE (I := I) (D.x₀ i) z))).det) z :=
      (contDiff_det_of (n := Module.finrank ℝ E)).contDiffAt.comp z hcomp
    have hsqrt : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z => Real.sqrt ((Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (flatToE (I := I) (D.x₀ i) z))).det)) z :=
      (Real.contDiffAt_sqrt (ne_of_gt hdetpos)).comp z hdet
    exact hsqrt

end Work.Diff.STE.B3
