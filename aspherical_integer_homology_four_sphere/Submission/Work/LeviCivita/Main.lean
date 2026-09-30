/-
# Area LC: the Levi-Civita connection, assembled

This is the assembly file of area `Submission/Work/LeviCivita/`.  It proves the smoothness of
`lcConn` and re-exports the interface.

## The theorem

    Work.LeviCivita.contMDiffCovariantDerivative_lcConn :
      CovariantDerivative.ContMDiffCovariantDerivative (lcConn (I := I) (M := M)) ∞

(registered as a typeclass instance).  Mathlib has `leviCivitaConnection` together with
torsion-freeness and metric compatibility, but not its smoothness; this is that gap filled.

The proof: for a `C^∞` section `σ`, the section `x ↦ ⟨x, lcConn σ x⟩` of `Hom(TM, TM)` is `C^∞`
by `Trivialization.contMDiffWithinAt_section`, which reduces to the smoothness of the coordinate
representative `x ↦ inCoordinates E (TangentSpace I) E (TangentSpace I) x₀ x x₀ x (lcConn σ x)`.
That representative is eventually equal (near `x₀`) to the explicitly constructed smooth function
`chartLCcoords x₀ σ` (`Work.LeviCivita.chartLCcoords_eventuallyEq`), by the definition of
`chartLCcoords = chartLCcoords` as "raise the Koszul pairing `chartPairing` with the inverse chart
metric" and the positive definiteness of the chart metric on the chart (`chartGram_posDef`).
-/
import Submission.Work.LeviCivita.Defs
import Submission.Work.LeviCivita.ChartMetric
import Submission.Work.LeviCivita.Koszul
import Submission.Work.LeviCivita.Smooth
import Submission.Work.LeviCivita.chartLCcoords_eventuallyEq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic

namespace Work.LeviCivita

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

/-- The hom-bundle section of `lcConn σ` is `C^∞` at every point, for `σ` a `C^∞` section. -/
lemma contMDiffWithinAt_lcConn_homSection {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I I.tangent ∞ (T% σ)) (x₀ : M) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M ↦ (⟨x, lcConn (I := I) (M := M) σ x⟩ :
        TotalSpace (E →L[ℝ] E) (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)))
      Set.univ x₀ := by
  refine (Trivialization.contMDiffWithinAt_section (n := ∞) (IB := I) (F := E →L[ℝ] E)
    (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
    (s := fun x : M ↦ lcConn (I := I) (M := M) σ x) Set.univ (x₀ := x₀)
    (e := trivializationAt (E →L[ℝ] E)
      (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x₀) ?_).mpr ?_
  · rw [hom_trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet]
    exact ⟨mem_chart_source H x₀, mem_chart_source H x₀⟩
  · rw [contMDiffWithinAt_univ]
    refine (contMDiffAt_chartLCcoords (I := I) x₀ hσ x₀ (mem_chart_source H x₀)).congr_of_eventuallyEq ?_
    filter_upwards [chartLCcoords_eventuallyEq (I := I) x₀ hσ] with x hx
    rw [hx, hom_trivializationAt_apply]

/-- **The Levi-Civita connection is a smooth covariant derivative.** -/
theorem contMDiffCovariantDerivative_lcConn :
    CovariantDerivative.ContMDiffCovariantDerivative (lcConn (I := I) (M := M)) ∞ := by
  refine ⟨{ contMDiff := ?_ }⟩
  intro σ hσ x _
  have hσ' : ContMDiff I I.tangent ∞ (T% σ) := by
    have h1 : ContMDiffOn I I.tangent (∞ + 1) (T% σ) Set.univ := hσ
    rw [show (∞ + 1 : ℕ∞ω) = ∞ from by simp] at h1
    rwa [contMDiffOn_univ] at h1
  exact contMDiffWithinAt_lcConn_homSection (I := I) hσ' x

attribute [instance] contMDiffCovariantDerivative_lcConn

end

end Work.LeviCivita
