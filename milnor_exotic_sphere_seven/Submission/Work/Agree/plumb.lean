import Mathlib
import Submission.Work.Agree.Basic
import Submission.Work.Agree.PlumbDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-- Pulling back a reindexed real bundle is the reindexing of the pullback. -/
theorem bundleComap_reindex {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι ι' : Type}
    (Z : RealBundle B F ι) (σ : ι' → ι)
    (hσ : ∀ x : B, ∃ i, x ∈ Z.baseSet (σ i)) (f : C(B', B)) :
    Work.Thom.bundleComap (Z.reindex σ hσ) f
      = reindexCore (Work.Thom.bundleComap Z f) σ (fun x => hσ (f x)) := rfl

/-- Complexifying a reindexed real bundle is the reindexing of the complexification. -/
theorem complexificationCore_reindexCore {B : Type} [TopologicalSpace B] {k : ℕ} {ι ι' : Type}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (σ : ι' → ι)
    (hσ : ∀ x : B, ∃ i, x ∈ Z.baseSet (σ i)) :
    Work.Thom.complexificationCore (reindexCore Z σ hσ)
      = reindexCore (Work.Thom.complexificationCore Z) σ hσ := rfl

/-- Changing the fibre commutes with the pullback. -/
theorem mapFibre_bundleComap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {F F' : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {ι : Type}
    (e : F ≃L[ℝ] F') (Z : RealBundle B F ι) (f : C(B', B)) :
    RealBundle.mapFibre e (Work.Thom.bundleComap Z f)
      = Work.Thom.bundleComap (RealBundle.mapFibre e Z) f := rfl

/-- **Plumbing**: for any compact smooth charted space `X` over `ℝ⁸` and any continuous map
`f : B → X`, the pullback of the canonical complexified tangent bundle presentation
`Work.Thom.complexifiedTangentBundleFinite` is the complexification of the (fibre-changed) pullback
of the tangent bundle.  The finite-chart-cover reindexing is dropped and the change of fibre is
moved outside. -/
theorem nonempty_bundleIso_plumb {X : Type} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 8)) X] [IsManifold Work.Milnor.mE8 1 X]
    [CompactSpace X] {B : Type} [TopologicalSpace B] (f : C(B, X)) :
    Nonempty (Work.Thom.BundleIso
      (Work.Thom.bundleComap (Work.Thom.complexifiedTangentBundleFinite Work.Milnor.mE8 X) f)
      (Work.Thom.complexificationCore
        (RealBundle.mapFibre (Work.Thom.modelLinearEquiv (E := EuclideanSpace ℝ (Fin 8)))
          (Work.Thom.bundleComap
            (Work.TangentClasses.tangentBundle Work.Milnor.mE8 X) f)))) := by
  unfold Work.Thom.complexifiedTangentBundleFinite
  rw [← Work.Thom.complexificationCore_bundleComap]
  rw [bundleComap_reindex]
  rw [complexificationCore_reindexCore]
  rw [mapFibre_bundleComap]
  exact nonempty_bundleIso_reindexCore_self _ _ _

theorem plumb (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F) : Work.Agree.Plumb F hF := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 8))
      (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) :=
    Work.Milnor.cappedChartedSpace (Work.Milnor.cappedDatum F hF)
  letI : IsManifold Work.Milnor.mE8 1 (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) :=
    (Work.Milnor.capped_isManifold (Work.Milnor.cappedDatum F hF)).of_le (by simp)
  letI : CompactSpace (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) :=
    Work.Milnor.isCompact_capped F hF
  exact nonempty_bundleIso_plumb (Work.Agree.incl F hF)

end

end Work.Agree
