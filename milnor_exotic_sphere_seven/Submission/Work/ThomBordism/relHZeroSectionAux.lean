import Mathlib
import Submission.Work.TangentClasses.Bundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Auxiliary definitions for the injectivity of the localisation at the zero section
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Bundle
open scoped Manifold Topology

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type} {k : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin 8)) B]

/-- **The trivialising chart at a point of the total space**. -/
def bundleChartAt (Z : VectorBundleCore ℝ B F ι)
    (Ψ : EuclideanSpace ℝ (Fin (k + 8)) ≃ₜ (EuclideanSpace ℝ (Fin 8) × F)) (p : Z.TotalSpace) :
    OpenPartialHomeomorph Z.TotalSpace (EuclideanSpace ℝ (Fin (k + 8))) :=
  (Z.localTrivAt p.proj).toOpenPartialHomeomorph.trans
    (((chartAt (EuclideanSpace ℝ (Fin 8)) p.proj).prod (OpenPartialHomeomorph.refl F)).trans
      (Ψ.symm).toOpenPartialHomeomorph)

/-- **The trivialising atlas of the total space of a real bundle** over a base charted on `ℝ⁸`. -/
@[instance_reducible] def bundleChartedSpace (Z : VectorBundleCore ℝ B F ι)
    (Ψ : EuclideanSpace ℝ (Fin (k + 8)) ≃ₜ (EuclideanSpace ℝ (Fin 8) × F)) :
    ChartedSpace (EuclideanSpace ℝ (Fin (k + 8))) Z.TotalSpace where
  atlas := Set.range (bundleChartAt Z Ψ)
  chartAt := bundleChartAt Z Ψ
  mem_chart_source p := by
    rw [bundleChartAt, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff]
    constructor
    · exact (Z.localTrivAt p.proj).mem_source.mpr (Z.mem_baseSet_at p.proj)
    · simp only [OpenPartialHomeomorph.trans_source, Set.mem_preimage, Set.mem_inter_iff,
        Bundle.Trivialization.coe_coe, Z.localTrivAt_apply, OpenPartialHomeomorph.prod_source,
        Set.mem_prod, Homeomorph.toOpenPartialHomeomorph_source, Set.mem_univ, and_true]
      exact ⟨mem_chart_source (EuclideanSpace ℝ (Fin 8)) p.proj, Set.mem_univ _⟩
  chart_mem_atlas p := Set.mem_range_self p

/-- The chart of `bundleChartedSpace` is `bundleChartAt`. -/
theorem bundleChartedSpace_chartAt (Z : VectorBundleCore ℝ B F ι)
    (Ψ : EuclideanSpace ℝ (Fin (k + 8)) ≃ₜ (EuclideanSpace ℝ (Fin 8) × F)) (p : Z.TotalSpace) :
    @ChartedSpace.chartAt (EuclideanSpace ℝ (Fin (k + 8)))
      (inferInstance : TopologicalSpace (EuclideanSpace ℝ (Fin (k + 8)))) Z.TotalSpace
      (inferInstance : TopologicalSpace Z.TotalSpace)
      (bundleChartedSpace Z Ψ) p = bundleChartAt Z Ψ p := rfl

/-- The linear subspace of the model on which the zero section lives. -/
def modelSubspace (Ψ : EuclideanSpace ℝ (Fin (k + 8)) ≃ₜ (EuclideanSpace ℝ (Fin 8) × F)) :
    Set (EuclideanSpace ℝ (Fin (k + 8))) :=
  Set.range (fun w : EuclideanSpace ℝ (Fin 8) => Ψ.symm (w, (0 : F)))

/-- **The zero-section piece** over the chart ball of radius `ρ` at `b`: the preimage under the
trivialising chart at the zero-section point of `b` of the compact convex set
`closedBall (centre, ρ/2) ∩ modelSubspace`. -/
def zeroBallPiece (Z : VectorBundleCore ℝ B F ι)
    (Ψ : EuclideanSpace ℝ (Fin (k + 8)) ≃ₜ (EuclideanSpace ℝ (Fin 8) × F)) (b : B) (ρ : ℝ) :
    Set Z.TotalSpace :=
  (bundleChartAt Z Ψ (⟨b, 0⟩ : Z.TotalSpace)) ⁻¹'
      (Metric.closedBall (bundleChartAt Z Ψ (⟨b, 0⟩ : Z.TotalSpace) (⟨b, 0⟩ : Z.TotalSpace)) (ρ / 2)
        ∩ modelSubspace Ψ) ∩
    (bundleChartAt Z Ψ (⟨b, 0⟩ : Z.TotalSpace)).source

end

end Work.ThomBordism
