import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Transporting charted space / manifold structures across a homeomorphism

Given a homeomorphism `e : X ≃ₜ Y` and a charted space structure on `X` modelled on a space `H`,
we push the charts of `X` forward along `e` to obtain a charted space structure on `Y`: the chart
of `Y` at a point `y` is the chart of `X` at `e.symm y`, read through `e.symm`.

The point of this construction is that the change of coordinates between two pushed charts is
*literally* the change of coordinates between the original charts (`pushChart_symm_trans_pushChart`,
proved by an explicit `OpenPartialHomeomorph.ext`): the homeomorphism cancels out.  Hence, if the
atlas of `X` is compatible with a structure groupoid `G` (e.g. the groupoid of `C^n` changes of
coordinates), then so is the pushed atlas, and a `C^n` manifold structure is transported.

As the charts of `Y` are the charts of `X` evaluated at the corresponding point of `X`, the
boundary is transported as well: `y ∈ boundary Y ↔ e.symm y ∈ boundary X`.

This is the lemma `Work.PTGeometric.exists_chartedSpace_and_isManifold_of_homeomorph`.
-/

open Set
open scoped Manifold

namespace Work.PTGeometric

noncomputable section

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]
variable {H : Type*} [TopologicalSpace H]

/-- Push a chart of `X` forward to a chart of `Y` along a homeomorphism `e : X ≃ₜ Y`: the domain
of the pushed chart is the preimage under `e.symm` of the domain of the original chart, and the
pushed chart is `y ↦ ψ (e.symm y)`. -/
def pushChart (e : Homeomorph X Y) (ψ : OpenPartialHomeomorph X H) :
    OpenPartialHomeomorph Y H :=
  e.symm.toOpenPartialHomeomorph ≫ₕ ψ

@[simp]
lemma pushChart_apply (e : Homeomorph X Y) (ψ : OpenPartialHomeomorph X H) (y : Y) :
    pushChart e ψ y = ψ (e.symm y) := rfl

@[simp]
lemma pushChart_symm (e : Homeomorph X Y) (ψ : OpenPartialHomeomorph X H) :
    (pushChart e ψ).symm = ψ.symm ≫ₕ e.toOpenPartialHomeomorph := rfl

/-- The change of coordinates between two pushed charts is exactly the change of coordinates
between the original charts: the homeomorphism `e` cancels out. -/
lemma pushChart_symm_trans_pushChart (e : Homeomorph X Y)
    (ψ ψ' : OpenPartialHomeomorph X H) :
    (pushChart e ψ).symm ≫ₕ (pushChart e ψ') = ψ.symm ≫ₕ ψ' := by
  refine OpenPartialHomeomorph.ext _ _ (fun x ↦ ?_) (fun x ↦ ?_) ?_
  · simp only [pushChart, OpenPartialHomeomorph.coe_trans,
      OpenPartialHomeomorph.coe_trans_symm, Homeomorph.toOpenPartialHomeomorph_apply,
      Function.comp_apply]
    simp
  · simp only [pushChart, OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply]
    simp
  · simp only [pushChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      univ_inter, preimage_preimage]
    simp

/-- The charted space structure on `Y` obtained by pushing forward the charts of `X` along a
homeomorphism `e : X ≃ₜ Y`. -/
@[instance_reducible]
def pushedChartedSpace [ChartedSpace H X] (e : Homeomorph X Y) : ChartedSpace H Y where
  atlas := pushChart e '' atlas H X
  chartAt y := pushChart e (chartAt H (e.symm y))
  mem_chart_source y := by
    simp only [pushChart, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, univ_inter, mem_preimage]
    exact mem_chart_source H (e.symm y)
  chart_mem_atlas y := ⟨chartAt H (e.symm y), chart_mem_atlas H (e.symm y), rfl⟩

lemma atlas_pushedChartedSpace [ChartedSpace H X] (e : Homeomorph X Y) :
    (pushedChartedSpace e).atlas = pushChart e '' atlas H X := rfl

/-- The preferred chart of the pushed charted space, evaluated at the point, agrees with the
preferred chart of `X` at the corresponding point. -/
lemma chartAt_pushedChartedSpace_apply [ChartedSpace H X] (e : Homeomorph X Y) (y : Y) :
    (pushedChartedSpace e).chartAt y y = (chartAt H (e.symm y)) (e.symm y) := rfl

/-- Pushing the atlas forward along a homeomorphism preserves the structure groupoid of changes
of coordinates. -/
theorem hasGroupoid_pushedChartedSpace [ChartedSpace H X] (e : Homeomorph X Y)
    (G : StructureGroupoid H) [HasGroupoid X G] :
    letI : ChartedSpace H Y := pushedChartedSpace e
    HasGroupoid Y G := by
  letI : ChartedSpace H Y := pushedChartedSpace e
  exact ⟨fun {φ φ'} hφ hφ' => by
    simp only [atlas, atlas_pushedChartedSpace, mem_image] at hφ hφ'
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    obtain ⟨ψ', hψ', rfl⟩ := hφ'
    rw [pushChart_symm_trans_pushChart]
    exact StructureGroupoid.compatible G hψ hψ'⟩

end

theorem exists_chartedSpace_and_isManifold_of_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : Homeomorph X Y)
    [ChartedSpace (EuclideanHalfSpace 9) X]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) ((⊤ : ℕ∞) : WithTop ℕ∞) X] :
    ∃ (c : ChartedSpace (EuclideanHalfSpace 9) Y), letI := c;
      ∃ (_ : IsManifold (modelWithCornersEuclideanHalfSpace 9) ((⊤ : ℕ∞) : WithTop ℕ∞) Y),
        (∀ y : Y, y ∈ (modelWithCornersEuclideanHalfSpace 9).boundary Y ↔
          e.symm y ∈ (modelWithCornersEuclideanHalfSpace 9).boundary X) := by
  set I := modelWithCornersEuclideanHalfSpace 9 with hI
  set n := ((⊤ : ℕ∞) : WithTop ℕ∞) with hn
  letI : ChartedSpace (EuclideanHalfSpace 9) Y := pushedChartedSpace e
  haveI : HasGroupoid Y (contDiffGroupoid n I) :=
    hasGroupoid_pushedChartedSpace e (contDiffGroupoid n I)
  haveI : IsManifold I n Y := IsManifold.mk' I n Y
  refine ⟨pushedChartedSpace e, ?_⟩
  refine ⟨inferInstance, ?_⟩
  intro y
  have hchart : (chartAt (EuclideanHalfSpace 9) y) y
      = (chartAt (EuclideanHalfSpace 9) (e.symm y)) (e.symm y) := rfl
  show I.IsBoundaryPoint y ↔ I.IsBoundaryPoint (e.symm y)
  rw [ModelWithCorners.isBoundaryPoint_iff, ModelWithCorners.isBoundaryPoint_iff]
  simp only [extChartAt_coe, Function.comp_apply, hchart]

end Work.PTGeometric
