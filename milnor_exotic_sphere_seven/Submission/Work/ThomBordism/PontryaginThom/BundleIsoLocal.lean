import Submission.Work.TangentClasses.Bundle
import Submission.Work.Thom.BundleIso_comap_exists

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Building a bundle isomorphism from local continuous expressions

`Work.Thom.continuous_totalSpaceMap_clm_gen` is the criterion for the continuity of the map of total
spaces induced by a family of continuous linear maps: it suffices that, in every pair of charts, the
*trivialised* expression is continuous on the overlap.

This file records the resulting constructor of a `Work.Thom.BundleIso` from a fibrewise linear
isomorphism given by a family of continuous linear maps: it is the tool with which the splitting
`TV ⊕ ν ≅ ε^{k+8}` of an immersion is assembled from the chartwise expressions.
-/

open scoped Topology

namespace Work.ThomBordism.PontryaginThom

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type*} [TopologicalSpace B] {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {ι₁ ι₂ : Type*}

/-- **A bundle isomorphism from a fibrewise linear isomorphism whose chart expressions are
continuous.**  Given gluing data `Z₁`, `Z₂`, a fibrewise isomorphism `T` (with inverse `U`) whose
trivialised expressions are continuous on the overlaps, the induced map of total spaces is
continuous, and `T` is a `BundleIso`.

The pair of continuity hypotheses is exactly the hypothesis of
`Work.Thom.continuous_totalSpaceMap_clm_gen` (for `T` and for `U`). -/
theorem nonempty_bundleIso_of_clm (Z₁ : RealBundle B F₁ ι₁) (Z₂ : RealBundle B F₂ ι₂)
    (T : B → F₁ →L[ℝ] F₂) (U : B → F₂ →L[ℝ] F₁)
    (hT : ∀ i₁ i₂, ContinuousOn (fun b =>
      (Z₂.coordChange (Z₂.indexAt b) i₂ b).comp ((T b).comp (Z₁.coordChange i₁ (Z₁.indexAt b) b)))
      (Z₁.baseSet i₁ ∩ Z₂.baseSet i₂))
    (hU : ∀ i₂ i₁, ContinuousOn (fun b =>
      (Z₁.coordChange (Z₁.indexAt b) i₁ b).comp ((U b).comp (Z₂.coordChange i₂ (Z₂.indexAt b) b)))
      (Z₂.baseSet i₂ ∩ Z₁.baseSet i₁))
    (left_inv : ∀ b (x : F₁), U b (T b x) = x)
    (right_inv : ∀ b (y : F₂), T b (U b y) = y) :
    Nonempty (BundleIso Z₁ Z₂) := by
  have hcont₁ : Continuous (fun p : Z₁.TotalSpace => (⟨p.1, T p.1 p.2⟩ : Z₂.TotalSpace)) :=
    continuous_totalSpaceMap_clm_gen Z₁ Z₂ (ContinuousMap.id B) T fun i₁ i₂ => by
      simpa using hT i₁ i₂
  have hcont₂ : Continuous (fun p : Z₂.TotalSpace => (⟨p.1, U p.1 p.2⟩ : Z₁.TotalSpace)) :=
    continuous_totalSpaceMap_clm_gen Z₂ Z₁ (ContinuousMap.id B) U fun i₂ i₁ => by
      simpa using hU i₂ i₁
  exact ⟨{ hom := fun b => (T b : F₁ →ₗ[ℝ] F₂)
           inv := fun b => (U b : F₂ →ₗ[ℝ] F₁)
           left_inv := left_inv
           right_inv := right_inv
           continuous_hom := hcont₁
           continuous_inv := hcont₂ }⟩

end

end Work.ThomBordism.PontryaginThom
