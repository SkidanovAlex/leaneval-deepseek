import Mathlib
import Submission.Work.Cohomology.Pullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

/-!
# The cohomology model of the tangent-classes chapter

The workspace's cohomology model is singular cohomology computed from the singular cochain complex
of a simplicial set (`Submission/Work/Cohomology/Singular.lean`); the total space of a bundle is
turned into a simplicial set by `TopCat.toSSet`.  This module fixes the notation used throughout
the chapter:

* `Work.TangentClasses.H n B` is `H^n(B; ℤ)` in that model, `B` an arbitrary topological space;
* `Work.TangentClasses.HMap f n` is the pullback `f^* : H^n(B₂;ℤ) → H^n(B₁;ℤ)` along a continuous
  map `f : C(B₁, B₂)` (contravariance, `HMap_id`, `HMap_comp`, and `ℤ`-linearity, which is
  `map_add`/`map_zsmul` of the underlying linear map).

Everything in the chapter is stated with these two notations, so a caller can read
`p₁(TX) ∈ H 4 X` as an ordinary class in the model the endgame uses.
-/

namespace Work.TangentClasses

open CategoryTheory

noncomputable section

/-- `H^n(B; ℤ)`, singular cohomology with `ℤ` coefficients, in the workspace's model. -/
abbrev H (n : ℕ) (B : Type) [TopologicalSpace B] : ModuleCat ℤ :=
  Work.Cohomology.singularCohomology ℤ n (TopCat.of B)

/-- The pullback `f^* : H^n(B₂;ℤ) → H^n(B₁;ℤ)` along a continuous map `f : C(B₁, B₂)`. -/
abbrev HMap {B₁ B₂ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂] (f : C(B₁, B₂)) (n : ℕ) :
    H n B₂ ⟶ H n B₁ :=
  Work.Cohomology.singularCohomologyMap ℤ (TopCat.of B₁) (TopCat.of B₂) (TopCat.ofHom f) n

@[simp] theorem HMap_id {B : Type} [TopologicalSpace B] (n : ℕ) :
    HMap (ContinuousMap.id B) n = 𝟙 (H n B) := by
  rw [HMap, TopCat.ofHom_id, Work.Cohomology.singularCohomologyMap_id]

theorem HMap_comp {B₁ B₂ B₃ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂]
    [TopologicalSpace B₃] (f : C(B₁, B₂)) (g : C(B₂, B₃)) (n : ℕ) :
    HMap (g.comp f) n = HMap g n ≫ HMap f n := by
  rw [HMap, HMap, HMap, TopCat.ofHom_comp,
    Work.Cohomology.singularCohomologyMap_comp]

/-- The pullback is additive. -/
theorem HMap_add {B₁ B₂ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂] (f : C(B₁, B₂))
    (n : ℕ) (x y : H n B₂) : (HMap f n).hom (x + y) = (HMap f n).hom x + (HMap f n).hom y :=
  map_add _ x y

/-- The pullback is `ℤ`-linear (here: compatible with `ℤ`-smultiplication, the form used to pull
back an integral multiple of a generator). -/
theorem HMap_zsmul {B₁ B₂ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂] (f : C(B₁, B₂))
    (n : ℕ) (k : ℤ) (x : H n B₂) : (HMap f n).hom (k • x) = k • (HMap f n).hom x :=
  map_zsmul _ k x

end

end Work.TangentClasses
