import Mathlib
import Submission.Work.Tubular.LocalStep
import Submission.Work.Orient.Closed
import Submission.Work.Orient.Bridge
import Submission.Work.Thom.ThomClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# The zero section carries the fundamental class onto a generator of `H_8` of the total space

For a real bundle `Z` over a closed oriented smooth `8`-manifold `V` the total space `Z.TotalSpace`
is homotopy equivalent to `V` (fibrewise rescaling, `Work.Thom.homotopic_zeroSection_comp_bundleProj`),
with homotopy inverse the zero section `z` and the projection `π`.  Consequently
`z_* : H_8(V) → H_8(Z.TotalSpace)` is an isomorphism; since the fundamental class `V.c` generates
`H_8(V)` (`Work.Orient.span_singleton_eq_top_of_isFundClass`), its image under `z_*` generates
`H_8(Z.TotalSpace)`.
-/

namespace Work.ThomBordism

open CategoryTheory AlgebraicTopology
open Work.Cohomology

noncomputable section

/-! ## The projection of a real bundle as a morphism of `TopCat` -/

/-- The projection `π : Z.TotalSpace ⟶ B` of a real bundle. -/
def bundleProjTop {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι) :
    TopCat.of Z.TotalSpace ⟶ TopCat.of B :=
  TopCat.ofHom (Work.Thom.bundleProj Z)

/-! ## The homological toolkit -/

/-- The chain maps of a composite are the composite of the chain maps. -/
theorem chainMap_comp_self {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    chainMap ℤ X Y f ≫ chainMap ℤ Y Z g = chainMap ℤ X Z (f ≫ g) := by
  simp only [chainMap, CategoryTheory.Functor.map_comp]

/-- The chain map of an identity is the identity. -/
theorem chainMap_id_self (X : TopCat) :
    chainMap ℤ X X (𝟙 X) = 𝟙 (singularChains ℤ X) := by
  simp only [chainMap, CategoryTheory.Functor.map_id]

/-- Functoriality of `homologyMap` for singular chain maps. -/
theorem homologyMap_chainMap_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    HomologicalComplex.homologyMap (chainMap ℤ X Z (f ≫ g)) n =
      HomologicalComplex.homologyMap (chainMap ℤ X Y f) n ≫
        HomologicalComplex.homologyMap (chainMap ℤ Y Z g) n := by
  rw [← chainMap_comp_self]
  exact HomologicalComplex.homologyMap_comp _ _ n

/-- **Homotopy invariance of singular homology.**  Homotopic continuous maps induce the same map on
singular homology. -/
theorem homologyMap_chainMap_homotopic {X Y : TopCat} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (n : ℕ) :
    HomologicalComplex.homologyMap (chainMap ℤ X Y f) n =
      HomologicalComplex.homologyMap (chainMap ℤ X Y g) n :=
  H.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) n

/-- A surjective `ℤ`-linear map carries a generating class to a generating class. -/
theorem span_singleton_eq_top_of_surjective {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) {x : M}
    (hx : Submodule.span ℤ ({x} : Set M) = ⊤) :
    Submodule.span ℤ ({f x} : Set N) = ⊤ := by
  rw [← LinearMap.range_eq_top.mpr hf, ← Submodule.map_top f, ← hx, Submodule.map_span,
    Set.image_singleton]

/-! ## The main theorem -/

theorem zeroSectionFundClassSpan {V : Work.ThomBordism.Man8} {k : ℕ} {ι : Type}
    (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι) [PathConnectedSpace V.pt] :
    Submodule.span ℤ ({((HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of V.pt) (TopCat.of Z.TotalSpace)
        (Work.Tubular.zeroSectionTop Z)) 8) V.c)} : Set _) = ⊤ := by
  haveI : ConnectedSpace V.pt := PathConnectedSpace.connectedSpace
  -- The fundamental class generates `H_8(V)`.
  have hspanV : Submodule.span ℤ
      ({V.c} : Set ((singularChains ℤ (TopCat.of V.pt)).homology 8)) = ⊤ :=
    Work.Orient.span_singleton_eq_top_of_isFundClass 8 (by norm_num) (TopCat.of V.pt) V.c
      (Work.Orient.Man8.isFundClass V)
  -- The zero section is a section of the projection.
  have hcomp_zp : Work.Tubular.zeroSectionTop Z ≫ bundleProjTop Z = 𝟙 (TopCat.of V.pt) := by
    rw [Work.Tubular.zeroSectionTop, bundleProjTop,
      ← TopCat.ofHom_comp (Work.Thom.zeroSection Z) (Work.Thom.bundleProj Z)]
    have h : (Work.Thom.bundleProj Z).comp (Work.Thom.zeroSection Z) = ContinuousMap.id V.pt := by
      ext x; rfl
    rw [h, TopCat.ofHom_id]
  -- `z ∘ π` is homotopic to the identity of the total space.
  have hhom : TopCat.Homotopy (bundleProjTop Z ≫ Work.Tubular.zeroSectionTop Z)
      (𝟙 (TopCat.of Z.TotalSpace)) :=
    (Work.Thom.homotopic_zeroSection_comp_bundleProj Z).some
  -- The two composite homology maps.
  have hA : HomologicalComplex.homologyMap
        (chainMap ℤ (TopCat.of V.pt) (TopCat.of Z.TotalSpace)
          (Work.Tubular.zeroSectionTop Z)) 8
      ≫ HomologicalComplex.homologyMap
        (chainMap ℤ (TopCat.of Z.TotalSpace) (TopCat.of V.pt) (bundleProjTop Z)) 8
      = 𝟙 ((singularChains ℤ (TopCat.of V.pt)).homology 8) := by
    rw [← homologyMap_chainMap_comp (Work.Tubular.zeroSectionTop Z) (bundleProjTop Z) 8,
      hcomp_zp, chainMap_id_self, HomologicalComplex.homologyMap_id]
  have hB : HomologicalComplex.homologyMap
        (chainMap ℤ (TopCat.of Z.TotalSpace) (TopCat.of V.pt) (bundleProjTop Z)) 8
      ≫ HomologicalComplex.homologyMap
        (chainMap ℤ (TopCat.of V.pt) (TopCat.of Z.TotalSpace)
          (Work.Tubular.zeroSectionTop Z)) 8
      = 𝟙 ((singularChains ℤ (TopCat.of Z.TotalSpace)).homology 8) := by
    rw [← homologyMap_chainMap_comp (bundleProjTop Z) (Work.Tubular.zeroSectionTop Z) 8,
      homologyMap_chainMap_homotopic hhom 8, chainMap_id_self,
      HomologicalComplex.homologyMap_id]
  -- `z_*` is surjective, because `z_* ∘ π_* = id`.
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of V.pt) (TopCat.of Z.TotalSpace)
        (Work.Tubular.zeroSectionTop Z)) 8).hom := by
    intro y
    exact ⟨(HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of Z.TotalSpace) (TopCat.of V.pt) (bundleProjTop Z)) 8).hom y,
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hB) y⟩
  exact span_singleton_eq_top_of_surjective _ hsurj hspanV

end

end Work.ThomBordism
