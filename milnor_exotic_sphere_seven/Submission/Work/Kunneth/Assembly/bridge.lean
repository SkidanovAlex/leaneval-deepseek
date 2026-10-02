import Mathlib
import Submission.Work.Kunneth.Assembly.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The bridge between the simplicial cross product and the space-level cup product

`Work.Kunneth.Asm.iota m B : Sing (B × Qb m) ⟶ Sing B ⊗ Sing Qb m` is the monoidal comparison
(compatible with the projections by `Work.Kunneth.Asm.iota_comp_fst`/`iota_comp_snd`), and
`Work.Kunneth.Asm.pullIso m B n` is the pullback along it.

* `pullIso_crossH`: the pullback along `iota` of the simplicial cross product
  `Work.Kunneth.crossH` is the cup product of the pullbacks along the two projections;
* `pullIso_bijective`: since `iota` is an isomorphism of simplicial sets, this pullback is
  bijective.
-/

namespace Work.Kunneth.Asm

open CategoryTheory CategoryTheory.Limits Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization MonoidalCategory TensorProduct

noncomputable section

theorem iota_comp_fst (m : ℕ) (B : Type) [TopologicalSpace B] :
    CategoryTheory.CategoryStruct.comp (iota m B)
        (CategoryTheory.SemiCartesianMonoidalCategory.fst (ssB B) (ssB (Qb m)))
      = TopCat.toSSet.map (TopCat.ofHom (pi1 m B)) := by
  have hμ : CategoryTheory.CategoryStruct.comp (Work.Kunneth.singProdIso (TopCat.of B)
      (TopCat.of (Qb m))).hom
      (Functor.Monoidal.μIso TopCat.toSSet (TopCat.of B) (TopCat.of (Qb m))).hom
      = 𝟙 (ssB (B × Qb m)) :=
    Iso.inv_hom_id (Functor.Monoidal.μIso TopCat.toSSet (TopCat.of B) (TopCat.of (Qb m)))
  have hfst : CategoryTheory.SemiCartesianMonoidalCategory.fst (ssB B) (ssB (Qb m))
      = CategoryTheory.CategoryStruct.comp
        (Functor.Monoidal.μIso TopCat.toSSet (TopCat.of B) (TopCat.of (Qb m))).hom
        (TopCat.toSSet.map (CategoryTheory.SemiCartesianMonoidalCategory.fst
          (TopCat.of B) (TopCat.of (Qb m)))) :=
    (Functor.Monoidal.μ_fst (TopCat.toSSet) (TopCat.of B) (TopCat.of (Qb m))).symm
  rw [hfst, ← CategoryTheory.Category.assoc]
  rw [show CategoryTheory.CategoryStruct.comp (iota m B)
      (Functor.Monoidal.μIso TopCat.toSSet (TopCat.of B) (TopCat.of (Qb m))).hom
      = 𝟙 (ssB (B × Qb m)) from hμ]
  rw [CategoryTheory.Category.id_comp]
  exact congrArg (fun (f : TopCat.of (B × Qb m) ⟶ TopCat.of B) => TopCat.toSSet.map f) rfl

theorem iota_comp_snd (m : ℕ) (B : Type) [TopologicalSpace B] :
    CategoryTheory.CategoryStruct.comp (iota m B)
        (CategoryTheory.SemiCartesianMonoidalCategory.snd (ssB B) (ssB (Qb m)))
      = TopCat.toSSet.map (TopCat.ofHom (pi2 m B)) := by
  have hμ : CategoryTheory.CategoryStruct.comp (Work.Kunneth.singProdIso (TopCat.of B)
      (TopCat.of (Qb m))).hom
      (Functor.Monoidal.μIso TopCat.toSSet (TopCat.of B) (TopCat.of (Qb m))).hom
      = 𝟙 (ssB (B × Qb m)) :=
    Iso.inv_hom_id (Functor.Monoidal.μIso TopCat.toSSet (TopCat.of B) (TopCat.of (Qb m)))
  have hsnd : CategoryTheory.SemiCartesianMonoidalCategory.snd (ssB B) (ssB (Qb m))
      = CategoryTheory.CategoryStruct.comp
        (Functor.Monoidal.μIso TopCat.toSSet (TopCat.of B) (TopCat.of (Qb m))).hom
        (TopCat.toSSet.map (CategoryTheory.SemiCartesianMonoidalCategory.snd
          (TopCat.of B) (TopCat.of (Qb m)))) :=
    (Functor.Monoidal.μ_snd (TopCat.toSSet) (TopCat.of B) (TopCat.of (Qb m))).symm
  rw [hsnd, ← CategoryTheory.Category.assoc]
  rw [show CategoryTheory.CategoryStruct.comp (iota m B)
      (Functor.Monoidal.μIso TopCat.toSSet (TopCat.of B) (TopCat.of (Qb m))).hom
      = 𝟙 (ssB (B × Qb m)) from hμ]
  rw [CategoryTheory.Category.id_comp]
  exact congrArg (fun (f : TopCat.of (B × Qb m) ⟶ TopCat.of (Qb m)) => TopCat.toSSet.map f) rfl

theorem pullIso_crossH (m : ℕ) (B : Type) [TopologicalSpace B] (p q : ℕ)
    (a : Coh ℤ p B) (b : Coh ℤ q (Qb m)) :
    pullIso m B (p + q) (Work.Kunneth.crossH (ssB B) (ssB (Qb m)) p q a b)
      = Work.Cohomology.cupH' ℤ (ssB (B × Qb m)) p q
          ((CohMap (pi1 m B) ℤ p).hom a) ((CohMap (pi2 m B) ℤ q).hom b) := by
  rw [Work.Kunneth.crossH_apply]
  erw [Work.Kunneth.pullbackH_cupH]
  refine congrArg₂ (fun x y => Work.Cohomology.cupH' ℤ (ssB (B × Qb m)) p q x y) ?_ ?_
  · rw [← Work.Kunneth.pullbackH_comp, iota_comp_fst]
    rfl
  · rw [← Work.Kunneth.pullbackH_comp, iota_comp_snd]
    rfl

/-- The inverse of the monoidal comparison, as a simplicial map. -/
abbrev iotaInv (m : ℕ) (B : Type) [TopologicalSpace B] :
    Work.Kunneth.sProd (ssB B) (ssB (Qb m)) ⟶ ssB (B × Qb m) :=
  (Work.Kunneth.singProdIso (TopCat.of B) (TopCat.of (Qb m))).inv

theorem iota_comp_iotaInv (m : ℕ) (B : Type) [TopologicalSpace B] :
    CategoryTheory.CategoryStruct.comp (iota m B) (iotaInv m B) = 𝟙 (ssB (B × Qb m)) :=
  Iso.hom_inv_id _

theorem iotaInv_comp_iota (m : ℕ) (B : Type) [TopologicalSpace B] :
    CategoryTheory.CategoryStruct.comp (iotaInv m B) (iota m B)
      = 𝟙 (Work.Kunneth.sProd (ssB B) (ssB (Qb m))) :=
  Iso.inv_hom_id _

theorem pullIso_bijective (m : ℕ) (B : Type) [TopologicalSpace B] (n : ℕ) :
    Function.Bijective (pullIso m B n) := by
  have hleft : Function.LeftInverse
      (Work.Kunneth.pullbackH (Work.Kunneth.sProd (ssB B) (ssB (Qb m)))
        (ssB (B × Qb m)) (iotaInv m B) n) (pullIso m B n) := by
    intro x
    rw [show pullIso m B n = Work.Kunneth.pullbackH (ssB (B × Qb m))
      (Work.Kunneth.sProd (ssB B) (ssB (Qb m))) (iota m B) n from rfl]
    erw [← Work.Kunneth.pullbackH_comp, iotaInv_comp_iota]
    exact Work.Kunneth.pullbackH_id _ n x
  have hright : Function.RightInverse
      (Work.Kunneth.pullbackH (Work.Kunneth.sProd (ssB B) (ssB (Qb m)))
        (ssB (B × Qb m)) (iotaInv m B) n) (pullIso m B n) := by
    intro y
    rw [show pullIso m B n = Work.Kunneth.pullbackH (ssB (B × Qb m))
      (Work.Kunneth.sProd (ssB B) (ssB (Qb m))) (iota m B) n from rfl]
    erw [← Work.Kunneth.pullbackH_comp, iota_comp_iotaInv]
    exact Work.Kunneth.pullbackH_id _ n y
  exact ⟨hleft.injective, hright.surjective⟩

end

end Work.Kunneth.Asm
