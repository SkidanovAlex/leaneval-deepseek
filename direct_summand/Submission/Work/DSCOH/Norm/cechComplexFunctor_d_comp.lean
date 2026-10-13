import Mathlib
import Submission.Work.DSCOH.Norm.Defs
import Submission.Work.DSCOH.Norm.SemiOrd

namespace Work.DSCOH.Norm

universe u v w

open scoped BigOperators
open CategoryTheory

/-- The cosimplicial object whose alternating coface complex *is* Mathlib's unnormalized Čech
complex of the presheaf `P` with respect to the family `U` (definitionally). -/
noncomputable abbrev cechCosimp {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
    {ι : Type w} [CategoryTheory.Limits.HasProducts.{w} (ModuleCat A)]
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) : CosimplicialObject (ModuleCat A) :=
  (CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
    ((CategoryTheory.Limits.FormalCoproduct.mk ι U).cech)).obj P

/-- The coface map of `cechCosimp P U` along `SimplexCategory.δ b` is the "delete the `b`-th
entry and restrict" map. -/
lemma cechCosimp_δ {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
    {ι : Type w} [CategoryTheory.Limits.HasProducts.{w} (ModuleCat A)]
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) {n : ℕ} (b : Fin (n + 2)) :
    (cechCosimp P U).δ b =
      CategoryTheory.Limits.Pi.lift (fun x : Fin (n + 2) → ι =>
        CategoryTheory.Limits.Pi.π (fun y : Fin (n + 1) → ι => tupleMod P U y) (del x b) ≫
          resDel P U x b) := by
  dsimp only [CosimplicialObject.δ, cechCosimp,
    CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor, Functor.whiskeringLeft,
    Functor.comp_obj, Functor.comp_map]
  rw [CategoryTheory.Limits.FormalCoproduct.evalOp_obj_map]
  simp only [Functor.rightOp_obj, Functor.rightOp_map, Quiver.Hom.unop_op]
  rw [CategoryTheory.Limits.FormalCoproduct.cech_map]
  simp only [Quiver.Hom.unop_op, CategoryTheory.Limits.FormalCoproduct.cech_obj]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The differential of Mathlib's unnormalized Čech complex is the alternating sum of the
coface maps of the underlying cosimplicial object. -/
lemma cechComplexFunctor_d_eq {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
    {ι : Type w} [CategoryTheory.Limits.HasProducts.{w} (ModuleCat A)]
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) :
    ((CategoryTheory.cechComplexFunctor U).obj P).d n (n + 1) =
      ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) • (cechCosimp P U).δ b := by
  change (AlgebraicTopology.AlternatingCofaceMapComplex.obj (cechCosimp P U)).d n (n + 1) = _
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD]

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary form of `cechComplexFunctor_d_comp`.  It is proved with `isDefEq` not respecting
transparency: the composite Čech terms are only *definitionally* equal to the explicit products
`∏ᶜ fun y => tupleMod P U y`. -/
private theorem cechComplexFunctor_d_comp_aux {X : Type u} [TopologicalSpace X] {A : Type v}
    [CommRing A] {ι : Type w} [Fintype ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : Opposite (TopologicalSpace.Opens X) ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) :
    ((CategoryTheory.cechComplexFunctor U).obj P).d n (n + 1) =
      CategoryTheory.Limits.Pi.lift (fun x : Fin (n + 2) → ι =>
        ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) •
          (CategoryTheory.Limits.Pi.π
              (fun y : Fin (n + 1) → ι => Work.DSCOH.Norm.tupleMod P U y)
              (Work.DSCOH.Norm.del x b) ≫ Work.DSCOH.Norm.resDel P U x b)) := by
  have hβ : ∀ b : Fin (n + 2), (cechCosimp P U).δ b =
      CategoryTheory.Limits.Pi.lift (fun x : Fin (n + 2) → ι =>
        CategoryTheory.Limits.Pi.π (fun y : Fin (n + 1) → ι => tupleMod P U y) (del x b) ≫
          resDel P U x b) := by
    intro b
    dsimp only [CosimplicialObject.δ, cechCosimp,
      CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor, Functor.whiskeringLeft,
      Functor.comp_obj, Functor.comp_map]
    rw [CategoryTheory.Limits.FormalCoproduct.evalOp_obj_map]
    simp only [Functor.rightOp_obj, Functor.rightOp_map, Quiver.Hom.unop_op]
    rw [CategoryTheory.Limits.FormalCoproduct.cech_map]
    simp only [Quiver.Hom.unop_op, CategoryTheory.Limits.FormalCoproduct.cech_obj]
    rfl
  rw [cechComplexFunctor_d_eq P U n]
  apply CategoryTheory.Limits.Pi.hom_ext
    (f := fun y : Fin (n + 2) → ι => Work.DSCOH.Norm.tupleMod P U y)
  intro x
  have key : ∀ b : Fin (n + 2),
      (cechCosimp P U).δ b ≫
          CategoryTheory.Limits.Pi.π (fun y : Fin (n + 2) → ι => tupleMod P U y) x =
        CategoryTheory.Limits.Pi.π (fun y : Fin (n + 1) → ι => tupleMod P U y) (del x b) ≫
          resDel P U x b := by
    intro b
    rw [hβ b, CategoryTheory.Limits.Pi.lift_comp_π]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, CategoryTheory.Limits.Pi.lift_comp_π,
    key]

/-- The `x`-th component of the differential of Mathlib's unnormalized Čech complex is the
alternating sum, over the entries `b` of `x`, of the "delete the `b`-th entry and restrict"
map.  This is the component formula for `cechComplexFunctor`, in the vocabulary of
`Work.DSCOH.Norm` (`tupleMod`, `del`, `resDel`). -/
theorem cechComplexFunctor_d_comp {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
    {ι : Type w} [Fintype ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : Opposite (TopologicalSpace.Opens X) ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) :
    ((CategoryTheory.cechComplexFunctor U).obj P).d n (n + 1) =
      CategoryTheory.Limits.Pi.lift (fun x : Fin (n + 2) → ι =>
        ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) •
          (CategoryTheory.Limits.Pi.π
              (fun y : Fin (n + 1) → ι => Work.DSCOH.Norm.tupleMod P U y)
              (Work.DSCOH.Norm.del x b) ≫ Work.DSCOH.Norm.resDel P U x b)) :=
  cechComplexFunctor_d_comp_aux P U n

end Work.DSCOH.Norm
