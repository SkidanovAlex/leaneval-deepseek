import Mathlib

namespace Work.DSG1

open CategoryTheory Limits Pretriangulated

/-- A natural transformation `τ : F₁ ⟶ F₂` between functors equipped with commutation
isomorphisms with a shift, satisfying `NatTrans.CommShift τ ℤ`, induces a morphism of triangles
`F₁.mapTriangle.obj T ⟶ F₂.mapTriangle.obj T` whose components are `τ.app T.objᵢ`. -/
theorem triangleHomOfCommShift {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] {F₁ F₂ : C ⥤ D} [F₁.CommShift ℤ] [F₂.CommShift ℤ]
    (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] (T : Triangle C) :
    ∃ φ : F₁.mapTriangle.obj T ⟶ F₂.mapTriangle.obj T,
      φ.hom₁ = τ.app T.obj₁ ∧ φ.hom₂ = τ.app T.obj₂ ∧ φ.hom₃ = τ.app T.obj₃ := by
  refine ⟨Triangle.homMk _ _ (τ.app T.obj₁) (τ.app T.obj₂) (τ.app T.obj₃)
    (τ.naturality T.mor₁) (τ.naturality T.mor₂) ?_, rfl, rfl, rfl⟩
  simp only [Functor.mapTriangle_obj, Triangle.mk_mor₃, Category.assoc,
    NatTrans.shift_app_comm τ (1 : ℤ) T.obj₁, NatTrans.naturality_assoc]

end Work.DSG1
