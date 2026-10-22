import Mathlib
import Submission.Work.TOOLKIT.Basic

namespace Work.TOOLKIT.Les

open CategoryTheory CategoryTheory.Pretriangulated

/-- Explicit description of the connecting homomorphism `conn`: for `x : T.obj₁ ⟶ W⟦k⟧` it is
the composite `T.mor₃ ≫ x⟦1⟧' ≫ (W⟦k⟧⟦1⟧ ≅ W⟦k+1⟧).inv`.  Indeed, by
`Pretriangulated.preadditiveYoneda_homologySequenceδ_apply`, the connecting map of the
contravariant Yoneda functor is given by that formula. -/
lemma conn_eq (T : Triangle DCat) (W : DCat) (k : ℤ)
    (x : T.obj₁ ⟶ (shiftFunctor DCat k).obj W) :
    Work.TOOLKIT.conn T W k x =
      T.mor₃ ≫ x⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' DCat k 1 (k + 1) rfl).inv.app W := by
  rw [Work.TOOLKIT.conn, Pretriangulated.preadditiveYoneda_homologySequenceδ_apply]

/-- Naturality of the connecting homomorphism `conn` of the contravariant long exact sequence
under a morphism of distinguished triangles `ψ : T ⟶ T'`.  Both sides are functions on
`Hom(T'.obj₁, W⟦k⟧)`: the left one first precomposes with `ψ.hom₁` and then applies the
connecting map of `T`, the right one first applies the connecting map of `T'` and then
precomposes with `ψ.hom₃`. -/
theorem conn_naturality {T T' : CategoryTheory.Pretriangulated.Triangle Work.TOOLKIT.DCat}
    (ψ : T ⟶ T') (W : Work.TOOLKIT.DCat) (k : ℤ) :
    (fun u : T'.obj₁ ⟶ (CategoryTheory.shiftFunctor Work.TOOLKIT.DCat k).obj W =>
        Work.TOOLKIT.conn T W k (CategoryTheory.CategoryStruct.comp ψ.hom₁ u)) =
      (fun u : T'.obj₁ ⟶ (CategoryTheory.shiftFunctor Work.TOOLKIT.DCat k).obj W =>
        CategoryTheory.CategoryStruct.comp ψ.hom₃ (Work.TOOLKIT.conn T' W k u)) := by
  funext u
  rw [conn_eq T W k (ψ.hom₁ ≫ u), conn_eq T' W k u]
  simp only [Functor.map_comp, Category.assoc, TriangleMorphism.comm₃_assoc]

end Work.TOOLKIT.Les
