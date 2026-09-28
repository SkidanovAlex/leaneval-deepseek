import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Thom

open CategoryTheory MonoidalCategory Simplicial SimplicialObject Opposite

/-- Compatibility of the combinatorial homotopies associated to homotopies of
simplicial sets: if `H : SSet.Homotopy f g` and `H' : SSet.Homotopy f' g'` are
related by morphisms `u : X ⟶ X'`, `v : Y ⟶ Y'` (i.e. `H.h ≫ v = (u ▷ Δ[1]) ≫ H'.h`),
then the corresponding `SimplicialObject.Homotopy`'s satisfy the same compatibility
condition degreewise. -/
theorem toSimplicialObjectHomotopy_h_naturality {X Y X' Y' : SSet} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}
    (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g') (u : X ⟶ X') (v : Y ⟶ Y')
    (hvu : H.h ≫ v = (u ▷ Δ[1]) ≫ H'.h) {n : ℕ} (i : Fin (n+1)) :
    (H.toSimplicialObjectHomotopy).h i ≫ v.app (op ⦋n+1⦌)
      = u.app (op ⦋n⦌) ≫ (H'.toSimplicialObjectHomotopy).h i := by
  ext x
  simp only [SSet.Homotopy.toSimplicialObjectHomotopy, TypeCat.Fun.toFun_apply, types_comp_apply,
    TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
  rw [← types_comp_apply, ← NatTrans.comp_app]
  rw [show ((SSet.yonedaEquiv.symm x ▷ Δ[1] ≫ H.h) ≫ v)
      = (SSet.yonedaEquiv.symm ((ConcreteCategory.hom (u.app (op ⦋n⦌))) x) ▷ Δ[1]) ≫ H'.h from by
        rw [Category.assoc, hvu, ← Category.assoc, ← comp_whiskerRight, SSet.yonedaEquiv_symm_comp]]

/-- Naturality of the chain homotopy induced by a combinatorial homotopy of
simplicial objects in a preadditive category: the components of
`Homotopy.toChainHomotopy` commute with the chain maps induced by `u` and `v`,
provided the combinatorial homotopies are compatible. -/
theorem toChainHomotopy_hom_naturality {C : Type*} [Category* C] [Preadditive C]
    {X Y X' Y' : SimplicialObject C} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}
    (H : SimplicialObject.Homotopy f g) (H' : SimplicialObject.Homotopy f' g')
    (u : X ⟶ X') (v : Y ⟶ Y')
    (hvu : ∀ {n : ℕ} (i : Fin (n+1)), H.h i ≫ v.app (op ⦋n+1⦌) = u.app (op ⦋n⦌) ≫ H'.h i)
    (n : ℕ) :
    (H.toChainHomotopy).hom n (n+1) ≫ ((AlgebraicTopology.alternatingFaceMapComplex C).map v).f (n+1)
      = ((AlgebraicTopology.alternatingFaceMapComplex C).map u).f n ≫ (H'.toChainHomotopy).hom n (n+1) := by
  simp only [SimplicialObject.Homotopy.toChainHomotopy,
    SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
    AlgebraicTopology.alternatingFaceMapComplex_map_f, hvu, Preadditive.neg_comp,
    Preadditive.comp_neg, Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul]

open CategoryTheory MonoidalCategory Simplicial SimplicialObject Opposite in
theorem SSetChainHomotopyNaturality {X Y X' Y' : SSet} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}
    (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g') (u : X ⟶ X') (v : Y ⟶ Y')
    (R : Type) [CommRing R] (hvu : H.h ≫ v = (u ▷ Δ[1]) ≫ H'.h) (n : ℕ) :
    (H.chainComplexMap (ModuleCat.of R R)).hom n (n+1)
        ≫ (SSet.chainComplexMap v (ModuleCat.of R R)).f (n+1)
      = (SSet.chainComplexMap u (ModuleCat.of R R)).f n
        ≫ (H'.chainComplexMap (ModuleCat.of R R)).hom n (n+1) := by
  let F := Limits.sigmaConst.obj (ModuleCat.of R R)
  let W := (SimplicialObject.whiskering (Type _) (ModuleCat R)).obj F
  have hcompat : ∀ {n : ℕ} (i : Fin (n+1)),
      ((H.toSimplicialObjectHomotopy).whiskerRight F).h i ≫ (W.map v).app (op ⦋n+1⦌)
        = (W.map u).app (op ⦋n⦌) ≫ ((H'.toSimplicialObjectHomotopy).whiskerRight F).h i := by
    intro n i
    rw [SimplicialObject.Homotopy.whiskerRight_h, SimplicialObject.Homotopy.whiskerRight_h,
      Functor.whiskeringRight_obj_map, Functor.whiskeringRight_obj_map, Functor.whiskerRight_app,
      Functor.whiskerRight_app,
      ← F.map_comp, ← F.map_comp, toSimplicialObjectHomotopy_h_naturality H H' u v hvu i]
  change ((H.toSimplicialObjectHomotopy).whiskerRight F).toChainHomotopy.hom n (n+1)
      ≫ ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat R)).map (W.map v)).f (n+1)
    = ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat R)).map (W.map u)).f n
      ≫ ((H'.toSimplicialObjectHomotopy).whiskerRight F).toChainHomotopy.hom n (n+1)
  exact toChainHomotopy_hom_naturality _ _ (W.map u) (W.map v) hcompat n

end Work.Thom
