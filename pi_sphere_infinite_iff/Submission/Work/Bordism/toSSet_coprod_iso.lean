import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Bordism.coprod_simplices_equiv

/-!
# The singular simplicial set of a disjoint union

`TopCat.toSSet` is right adjoint to geometric realization, hence preserves *limits*, not
coproducts; nevertheless the singular simplicial set of a coproduct of topological spaces *is*
the coproduct of the singular simplicial sets, because the standard simplex `Δᵏ` is connected:
every continuous map `Δᵏ ⟶ X ⊕ Y` lands entirely in one of the summands, so that the levelwise
"product" (the universal property of the coproduct in `TopCat`) is in fact a "sum".

We reduce from the abstract coproduct `X ⨿ Y` of `TopCat` to the *concrete* disjoint union
`TopCat.of (X ⊕ Y)` (which is isomorphic to it, `Work.Bordism.coprodIso`, and `toSSet` carries
this isomorphism to an isomorphism of simplicial sets) and then exhibit a colimit cofan with point
`toSSet.obj (TopCat.of (X ⊕ Y))` whose two legs are `toSSet` of the two sum inclusions. The
levelwise colimit statement is `Types.binaryCofan_isColimit_iff` together with the connectedness
of `Δᵏ`, packaged as the splitting `Work.Bordism.splitEquiv` of the `k`-simplices.
-/

open CategoryTheory Limits Topology

namespace Work.Bordism

universe u

/-- `TopCat.toSSet` acts on simplices by postcomposition with the map of spaces. -/
@[simp]
lemma toSSetObjEquiv_map_apply {X Z : TopCat.{u}} (g : X ⟶ Z) (n : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj X).obj n) :
    (TopCat.toSSetObjEquivT Z n) ((TopCat.toSSet.map g).app n x) =
      g.hom.comp ((TopCat.toSSetObjEquivT X n) x) := rfl

/-- The abstract coproduct `X ⨿ Y` of `TopCat` is the concrete disjoint union `TopCat.of (X ⊕ Y)`. -/
noncomputable def coprodIso (X Y : TopCat.{u}) :
    Limits.coprod X Y ≅ TopCat.of (↑X ⊕ ↑Y) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit (pair X Y))
    (TopCat.binaryCofanIsColimit X Y)

/-! ## The levelwise splitting -/

section Splitting

variable (X Y : TopCat.{u})

/-- The `k`-simplices of the singular simplicial set of `X ⊕ Y` split as the two summands
`(toSSet.obj X).obj k` and `(toSSet.obj Y).obj k`, because `Δᵏ` is connected. -/
noncomputable def splitEquiv (k : SimplexCategoryᵒᵖ) :
    (TopCat.toSSet.obj (TopCat.of (↑X ⊕ ↑Y))).obj k ≃
      (TopCat.toSSet.obj X).obj k ⊕ (TopCat.toSSet.obj Y).obj k :=
  (TopCat.toSSetObjEquivT (TopCat.of (↑X ⊕ ↑Y)) k).trans
    ((sumCMEquiv (T := stdSimplex ℝ (Fin (k.unop.len + 1)))).symm.trans
      (Equiv.sumCongr (TopCat.toSSetObjEquivT X k).symm (TopCat.toSSetObjEquivT Y k).symm))

/-- The splitting of the simplices of `X ⊕ Y` is compatible with the inclusion of `X`. -/
lemma splitEquiv_inl_apply (k : SimplexCategoryᵒᵖ) (x : (TopCat.toSSet.obj X).obj k) :
    splitEquiv X Y k
        ((TopCat.toSSet.map (TopCat.ofHom (⟨Sum.inl, continuous_inl⟩ :
          C(↑X, ↑X ⊕ ↑Y)))).app k x) = Sum.inl x := by
  rw [splitEquiv, Equiv.trans_apply, Equiv.trans_apply, toSSetObjEquiv_map_apply]
  have h : (TopCat.ofHom (⟨Sum.inl, continuous_inl⟩ : C(↑X, ↑X ⊕ ↑Y))).hom.comp
      ((TopCat.toSSetObjEquivT X k) x)
      = sumCMEquiv (Sum.inl ((TopCat.toSSetObjEquivT X k) x)) := rfl
  rw [h, Equiv.symm_apply_apply]
  simp

/-- The splitting of the simplices of `X ⊕ Y` is compatible with the inclusion of `Y`. -/
lemma splitEquiv_inr_apply (k : SimplexCategoryᵒᵖ) (y : (TopCat.toSSet.obj Y).obj k) :
    splitEquiv X Y k
        ((TopCat.toSSet.map (TopCat.ofHom (⟨Sum.inr, continuous_inr⟩ :
          C(↑Y, ↑X ⊕ ↑Y)))).app k y) = Sum.inr y := by
  rw [splitEquiv, Equiv.trans_apply, Equiv.trans_apply, toSSetObjEquiv_map_apply]
  have h : (TopCat.ofHom (⟨Sum.inr, continuous_inr⟩ : C(↑Y, ↑X ⊕ ↑Y))).hom.comp
      ((TopCat.toSSetObjEquivT Y k) y)
      = sumCMEquiv (Sum.inr ((TopCat.toSSetObjEquivT Y k) y)) := rfl
  rw [h, Equiv.symm_apply_apply]
  simp

/-- The levelwise cofan with point `(toSSet.obj (X ⊕ Y)).obj k` is a coproduct cofan: this is
the connectedness of `Δᵏ`. -/
noncomputable def level_isColimit (k : SimplexCategoryᵒᵖ) :
    IsColimit (BinaryCofan.mk
      (P := (TopCat.toSSet.obj (TopCat.of (↑X ⊕ ↑Y))).obj k)
      ((TopCat.toSSet.map (TopCat.ofHom (⟨Sum.inl, continuous_inl⟩ :
        C(↑X, ↑X ⊕ ↑Y)))).app k)
      ((TopCat.toSSet.map (TopCat.ofHom (⟨Sum.inr, continuous_inr⟩ :
        C(↑Y, ↑X ⊕ ↑Y)))).app k)) := by
  have h1 : Function.Injective
      ((TopCat.toSSet.map (TopCat.ofHom (⟨Sum.inl, continuous_inl⟩ :
        C(↑X, ↑X ⊕ ↑Y)))).app k) := by
    intro a b hab
    have : (Sum.inl a : (TopCat.toSSet.obj X).obj k ⊕ (TopCat.toSSet.obj Y).obj k)
        = Sum.inl b := by
      rw [← splitEquiv_inl_apply X Y k a, ← splitEquiv_inl_apply X Y k b, hab]
    exact Sum.inl.inj this
  have h2 : Function.Injective
      ((TopCat.toSSet.map (TopCat.ofHom (⟨Sum.inr, continuous_inr⟩ :
        C(↑Y, ↑X ⊕ ↑Y)))).app k) := by
    intro a b hab
    have : (Sum.inr a : (TopCat.toSSet.obj X).obj k ⊕ (TopCat.toSSet.obj Y).obj k)
        = Sum.inr b := by
      rw [← splitEquiv_inr_apply X Y k a, ← splitEquiv_inr_apply X Y k b, hab]
    exact Sum.inr.inj this
  have h3 : IsCompl
      (Set.range ((TopCat.toSSet.map (TopCat.ofHom (⟨Sum.inl, continuous_inl⟩ :
        C(↑X, ↑X ⊕ ↑Y)))).app k))
      (Set.range ((TopCat.toSSet.map (TopCat.ofHom (⟨Sum.inr, continuous_inr⟩ :
        C(↑Y, ↑X ⊕ ↑Y)))).app k)) := by
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      rintro z ⟨a, rfl⟩ ⟨b, hb⟩
      have e1 := splitEquiv_inl_apply X Y k a
      have e2 := splitEquiv_inr_apply X Y k b
      rw [hb] at e2
      exact Sum.inl_ne_inr (e1.symm.trans e2)
    · rw [codisjoint_iff]
      refine Set.eq_univ_iff_forall.2 ?_
      intro z
      rcases hz : splitEquiv X Y k z with a | b
      · exact Or.inl ⟨a, (splitEquiv X Y k).injective (by rw [splitEquiv_inl_apply, ← hz])⟩
      · exact Or.inr ⟨b, (splitEquiv X Y k).injective (by rw [splitEquiv_inr_apply, ← hz])⟩
  exact Nonempty.some ((Types.binaryCofan_isColimit_iff (BinaryCofan.mk
    (P := (TopCat.toSSet.obj (TopCat.of (↑X ⊕ ↑Y))).obj k)
    ((TopCat.toSSet.map (TopCat.ofHom (⟨Sum.inl, continuous_inl⟩ :
      C(↑X, ↑X ⊕ ↑Y)))).app k)
    ((TopCat.toSSet.map (TopCat.ofHom (⟨Sum.inr, continuous_inr⟩ :
      C(↑Y, ↑X ⊕ ↑Y)))).app k))).mpr ⟨h1, h2, h3⟩)

end Splitting

/-! ## The cofan of the singular simplicial set of a disjoint union -/

/-- The cofan expressing that `toSSet.obj (X ⊕ Y)` is a coproduct of `toSSet.obj X` and
`toSSet.obj Y`. -/
noncomputable def sumCofan (X Y : TopCat.{u}) :
    BinaryCofan (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) :=
  BinaryCofan.mk (TopCat.toSSet.map (TopCat.ofHom (⟨Sum.inl, continuous_inl⟩ :
      C(↑X, ↑X ⊕ ↑Y))))
    (TopCat.toSSet.map (TopCat.ofHom (⟨Sum.inr, continuous_inr⟩ : C(↑Y, ↑X ⊕ ↑Y))))

set_option backward.isDefEq.respectTransparency false in
/-- The cofan `sumCofan X Y` is a colimit cofan. -/
noncomputable def sumCofan_isColimit (X Y : TopCat.{u}) : IsColimit (sumCofan X Y) := by
  apply evaluationJointlyReflectsColimits (K := SimplexCategoryᵒᵖ) (C := Type u)
  intro k
  have hck := level_isColimit X Y k
  refine (IsColimit.equivOfNatIsoOfIso
    (α := (pairComp (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj k)).symm)
    (BinaryCofan.mk
      (P := (TopCat.toSSet.obj (TopCat.of (↑X ⊕ ↑Y))).obj k)
      ((TopCat.toSSet.map (TopCat.ofHom (⟨Sum.inl, continuous_inl⟩ :
        C(↑X, ↑X ⊕ ↑Y)))).app k)
      ((TopCat.toSSet.map (TopCat.ofHom (⟨Sum.inr, continuous_inr⟩ :
        C(↑Y, ↑X ⊕ ↑Y)))).app k))
    (((evaluation SimplexCategoryᵒᵖ (Type u)).obj k).mapCocone (sumCofan X Y))
    ?_) hck
  refine Cocone.ext (Iso.refl _) ?_
  intro j
  rcases j with ⟨(_ | _)⟩
  · simp [Cocone.precompose_obj_ι, NatTrans.comp_app, Iso.refl_hom, sumCofan,
      pairComp, diagramIsoPair, mapPairIso]
    try rfl
  · simp [Cocone.precompose_obj_ι, NatTrans.comp_app, Iso.refl_hom, sumCofan,
      pairComp, diagramIsoPair, mapPairIso]
    try rfl

/-! ## The statement -/

theorem toSSet_coprod_iso (X Y : TopCat) :
    Nonempty (TopCat.toSSet.obj (CategoryTheory.Limits.coprod X Y) ≅
      (TopCat.toSSet.obj X ⨿ TopCat.toSSet.obj Y)) := by
  have h1 : TopCat.toSSet.obj (CategoryTheory.Limits.coprod X Y) ≅
      TopCat.toSSet.obj (TopCat.of (↑X ⊕ ↑Y)) :=
    TopCat.toSSet.mapIso (coprodIso X Y)
  have h2 := IsColimit.coconePointUniqueUpToIso (sumCofan_isColimit X Y)
      (coprodIsCoprod (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y))
  exact ⟨h1.trans h2⟩

end Work.Bordism
