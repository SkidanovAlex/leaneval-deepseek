import Mathlib
import Submission.Work.Bordism.chainC_coprod_iso
import Submission.Work.Bordism.toSSet_coprod_iso
import Submission.Work.Cohomology.Pullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chain complex of a disjoint union splits off its two summands

`Work.Bordism.chainC_coprod_iso` shows that the singular chain complex of a disjoint union
`X ⊔ Y` of topological spaces is *isomorphic* to the biproduct `C_*(X) ⊞ C_*(Y)`.  For the
applications in this chapter (the Künneth-like splitting of homology and cohomology) one needs
the sharper statement that the two coproduct inclusions

`C_*(X) ⟶ C_*(X ⊔ Y)`,  `C_*(Y) ⟶ C_*(X ⊔ Y)`

are, up to that isomorphism, exactly the two biproduct inclusions — equivalently, that there are
retractions `p`, `q` which split the two summands off *and* are complementary:

`p ≫ i₁ = id`, `q ≫ i₂ = id`, `i₁ ≫ q = 0`, `i₂ ≫ p = 0`, `p ≫ i₁ + q ≫ i₂ = id`.

This is the content of `Work.Bordism.chainC_coprod_split` below.  Note that the splitting maps
`p`, `q` are *not* induced by continuous maps: the retraction `X ⊔ Y ⟶ X` collapsing `Y` to a
point restricts on `Y` to a constant map, whose chain map is not zero, whereas the projections of
the direct-sum decomposition kill the other summand.  The splitting therefore has to be built from
the direct-sum structure of the chain complexes, and this is what the file does.

The proof has three layers.

* `ssetChainC_coprod_split_aux` (the heart of the argument): for simplicial sets `A`, `B`, the
  canonical comparison isomorphism
  `chainC ℤ (A ⨿ B) ≅ chainC ℤ A ⊞ chainC ℤ B`
  built from the fact that `chainC ℤ` preserves colimits (as in
  `Work.Bordism.chainC_coprod_iso`) carries `chainC ℤ` of the two coproduct inclusions to the two
  biproduct inclusions.  The compatibility is read off from the defining equation of the colimit
  comparison isomorphisms (`ι_preservesColimitIso_hom_assoc`, `HasColimit.isoOfNatIso_ι_hom_assoc`,
  `IsColimit.comp_coconePointUniqueUpToIso_inv`) and from the components of `diagramIsoPair` being
  identities.

* `toSSetCoprodSplitIso_inl`, `toSSetCoprodSplitIso_inr`: the singular simplicial set of a
  disjoint union is the coproduct of the singular simplicial sets *in a way compatible with the
  inclusions* — the sharpening of `Work.Bordism.toSSet_coprod_iso` needed to transport the
  previous layer to topological spaces.

* `chainC_coprod_split_aux`: the two layers are composed, and the five required equations are then
  pure biproduct algebra, `p := e.hom ≫ biprod.fst`, `q := e.hom ≫ biprod.snd`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial

namespace Work.Bordism

noncomputable section

/-! ## The simplicial chain complex functor -/

/-- The simplicial chain complex with `ℤ`-coefficients, as a functor on simplicial sets.  This is
the functor underlying `Work.Cohomology.chainC ℤ`. -/
abbrev ssetChainC : SSet ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
  (SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

/-! ## The splitting at the level of simplicial sets -/

/-- **The coproduct comparison isomorphism is compatible with the inclusions.**

There is an isomorphism `chainC ℤ (A ⨿ B) ≅ chainC ℤ A ⊞ chainC ℤ B` which carries the chains of
the two coproduct inclusions to the two biproduct inclusions. -/
theorem ssetChainC_coprod_split_aux (A B : SSet) :
    ∃ E : ssetChainC.obj (A ⨿ B) ≅ (ssetChainC.obj A ⊞ ssetChainC.obj B),
      ssetChainC.map (coprod.inl : A ⟶ A ⨿ B) ≫ E.hom = biprod.inl ∧
      ssetChainC.map (coprod.inr : B ⟶ A ⨿ B) ≫ E.hom = biprod.inr := by
  -- the diagram `pair A B` and the fact that `chainC ℤ` preserves its colimit
  let K : Discrete WalkingPair ⥤ SSet := pair A B
  haveI hp : PreservesColimit K ssetChainC :=
    (Work.Bordism.chainC_preservesColimitsOfShape (J := Discrete WalkingPair)).preservesColimit
  -- the diagram `(G A, G B)` (spelled out, so that later rewrites match syntactically)
  let L : Discrete WalkingPair ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
    pair ((K ⋙ ssetChainC).obj ⟨WalkingPair.left⟩) ((K ⋙ ssetChainC).obj ⟨WalkingPair.right⟩)
  -- the three pieces of the comparison isomorphism: preservation of the colimit, the
  -- identification of the pair-diagram with `pair (G A) (G B)`, and the identification of the
  -- colimit of that diagram with the biproduct
  let e1 := preservesColimitIso ssetChainC K
  let e2 := HasColimit.isoOfNatIso (diagramIsoPair (K ⋙ ssetChainC))
  let e3 := (IsColimit.coconePointUniqueUpToIso
    (BinaryBiproduct.isColimit ((K ⋙ ssetChainC).obj ⟨WalkingPair.left⟩)
      ((K ⋙ ssetChainC).obj ⟨WalkingPair.right⟩))
    (colimit.isColimit L)).symm
  -- the last piece, identified with the biproduct inclusions
  have h4 : ∀ j : Discrete WalkingPair, colimit.ι L j ≫ e3.hom
      = (BinaryBiproduct.bicone ((K ⋙ ssetChainC).obj ⟨WalkingPair.left⟩)
          ((K ⋙ ssetChainC).obj ⟨WalkingPair.right⟩)).toCocone.ι.app j :=
    fun j => IsColimit.comp_coconePointUniqueUpToIso_inv
      (BinaryBiproduct.isColimit ((K ⋙ ssetChainC).obj ⟨WalkingPair.left⟩)
        ((K ⋙ ssetChainC).obj ⟨WalkingPair.right⟩))
      (colimit.isColimit L) j
  -- the middle piece acts as the identity on the two summands
  have h3l : (diagramIsoPair (K ⋙ ssetChainC)).hom.app ⟨WalkingPair.left⟩
      = 𝟙 ((K ⋙ ssetChainC).obj ⟨WalkingPair.left⟩) := rfl
  have h3r : (diagramIsoPair (K ⋙ ssetChainC)).hom.app ⟨WalkingPair.right⟩
      = 𝟙 ((K ⋙ ssetChainC).obj ⟨WalkingPair.right⟩) := rfl
  refine ⟨e1 ≪≫ e2 ≪≫ e3, ?_, ?_⟩
  · show ssetChainC.map (colimit.ι K ⟨WalkingPair.left⟩) ≫ e1.hom ≫ e2.hom ≫ e3.hom
      = biprod.inl
    rw [ι_preservesColimitIso_hom_assoc ssetChainC K ⟨WalkingPair.left⟩]
    rw [HasColimit.isoOfNatIso_ι_hom_assoc (diagramIsoPair (K ⋙ ssetChainC))
      ⟨WalkingPair.left⟩]
    rw [h3l, h4, Category.id_comp]
    rfl
  · show ssetChainC.map (colimit.ι K ⟨WalkingPair.right⟩) ≫ e1.hom ≫ e2.hom ≫ e3.hom
      = biprod.inr
    rw [ι_preservesColimitIso_hom_assoc ssetChainC K ⟨WalkingPair.right⟩]
    rw [HasColimit.isoOfNatIso_ι_hom_assoc (diagramIsoPair (K ⋙ ssetChainC))
      ⟨WalkingPair.right⟩]
    rw [h3r, h4, Category.id_comp]
    rfl

/-! ## The singular simplicial set of a disjoint union, compatibly with the inclusions -/

/-- The explicit isomorphism `toSSet (X ⨿ Y) ≅ toSSet X ⨿ toSSet Y` underlying
`Work.Bordism.toSSet_coprod_iso`: the identifications of the abstract coproduct with the concrete
disjoint union, and of the levelwise splitting with the coproduct of simplicial sets. -/
noncomputable def toSSetCoprodSplitIso (X Y : TopCat) :
    TopCat.toSSet.obj (X ⨿ Y) ≅ (TopCat.toSSet.obj X ⨿ TopCat.toSSet.obj Y) := by
  have h1 : TopCat.toSSet.obj (X ⨿ Y) ≅ TopCat.toSSet.obj (TopCat.of (↑X ⊕ ↑Y)) :=
    TopCat.toSSet.mapIso (Work.Bordism.coprodIso X Y)
  have h2 := IsColimit.coconePointUniqueUpToIso (Work.Bordism.sumCofan_isColimit X Y)
    (coprodIsCoprod (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y))
  exact h1.trans h2

/-- The isomorphism `toSSetCoprodSplitIso` is compatible with the first coproduct inclusion. -/
lemma toSSetCoprodSplitIso_inl (X Y : TopCat) :
    TopCat.toSSet.map (coprod.inl : X ⟶ X ⨿ Y) ≫ (toSSetCoprodSplitIso X Y).hom
      = (coprod.inl : TopCat.toSSet.obj X ⟶
          TopCat.toSSet.obj X ⨿ TopCat.toSSet.obj Y) := by
  -- the two inclusions of the concrete disjoint union correspond to each other
  have hcop : (coprod.inl : X ⟶ X ⨿ Y) ≫ (Work.Bordism.coprodIso X Y).hom
      = TopCat.ofHom (⟨Sum.inl, continuous_inl⟩ : C(↑X, ↑X ⊕ ↑Y)) := by
    show (colimit.cocone (pair X Y)).ι.app ⟨WalkingPair.left⟩ ≫
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (pair X Y))
        (TopCat.binaryCofanIsColimit X Y)).hom = _
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    rfl
  -- the cofan of the disjoint union is compatible with the coproduct of simplicial sets
  have hcpu : (Work.Bordism.sumCofan X Y).inl ≫
      (IsColimit.coconePointUniqueUpToIso (Work.Bordism.sumCofan_isColimit X Y)
        (coprodIsCoprod (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y))).hom = coprod.inl := by
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    rfl
  show TopCat.toSSet.map (coprod.inl : X ⟶ X ⨿ Y) ≫
      (TopCat.toSSet.mapIso (Work.Bordism.coprodIso X Y) ≪≫
        IsColimit.coconePointUniqueUpToIso (Work.Bordism.sumCofan_isColimit X Y)
          (coprodIsCoprod (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y))).hom = coprod.inl
  rw [Iso.trans_hom]
  rw [← Category.assoc, Functor.mapIso_hom, ← Functor.map_comp, hcop]
  exact hcpu

/-- The isomorphism `toSSetCoprodSplitIso` is compatible with the second coproduct inclusion. -/
lemma toSSetCoprodSplitIso_inr (X Y : TopCat) :
    TopCat.toSSet.map (coprod.inr : Y ⟶ X ⨿ Y) ≫ (toSSetCoprodSplitIso X Y).hom
      = (coprod.inr : TopCat.toSSet.obj Y ⟶
          TopCat.toSSet.obj X ⨿ TopCat.toSSet.obj Y) := by
  have hcop : (coprod.inr : Y ⟶ X ⨿ Y) ≫ (Work.Bordism.coprodIso X Y).hom
      = TopCat.ofHom (⟨Sum.inr, continuous_inr⟩ : C(↑Y, ↑X ⊕ ↑Y)) := by
    show (colimit.cocone (pair X Y)).ι.app ⟨WalkingPair.right⟩ ≫
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (pair X Y))
        (TopCat.binaryCofanIsColimit X Y)).hom = _
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    rfl
  have hcpu : (Work.Bordism.sumCofan X Y).inr ≫
      (IsColimit.coconePointUniqueUpToIso (Work.Bordism.sumCofan_isColimit X Y)
        (coprodIsCoprod (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y))).hom = coprod.inr := by
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    rfl
  show TopCat.toSSet.map (coprod.inr : Y ⟶ X ⨿ Y) ≫
      (TopCat.toSSet.mapIso (Work.Bordism.coprodIso X Y) ≪≫
        IsColimit.coconePointUniqueUpToIso (Work.Bordism.sumCofan_isColimit X Y)
          (coprodIsCoprod (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y))).hom = coprod.inr
  rw [Iso.trans_hom]
  rw [← Category.assoc, Functor.mapIso_hom, ← Functor.map_comp, hcop]
  exact hcpu

/-! ## The splitting for topological spaces -/

/-- The chain-level coproduct comparison isomorphism is compatible with the chain maps induced by
the two coproduct inclusions. -/
theorem chainC_coprod_split_aux (X Y : TopCat) :
    ∃ E : Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (X ⨿ Y)) ≅
        (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X) ⊞
          Work.Cohomology.chainC ℤ (TopCat.toSSet.obj Y)),
      Work.Cohomology.chainMap ℤ X (X ⨿ Y) coprod.inl ≫ E.hom = biprod.inl ∧
      Work.Cohomology.chainMap ℤ Y (X ⨿ Y) coprod.inr ≫ E.hom = biprod.inr := by
  obtain ⟨E', h1, h2⟩ := ssetChainC_coprod_split_aux
    (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
  refine ⟨Functor.mapIso ssetChainC (toSSetCoprodSplitIso X Y) ≪≫ E', ?_, ?_⟩
  · show ssetChainC.map (TopCat.toSSet.map (coprod.inl : X ⟶ X ⨿ Y)) ≫
      (Functor.mapIso ssetChainC (toSSetCoprodSplitIso X Y) ≪≫ E').hom = biprod.inl
    rw [Iso.trans_hom]
    rw [← Category.assoc, Functor.mapIso_hom, ← Functor.map_comp, toSSetCoprodSplitIso_inl]
    exact h1
  · show ssetChainC.map (TopCat.toSSet.map (coprod.inr : Y ⟶ X ⨿ Y)) ≫
      (Functor.mapIso ssetChainC (toSSetCoprodSplitIso X Y) ≪≫ E').hom = biprod.inr
    rw [Iso.trans_hom]
    rw [← Category.assoc, Functor.mapIso_hom, ← Functor.map_comp, toSSetCoprodSplitIso_inr]
    exact h2

/-! ## The statement -/

theorem chainC_coprod_split (X Y : TopCat) :
    ∃ p : Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (CategoryTheory.Limits.coprod X Y)) ⟶
          Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X),
    ∃ q : Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (CategoryTheory.Limits.coprod X Y)) ⟶
          Work.Cohomology.chainC ℤ (TopCat.toSSet.obj Y),
      (CategoryTheory.CategoryStruct.comp
          (Work.Cohomology.chainMap ℤ X (CategoryTheory.Limits.coprod X Y)
            CategoryTheory.Limits.coprod.inl) p
        = CategoryTheory.CategoryStruct.id (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X))) ∧
      (CategoryTheory.CategoryStruct.comp
          (Work.Cohomology.chainMap ℤ Y (CategoryTheory.Limits.coprod X Y)
            CategoryTheory.Limits.coprod.inr) q
        = CategoryTheory.CategoryStruct.id (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj Y))) ∧
      (CategoryTheory.CategoryStruct.comp
          (Work.Cohomology.chainMap ℤ X (CategoryTheory.Limits.coprod X Y)
            CategoryTheory.Limits.coprod.inl) q = 0) ∧
      (CategoryTheory.CategoryStruct.comp
          (Work.Cohomology.chainMap ℤ Y (CategoryTheory.Limits.coprod X Y)
            CategoryTheory.Limits.coprod.inr) p = 0) ∧
      (CategoryTheory.CategoryStruct.comp p
          (Work.Cohomology.chainMap ℤ X (CategoryTheory.Limits.coprod X Y)
            CategoryTheory.Limits.coprod.inl)
        + CategoryTheory.CategoryStruct.comp q
          (Work.Cohomology.chainMap ℤ Y (CategoryTheory.Limits.coprod X Y)
            CategoryTheory.Limits.coprod.inr)
        = CategoryTheory.CategoryStruct.id
            (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (CategoryTheory.Limits.coprod X Y)))) := by
  obtain ⟨E, h1, h2⟩ := chainC_coprod_split_aux X Y
  refine ⟨E.hom ≫ biprod.fst, E.hom ≫ biprod.snd, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, h1]
    exact biprod.inl_fst
  · rw [← Category.assoc, h2]
    exact biprod.inr_snd
  · rw [← Category.assoc, h1]
    exact biprod.inl_snd
  · rw [← Category.assoc, h2]
    exact biprod.inr_fst
  · -- the two projections of the direct sum decomposition are complementary
    have h5 : biprod.fst ≫ Work.Cohomology.chainMap ℤ X (X ⨿ Y) coprod.inl
        + biprod.snd ≫ Work.Cohomology.chainMap ℤ Y (X ⨿ Y) coprod.inr = E.inv := by
      have hd : (biprod.fst ≫ Work.Cohomology.chainMap ℤ X (X ⨿ Y) coprod.inl
            + biprod.snd ≫ Work.Cohomology.chainMap ℤ Y (X ⨿ Y) coprod.inr) ≫ E.hom
          = 𝟙 _ := by
        rw [Preadditive.add_comp, Category.assoc, Category.assoc, h1, h2]
        exact biprod.total
      calc biprod.fst ≫ Work.Cohomology.chainMap ℤ X (X ⨿ Y) coprod.inl
            + biprod.snd ≫ Work.Cohomology.chainMap ℤ Y (X ⨿ Y) coprod.inr
          = (biprod.fst ≫ Work.Cohomology.chainMap ℤ X (X ⨿ Y) coprod.inl
              + biprod.snd ≫ Work.Cohomology.chainMap ℤ Y (X ⨿ Y) coprod.inr) ≫ 𝟙 _ :=
            (Category.comp_id _).symm
        _ = (biprod.fst ≫ Work.Cohomology.chainMap ℤ X (X ⨿ Y) coprod.inl
              + biprod.snd ≫ Work.Cohomology.chainMap ℤ Y (X ⨿ Y) coprod.inr) ≫
                (E.hom ≫ E.inv) := by rw [Iso.hom_inv_id]
        _ = ((biprod.fst ≫ Work.Cohomology.chainMap ℤ X (X ⨿ Y) coprod.inl
              + biprod.snd ≫ Work.Cohomology.chainMap ℤ Y (X ⨿ Y) coprod.inr) ≫ E.hom) ≫
                E.inv := by rw [Category.assoc]
        _ = 𝟙 _ ≫ E.inv := by rw [hd]
        _ = E.inv := Category.id_comp _
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add]
    exact (congrArg (fun z => E.hom ≫ z) h5).trans (Iso.hom_inv_id E)

end

end Work.Bordism
