import Mathlib
import Submission.Work.CWIND.GClass.CondSigma
import Submission.Work.CWIND.GClass.condOf_sigma

/-!
# CWIND/GClass — the light condensed set of a disjoint union of clopen pieces

Let `Zt` be a topological space presented as a pairwise disjoint union of open pieces
`ι j : Z j ⟶ Zt` (with `⋃ j, range (ι j) = univ`).  This file proves that the induced cofan

`topCatToLightCondSet.obj Zt ← ∐ j, topCatToLightCondSet.obj (Z j)`

is a colimit in `LightCondSet`, i.e. that the light condensed set of `Zt` is the coproduct of the
light condensed sets of the pieces (`Work.CWIND.GClass.DUS`).

The proof uses the gluing machinery of `Submission/Work/CWIND/GClass/CondSigma.lean`
(`glueSec`, `glueSec_spec`, `glue_unique`): for a cocone with point `W` and legs `φ j`, the induced
map `Zt_cond ⟶ W` is the glued section, and its naturality is reduced to `glue_unique`.
-/

noncomputable section

set_option autoImplicit false

namespace Work.CWIND.GClass

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open Opposite

variable {J : Type} {Zt : TopCat.{0}} {Z : J → TopCat.{0}} {ι : ∀ j, Z j ⟶ Zt}

/-! ## A functoriality helper for sections of a light condensed set -/

/-- Functoriality of the action on sections of a light condensed set, in the form of an equation
between elements of `W(T)`. -/
lemma Wmap_comp_apply (W : LightCondSet.{0}) {T U V : LightProfinite.{0}} (h : U ⟶ T)
    (g : V ⟶ U) (y : W.obj.obj (op T)) :
    W.obj.map g.op (W.obj.map h.op y) = W.obj.map (g ≫ h).op y := by
  rw [show (g ≫ h).op = h.op ≫ g.op from op_comp, Functor.map_comp]
  rfl

/-! ## Naturality of the glued section -/

/-- The glued section `glueSec` is natural in the light profinite set. -/
theorem glueSec_naturality
    (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    (hdisj : Pairwise fun j k => Disjoint (Set.range ⇑(ι j)) (Set.range ⇑(ι k)))
    (hcov : (⋃ j, Set.range ⇑(ι j)) = Set.univ)
    (W : LightCondSet.{0}) (φ : ∀ j, topCatToLightCondSet.obj (Z j) ⟶ W)
    {S S' : LightProfinite.{0}} (v : S' ⟶ S) (f : C(↥S, ↥Zt)) :
    W.obj.map v.op (glueSec hopen hdisj hcov W φ f) =
      glueSec hopen hdisj hcov W φ (f.comp v.hom.hom) := by
  classical
  refine glue_unique hopen hdisj hcov W φ (f.comp v.hom.hom) ?_
    (fun k => glueSec_spec hopen hdisj hcov W φ (f.comp v.hom.hom) k)
  intro k
  haveI : CompactSpace ↥(cpiece (ι := ι) (f.comp v.hom.hom) k) :=
    isCompact_iff_compactSpace.mp
      (cpiece_isClopen hopen hdisj hcov (f.comp v.hom.hom) k).1.isCompact
  haveI : CompactSpace ↥(cpiece (ι := ι) f k) :=
    isCompact_iff_compactSpace.mp (cpiece_isClopen hopen hdisj hcov f k).1.isCompact
  -- the inclusion of the piece of `f ∘ v` into the piece of `f`
  have hcont : Continuous fun a : ↥(clopenLP S' (cpiece (ι := ι) (f.comp v.hom.hom) k)
        (cpiece_isClopen hopen hdisj hcov (f.comp v.hom.hom) k)) =>
      (⟨v a.1, a.2⟩ : ↥(clopenLP S (cpiece (ι := ι) f k)
        (cpiece_isClopen hopen hdisj hcov f k))) :=
    Continuous.subtype_mk ((ContinuousMap.continuous v.hom.hom).comp continuous_subtype_val) _
  set w : clopenLP S' (cpiece (ι := ι) (f.comp v.hom.hom) k)
        (cpiece_isClopen hopen hdisj hcov (f.comp v.hom.hom) k) ⟶
      clopenLP S (cpiece (ι := ι) f k) (cpiece_isClopen hopen hdisj hcov f k) :=
    CompHausLike.ofHom _ (⟨fun a => ⟨v a.1, a.2⟩, hcont⟩ :
      C(↥(clopenLP S' (cpiece (ι := ι) (f.comp v.hom.hom) k)
          (cpiece_isClopen hopen hdisj hcov (f.comp v.hom.hom) k)),
        ↥(clopenLP S (cpiece (ι := ι) f k) (cpiece_isClopen hopen hdisj hcov f k)))) with hwdef
  have hw : clopenIncl S' (cpiece (ι := ι) (f.comp v.hom.hom) k)
        (cpiece_isClopen hopen hdisj hcov (f.comp v.hom.hom) k) ≫ v =
      w ≫ clopenIncl S (cpiece (ι := ι) f k) (cpiece_isClopen hopen hdisj hcov f k) := by
    apply ConcreteCategory.hom_ext
    intro a
    simp only [hwdef, CompHausLike.coe_comp, Function.comp_apply]
    rfl
  -- the two restrictions of `pieceRestrict` agree
  have hpiece : (pieceRestrict hopen hdisj hcov f k).comp w.hom.hom =
      pieceRestrict hopen hdisj hcov (f.comp v.hom.hom) k := by
    refine condCorestrict_unique hopen ((f.comp v.hom.hom).comp
      (pieceIncl hopen hdisj hcov (f.comp v.hom.hom) k)) k (fun a => a.2) _ ?_
    show (ι k).hom.comp ((pieceRestrict hopen hdisj hcov f k).comp w.hom.hom) = _
    rw [← ContinuousMap.comp_assoc,
      show (ι k).hom.comp (pieceRestrict hopen hdisj hcov f k) =
        f.comp (pieceIncl hopen hdisj hcov f k) from
        condCorestrict_spec hopen (f.comp (pieceIncl hopen hdisj hcov f k)) k (fun x => x.2)]
    apply ContinuousMap.ext
    intro a
    simp only [hwdef, ContinuousMap.comp_apply]
    rfl
  calc W.obj.map (clopenIncl S' (cpiece (ι := ι) (f.comp v.hom.hom) k)
          (cpiece_isClopen hopen hdisj hcov (f.comp v.hom.hom) k)).op
        (W.obj.map v.op (glueSec hopen hdisj hcov W φ f))
      = W.obj.map ((clopenIncl S' (cpiece (ι := ι) (f.comp v.hom.hom) k)
          (cpiece_isClopen hopen hdisj hcov (f.comp v.hom.hom) k)) ≫ v).op
          (glueSec hopen hdisj hcov W φ f) := Wmap_comp_apply W v _ _
    _ = W.obj.map (w ≫ clopenIncl S (cpiece (ι := ι) f k)
          (cpiece_isClopen hopen hdisj hcov f k)).op (glueSec hopen hdisj hcov W φ f) := by
        rw [hw]
    _ = W.obj.map w.op (W.obj.map (clopenIncl S (cpiece (ι := ι) f k)
          (cpiece_isClopen hopen hdisj hcov f k)).op (glueSec hopen hdisj hcov W φ f)) :=
        (Wmap_comp_apply W _ _ _).symm
    _ = W.obj.map w.op ((φ k).hom.app (op (clopenLP S (cpiece (ι := ι) f k)
          (cpiece_isClopen hopen hdisj hcov f k)))
          (pieceRestrict hopen hdisj hcov f k)) := by
        rw [glueSec_spec hopen hdisj hcov W φ f k]
    _ = (φ k).hom.app (op (clopenLP S' (cpiece (ι := ι) (f.comp v.hom.hom) k)
          (cpiece_isClopen hopen hdisj hcov (f.comp v.hom.hom) k)))
        ((topCatToLightCondSet.obj (Z k)).obj.map w.op
          (pieceRestrict hopen hdisj hcov f k)) :=
        (NatTrans.naturality_apply (φ k).hom w.op (pieceRestrict hopen hdisj hcov f k)).symm
    _ = (φ k).hom.app (op (clopenLP S' (cpiece (ι := ι) (f.comp v.hom.hom) k)
          (cpiece_isClopen hopen hdisj hcov (f.comp v.hom.hom) k)))
        (pieceRestrict hopen hdisj hcov (f.comp v.hom.hom) k) := by
        rw [show (topCatToLightCondSet.obj (Z k)).obj.map w.op
              (pieceRestrict hopen hdisj hcov f k) =
            pieceRestrict hopen hdisj hcov (f.comp v.hom.hom) k from hpiece]

/-! ## The glued section of a map lying in a single piece -/

/-- If `f = ι j ∘ g` lies in the `j`-th piece, the glued section of `f` is the image of `g` under
the leg `φ j`. -/
theorem glueSec_eq_app_of_factors
    (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    (hdisj : Pairwise fun j k => Disjoint (Set.range ⇑(ι j)) (Set.range ⇑(ι k)))
    (hcov : (⋃ j, Set.range ⇑(ι j)) = Set.univ)
    (W : LightCondSet.{0}) (φ : ∀ j, topCatToLightCondSet.obj (Z j) ⟶ W)
    {S : LightProfinite.{0}} (j : J) (g : C(↥S, ↥(Z j))) :
    glueSec hopen hdisj hcov W φ ((ι j).hom.comp g) = (φ j).hom.app (op S) g := by
  classical
  set f : C(↥S, ↥Zt) := (ι j).hom.comp g with hf
  change glueSec hopen hdisj hcov W φ f = (φ j).hom.app (op S) g
  refine glue_unique hopen hdisj hcov W φ f ?_ ?_
  · intro k
    exact glueSec_spec hopen hdisj hcov W φ f k
  · intro k
    by_cases hk : k = j
    · rw [hk]
      have hnat := (NatTrans.naturality_apply (φ j).hom
        (clopenIncl S (cpiece (ι := ι) f j) (cpiece_isClopen hopen hdisj hcov f j)).op g).symm
      rw [hnat]
      congr 1
      exact condCorestrict_unique hopen (f.comp (pieceIncl hopen hdisj hcov f j)) j
        (fun x => x.2)
        (g.comp (clopenIncl S (cpiece (ι := ι) f j)
          (cpiece_isClopen hopen hdisj hcov f j)).hom.hom) (by ext s; rfl)
    · have hne : j ≠ k := fun h => hk h.symm
      have hempty : cpiece (ι := ι) f k = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr fun s hs => ?_
        obtain ⟨z, hz⟩ := hs
        refine Set.disjoint_left.mp (hdisj hne)
          (show (ι j).hom (g s) ∈ Set.range ⇑(ι j) from ⟨g s, rfl⟩) ?_
        exact ⟨z, by rw [hz, hf]; rfl⟩
      have hE : IsEmpty ↥(clopenLP S (cpiece (ι := ι) f k)
          (cpiece_isClopen hopen hdisj hcov f k)) := by
        rw [show (clopenLP S (cpiece (ι := ι) f k)
            (cpiece_isClopen hopen hdisj hcov f k) : Type) = ↥(cpiece (ι := ι) f k) from rfl,
          hempty]
        exact ⟨fun x => x.2⟩
      have hsub : Subsingleton (W.obj.obj (op (clopenLP S (cpiece (ι := ι) f k)
          (cpiece_isClopen hopen hdisj hcov f k)))) := subsingleton_of_isEmpty W hE
      exact Subsingleton.elim _ _

/-! ## Uniqueness of the induced map -/

/-- A map `Zt_cond ⟶ W` which agrees with the legs `φ j` after precomposition with the inclusions
`(ι j)_cond` agrees with the glued section on every section. -/
theorem glueSec_eq_of_legs
    (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    (hdisj : Pairwise fun j k => Disjoint (Set.range ⇑(ι j)) (Set.range ⇑(ι k)))
    (hcov : (⋃ j, Set.range ⇑(ι j)) = Set.univ)
    (W : LightCondSet.{0}) (φ : ∀ j, topCatToLightCondSet.obj (Z j) ⟶ W)
    (m : topCatToLightCondSet.obj Zt ⟶ W)
    (hm : ∀ j, CategoryTheory.CategoryStruct.comp (topCatToLightCondSet.map (ι j)) m = φ j)
    {S : LightProfinite.{0}} (x : C(↥S, ↥Zt)) :
    m.hom.app (op S) x = glueSec hopen hdisj hcov W φ x := by
  classical
  obtain ⟨F, hF⟩ := exists_finset_cover hopen hdisj hcov x
  have hA : ∀ i : {j : J // j ∈ F}, IsClopen (cpiece (ι := ι) x i.1) :=
    fun i => cpiece_isClopen hopen hdisj hcov x i.1
  have hdisj' : Pairwise fun i k : {j : J // j ∈ F} =>
      Disjoint (cpiece (ι := ι) x i.1) (cpiece (ι := ι) x k.1) := by
    intro i k hik
    exact (hdisj (fun h => hik (Subtype.ext h))).preimage x
  have hcov' : (⋃ i : {j : J // j ∈ F}, cpiece (ι := ι) x i.1) = Set.univ := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨j, hjF, hxj⟩ := hF s
    exact ⟨⟨j, hjF⟩, hxj⟩
  have hinj := (restrict_bijective_of_clopen_partition
    (fun i : {j : J // j ∈ F} => cpiece (ι := ι) x i.1) hA hdisj' hcov' W).1
  apply hinj
  funext i
  have hnat := NatTrans.naturality_apply m.hom
    (clopenIncl S (cpiece (ι := ι) x i.1) (hA i)).op x
  have hcx : (topCatToLightCondSet.obj Zt).obj.map
        (clopenIncl S (cpiece (ι := ι) x i.1) (hA i)).op x =
      (topCatToLightCondSet.map (ι i.1)).hom.app
        (op (clopenLP S (cpiece (ι := ι) x i.1) (hA i)))
        (pieceRestrict hopen hdisj hcov x i.1) := by
    rw [show (topCatToLightCondSet.obj Zt).obj.map
        (clopenIncl S (cpiece (ι := ι) x i.1) (hA i)).op x =
        x.comp (clopenIncl S (cpiece (ι := ι) x i.1) (hA i)).hom.hom from rfl]
    exact (condCorestrict_spec hopen (x.comp (pieceIncl hopen hdisj hcov x i.1)) i.1
      (fun a => a.2)).symm
  have hcomp : m.hom.app (op (clopenLP S (cpiece (ι := ι) x i.1) (hA i)))
        ((topCatToLightCondSet.map (ι i.1)).hom.app
          (op (clopenLP S (cpiece (ι := ι) x i.1) (hA i)))
          (pieceRestrict hopen hdisj hcov x i.1)) =
      (φ i.1).hom.app (op (clopenLP S (cpiece (ι := ι) x i.1) (hA i)))
        (pieceRestrict hopen hdisj hcov x i.1) := by
    show ((CategoryTheory.CategoryStruct.comp (topCatToLightCondSet.map (ι i.1)) m).hom.app
        (op (clopenLP S (cpiece (ι := ι) x i.1) (hA i))))
        (pieceRestrict hopen hdisj hcov x i.1) = _
    rw [hm i.1]
  calc W.obj.map (clopenIncl S (cpiece (ι := ι) x i.1) (hA i)).op (m.hom.app (op S) x)
      = m.hom.app (op (clopenLP S (cpiece (ι := ι) x i.1) (hA i)))
          ((topCatToLightCondSet.obj Zt).obj.map
            (clopenIncl S (cpiece (ι := ι) x i.1) (hA i)).op x) := hnat.symm
    _ = m.hom.app (op (clopenLP S (cpiece (ι := ι) x i.1) (hA i)))
          ((topCatToLightCondSet.map (ι i.1)).hom.app
            (op (clopenLP S (cpiece (ι := ι) x i.1) (hA i)))
            (pieceRestrict hopen hdisj hcov x i.1)) := by rw [hcx]
    _ = (φ i.1).hom.app (op (clopenLP S (cpiece (ι := ι) x i.1) (hA i)))
          (pieceRestrict hopen hdisj hcov x i.1) := hcomp
    _ = W.obj.map (clopenIncl S (cpiece (ι := ι) x i.1) (hA i)).op
          (glueSec hopen hdisj hcov W φ x) :=
        (glueSec_spec hopen hdisj hcov W φ x i.1).symm

/-! ## The induced morphism `Zt_cond ⟶ W` -/

/-- The glued section, as a function on the sections of the light condensed set of `Zt`. -/
noncomputable def glueFun (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    (hdisj : Pairwise fun j k => Disjoint (Set.range ⇑(ι j)) (Set.range ⇑(ι k)))
    (hcov : (⋃ j, Set.range ⇑(ι j)) = Set.univ)
    (W : LightCondSet.{0}) (φ : ∀ j, topCatToLightCondSet.obj (Z j) ⟶ W)
    (X : LightProfinite.{0}ᵒᵖ) (f : (topCatToLightCondSet.obj Zt).obj.obj X) : W.obj.obj X :=
  glueSec hopen hdisj hcov W φ (show C(↥(unop X), ↥Zt) from f)

/-- The morphism `Zt_cond ⟶ W` gluing the legs `φ`. -/
noncomputable def glueNat (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    (hdisj : Pairwise fun j k => Disjoint (Set.range ⇑(ι j)) (Set.range ⇑(ι k)))
    (hcov : (⋃ j, Set.range ⇑(ι j)) = Set.univ)
    (W : LightCondSet.{0}) (φ : ∀ j, topCatToLightCondSet.obj (Z j) ⟶ W) :
    topCatToLightCondSet.obj Zt ⟶ W :=
  ObjectProperty.homMk
    { app := fun X => ConcreteCategory.ofHom ⟨glueFun hopen hdisj hcov W φ X⟩
      naturality := by
        rintro ⟨S⟩ ⟨S'⟩ g
        rw [← Quiver.Hom.op_unop g]
        ext f
        exact (glueSec_naturality hopen hdisj hcov W φ (g.unop)
          (show C(↥S, ↥Zt) from f)).symm }

lemma glueNat_app (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    (hdisj : Pairwise fun j k => Disjoint (Set.range ⇑(ι j)) (Set.range ⇑(ι k)))
    (hcov : (⋃ j, Set.range ⇑(ι j)) = Set.univ)
    (W : LightCondSet.{0}) (φ : ∀ j, topCatToLightCondSet.obj (Z j) ⟶ W)
    (S : LightProfinite.{0}) (f : (topCatToLightCondSet.obj Zt).obj.obj (op S)) :
    (glueNat hopen hdisj hcov W φ).hom.app (op S) f = glueSec hopen hdisj hcov W φ f := rfl

/-- Two morphisms of light condensed sets agreeing on all sections over light profinite sets are
equal. -/
lemma sheaf_hom_ext_sections {F G : LightCondSet.{0}} (m m' : F ⟶ G)
    (h : ∀ (S : LightProfinite.{0}) (x : F.obj.obj (op S)),
      m.hom.app (op S) x = m'.hom.app (op S) x) : m = m' := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext X
  cases X with
  | op S => ext x; exact h S x

/-- The glued morphism restricts to the given legs. -/
lemma glueNat_comp_map (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    (hdisj : Pairwise fun j k => Disjoint (Set.range ⇑(ι j)) (Set.range ⇑(ι k)))
    (hcov : (⋃ j, Set.range ⇑(ι j)) = Set.univ)
    (W : LightCondSet.{0}) (φ : ∀ j, topCatToLightCondSet.obj (Z j) ⟶ W) (j : J) :
    topCatToLightCondSet.map (ι j) ≫ glueNat hopen hdisj hcov W φ = φ j := by
  apply sheaf_hom_ext_sections
  intro S x
  rw [show ((topCatToLightCondSet.map (ι j) ≫ glueNat hopen hdisj hcov W φ).hom.app
      (op S)) x =
      (glueNat hopen hdisj hcov W φ).hom.app (op S)
        ((topCatToLightCondSet.map (ι j)).hom.app (op S) x) from rfl]
  rw [glueNat_app]
  exact glueSec_eq_app_of_factors hopen hdisj hcov W φ j x

/-- **The light condensed set of a disjoint union of clopen pieces is the coproduct of the
pieces.** -/
theorem DUS {J : Type} {Zt : TopCat.{0}} (Z : J → TopCat.{0}) (ι : ∀ j, Z j ⟶ Zt)
    (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    (hdisj : Pairwise fun j k => Disjoint (Set.range ⇑(ι j)) (Set.range ⇑(ι k)))
    (hcov : (⋃ j, Set.range ⇑(ι j)) = Set.univ) :
    Nonempty (CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofan.mk
      (topCatToLightCondSet.obj Zt) (fun j => topCatToLightCondSet.map (ι j)))) := by
  classical
  refine ⟨IsColimit.mk
    (fun s => glueNat hopen hdisj hcov s.pt (fun j => s.ι.app (Discrete.mk j))) ?_ ?_⟩
  · intro s j
    rcases j with ⟨j⟩
    rw [Cofan.mk_ι_app]
    exact glueNat_comp_map hopen hdisj hcov s.pt (fun j => s.ι.app (Discrete.mk j)) j
  · intro s m hm
    apply sheaf_hom_ext_sections
    intro S x
    rw [glueNat_app]
    exact glueSec_eq_of_legs hopen hdisj hcov s.pt
      (fun j => s.ι.app (Discrete.mk j)) m
      (fun j => by
        have h := hm (Discrete.mk j)
        simpa only [Cofan.mk_ι_app] using h) x

end Work.CWIND.GClass
