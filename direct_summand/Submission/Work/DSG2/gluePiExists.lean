import Mathlib
import Submission.Work.DSG2.Setup
import Submission.Work.DSG2.phiiCompJ
import Submission.Work.DSG2.piiCompF
import Submission.Work.DSG2.surjective_pi
import Submission.Work.DSG2.eq_of_isSchemeTheoreticallyDominant
import Submission.Work.DSG2.isSchemeTheoreticallyDominant_toImage
import Submission.Work.DSG2.isSchemeTheoreticallyDominant_lift_qc

/-!
# DSG2: the morphism `π : X' ⟶ X` of Chow's lemma is well defined

For Chow data `D` the pieces `Vi D i ⊆ Z D` cover the open subscheme
`X' D = ⨆ i, Vi D i`, and the maps `pii D i : Vi D i ⟶ X` glue to a single morphism
`X' D ⟶ X`.  This file proves

* `Work.DSG2.glueMorphisms_opens` — a general gluing lemma: morphisms out of the members of an
  open cover of a scheme which agree on the intersections glue to a morphism out of the union;
* `Work.DSG2.range_jU_toImage_subset_Vi` — the scheme-theoretic image `Z` of `jU` is contained in
  each piece `Vi D i`, so that `U0` maps to `Vi D i` (and hence to any intersection of pieces);
* `Work.DSG2.phii_lift_comp` / `Work.DSG2.pii_lift_comp` — on `U0` the map `Vi D i ⟶ U i ⊆ X` is
  the canonical inclusion `U0 ⊆ U i ⊆ X`;
* `Work.DSG2.pii_lift_comp_le` — the same statement for the restriction to an intersection
  `Vi D i ⊓ Vi D j`;

and then assembles them into `Work.DSG2.gluePiExists` using the fact that two morphisms
`Vi i ⊓ Vi j ⟶ X` over the separated `f : X ⟶ Spec A` which agree after a scheme-theoretically
dominant morphism (here `U0 ⟶ Vi i ⊓ Vi j`) are equal.
-/

open CategoryTheory AlgebraicGeometry Limits

set_option maxHeartbeats 1000000

universe u

namespace Work.DSG2

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}

/-- The scheme-theoretic image `Z` of `jU` is contained in each piece `Vi D i`:
the morphism `jU.toImage : U0 ⟶ Z` factors through the open subscheme `Vi D i`.

Indeed `jU.toImage ≫ pi i = (U0 ↪ U i) ≫ (j i).toImage ≫ eUi.hom ≫ Wi.ι`, which lands in the
open image `Wi` of the immersion `j i`, and `Vi i = pi i ⁻¹ᵁ Wi` is the preimage of `Wi`. -/
theorem range_jU_toImage_subset_Vi (D : ChowSetup A X f) (i : Fin D.m) :
    Set.range ⇑(D.jU.toImage) ⊆ Set.range ⇑((ChowSetup.Vi D i).ι) := by
  -- `jU.toImage ≫ qi i = (U0 ↪ U i) ≫ j i`
  have hqi' : D.jU.toImage ≫ ChowSetup.qi D i = X.homOfLE (D.hU0le i) ≫ D.j i := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι D.jU, D.jU_proj i]
  -- the composite `U0 ⟶ Wi` whose composite with `Wi.ι` is `jU.toImage ≫ pi i`
  have hui : X.homOfLE (D.hU0le i) ≫ (ChowSetup.eUi D i).hom ≫ (ChowSetup.Wi D i).ι
      = D.jU.toImage ≫ ChowSetup.pi D i := by
    rw [ChowSetup.eUi_hom_ι D i]
    refine (cancel_mono (ChowSetup.ZiIota D i)).mp ?_
    rw [Category.assoc, Category.assoc, Scheme.Hom.toImage_imageι (D.j i),
      ChowSetup.pi_spec D i, hqi']
  -- `Vi i` is the pullback of `pi i` along `Wi.ι`
  have hpb : IsPullback (ChowSetup.pi D i ∣_ ChowSetup.Wi D i)
      (ChowSetup.Vi D i).ι (ChowSetup.Wi D i).ι (ChowSetup.pi D i) :=
    isPullback_morphismRestrict _ _
  let L : ((D.U0 : X.Opens) : Scheme.{u}) ⟶ ((ChowSetup.Vi D i) : Scheme.{u}) :=
    hpb.lift (X.homOfLE (D.hU0le i) ≫ (ChowSetup.eUi D i).hom) D.jU.toImage hui
  have hL : L ≫ (ChowSetup.Vi D i).ι = D.jU.toImage := hpb.lift_snd _ _ hui
  rw [← hL]
  rw [show ⇑(L ≫ (ChowSetup.Vi D i).ι) = ⇑((ChowSetup.Vi D i).ι) ∘ ⇑L
      from funext fun x => Scheme.Hom.comp_apply L _ x]
  rw [Set.range_comp]
  exact Set.image_subset_range _ _

/-- If `s : T ⟶ Vi D i` is a lift of `t ≫ jU.toImage : T ⟶ Z` along `(Vi D i).ι`, then
`s ≫ phii D i : T ⟶ U i` is the morphism `t ≫ (U0 ↪ U i)` induced by `hU0le i`. -/
theorem phii_lift_comp (D : ChowSetup A X f) (i : Fin D.m) {T : Scheme.{u}}
    {t : T ⟶ ((D.U0 : X.Opens) : Scheme.{u})}
    {s : T ⟶ ((ChowSetup.Vi D i) : Scheme.{u})}
    (hs : s ≫ (ChowSetup.Vi D i).ι = t ≫ D.jU.toImage) :
    s ≫ ChowSetup.phii D i = t ≫ X.homOfLE (D.hU0le i) := by
  haveI : IsImmersion (D.j i) := D.hjImm i
  refine (cancel_mono (D.j i)).mp ?_
  simp only [Category.assoc]
  rw [phiiCompJ D i]
  rw [← Category.assoc, hs, Category.assoc]
  have hqi : D.jU.toImage ≫ D.jU.imageι ≫ D.p i = X.homOfLE (D.hU0le i) ≫ D.j i := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι D.jU, D.jU_proj i]
  rw [hqi]

/-- If `s : T ⟶ Vi D i` is a lift of `t ≫ jU.toImage : T ⟶ Z` along `(Vi D i).ι`, then
`s ≫ pii D i : T ⟶ X` is the composite `t ≫ U0.ι`. -/
theorem pii_lift_comp (D : ChowSetup A X f) (i : Fin D.m) {T : Scheme.{u}}
    {t : T ⟶ ((D.U0 : X.Opens) : Scheme.{u})}
    {s : T ⟶ ((ChowSetup.Vi D i) : Scheme.{u})}
    (hs : s ≫ (ChowSetup.Vi D i).ι = t ≫ D.jU.toImage) :
    s ≫ ChowSetup.pii D i = t ≫ ((D.U0 : X.Opens)).ι := by
  have h := phii_lift_comp D i hs
  rw [ChowSetup.pii, ← Category.assoc s (ChowSetup.phii D i) ((D.U i : X.Opens)).ι, h,
    Category.assoc, Scheme.homOfLE_ι]

/-- The map `pii D k` restricted to the piece `Vi D i ⊓ Vi D j` through the inclusion
`homOfLE e` is the canonical inclusion `U0 ⊆ X`, for any `e : Vi i ⊓ Vi j ≤ Vi k`. -/
theorem pii_lift_comp_le (D : ChowSetup A X f) (i j k : Fin D.m)
    (e : ChowSetup.Vi D i ⊓ ChowSetup.Vi D j ≤ ChowSetup.Vi D k)
    (L : ((D.U0 : X.Opens) : Scheme.{u}) ⟶
      (((ChowSetup.Vi D i ⊓ ChowSetup.Vi D j) : (ChowSetup.Z D).Opens) : Scheme.{u}))
    (hL : L ≫ (ChowSetup.Vi D i ⊓ ChowSetup.Vi D j).ι = D.jU.toImage) :
    L ≫ ((ChowSetup.Z D).homOfLE e ≫ ChowSetup.pii D k) = ((D.U0 : X.Opens)).ι := by
  have hs : (L ≫ (ChowSetup.Z D).homOfLE e) ≫ (ChowSetup.Vi D k).ι
      = (𝟙 ((D.U0 : X.Opens) : Scheme.{u})) ≫ D.jU.toImage := by
    rw [Category.id_comp, Category.assoc, Scheme.homOfLE_ι, hL]
  have h := pii_lift_comp D k hs
  rw [← Category.assoc L _ (ChowSetup.pii D k)]
  rw [h, Category.id_comp]

/-- Gluing lemma: morphisms out of the members of an open cover of a scheme, presented as the
opens `V i` of an ambient scheme `Z`, which agree on the pairwise intersections glue to a
morphism out of the union `⋃ i, V i`.

This is `Scheme.Cover.glueMorphisms` for the cover `Scheme.Opens.iSupOpenCover V`, the
compatibility on pullbacks being the compatibility on the intersections
(`isPullback_opens_inf_le`). -/
theorem glueMorphisms_opens {Z : Scheme.{u}} {ι : Type u} (V : ι → Z.Opens)
    (p : ∀ i, ((V i) : Scheme.{u}) ⟶ X)
    (h : ∀ i j, Z.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ p i
      = Z.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ p j) :
    ∃ g : ((⨆ i, V i : Z.Opens) : Scheme.{u}) ⟶ X, ∀ i, Z.homOfLE (le_iSup V i) ≫ g = p i := by
  let 𝒰 := Scheme.Opens.iSupOpenCover V
  refine ⟨𝒰.glueMorphisms p ?_, fun i => 𝒰.ι_glueMorphisms p _ i⟩
  intro i j
  show pullback.fst (Z.homOfLE (le_iSup V i)) (Z.homOfLE (le_iSup V j)) ≫ p i
    = pullback.snd (Z.homOfLE (le_iSup V i)) (Z.homOfLE (le_iSup V j)) ≫ p j
  have hpb : IsPullback (Z.homOfLE (inf_le_left : V i ⊓ V j ≤ V i))
      (Z.homOfLE (inf_le_right : V i ⊓ V j ≤ V j))
      (Z.homOfLE (le_iSup V i)) (Z.homOfLE (le_iSup V j)) := isPullback_opens_inf_le _ _
  refine (cancel_epi hpb.isoPullback.hom).mp ?_
  calc hpb.isoPullback.hom ≫ pullback.fst (Z.homOfLE (le_iSup V i)) (Z.homOfLE (le_iSup V j)) ≫ p i
      = (hpb.isoPullback.hom ≫ pullback.fst (Z.homOfLE (le_iSup V i))
          (Z.homOfLE (le_iSup V j))) ≫ p i := (Category.assoc _ _ _).symm
    _ = Z.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ p i := by rw [hpb.isoPullback_hom_fst]
    _ = Z.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ p j := h i j
    _ = (hpb.isoPullback.hom ≫ pullback.snd (Z.homOfLE (le_iSup V i))
          (Z.homOfLE (le_iSup V j))) ≫ p j := by rw [hpb.isoPullback_hom_snd]
    _ = hpb.isoPullback.hom ≫ pullback.snd (Z.homOfLE (le_iSup V i))
        (Z.homOfLE (le_iSup V j)) ≫ p j := Category.assoc _ _ _

theorem gluePiExists {A : Type u} [CommRing A] {X : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)} [AlgebraicGeometry.IsSeparated f] (D : Work.DSG2.ChowSetup A X f) : ∃ g : Work.DSG2.ChowSetup.X' D ⟶ X, ∀ i : Fin D.m, CategoryTheory.CategoryStruct.comp ((Work.DSG2.ChowSetup.cover D).f i) g = Work.DSG2.ChowSetup.pii D i := by
  haveI : IsNoetherian X := D.hNoeth
  haveI hNoethU0 : TopologicalSpace.NoetherianSpace ((D.U0 : X.Opens) : Scheme.{u}) :=
    noetherianSpace_opens D
  haveI hQCjU : QuasiCompact D.jU := inferInstance
  haveI hQCimg : QuasiCompact D.jU.toImage := inferInstance
  haveI hDom : IsSchemeTheoreticallyDominant D.jU.toImage :=
    isSchemeTheoreticallyDominant_toImage D.jU
  have hri : ∀ i : Fin D.m,
      Set.range ⇑(D.jU.toImage) ⊆ Set.range ⇑((ChowSetup.Vi D i).ι) :=
    fun i => range_jU_toImage_subset_Vi D i
  -- the maps `pii D i` agree on the intersections `Vi i ⊓ Vi j`
  have hcompat : ∀ i j : Fin D.m,
      (ChowSetup.Z D).homOfLE (inf_le_left :
          ChowSetup.Vi D i ⊓ ChowSetup.Vi D j ≤ ChowSetup.Vi D i) ≫ ChowSetup.pii D i
      = (ChowSetup.Z D).homOfLE (inf_le_right :
          ChowSetup.Vi D i ⊓ ChowSetup.Vi D j ≤ ChowSetup.Vi D j) ≫ ChowSetup.pii D j := by
    intro i j
    have hW : Set.range ⇑(D.jU.toImage) ⊆
        Set.range ⇑((ChowSetup.Vi D i ⊓ ChowSetup.Vi D j).ι) := by
      intro z hz
      have h1 := hri i hz
      have h2 := hri j hz
      simpa only [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff] using
        And.intro h1 h2
    let L : ((D.U0 : X.Opens) : Scheme.{u}) ⟶
        (((ChowSetup.Vi D i ⊓ ChowSetup.Vi D j) : (ChowSetup.Z D).Opens) : Scheme.{u}) :=
      IsOpenImmersion.lift (ChowSetup.Vi D i ⊓ ChowSetup.Vi D j).ι D.jU.toImage hW
    have hL : L ≫ (ChowSetup.Vi D i ⊓ ChowSetup.Vi D j).ι = D.jU.toImage :=
      IsOpenImmersion.lift_fac _ _ hW
    -- `U0 ⟶ Vi i ⊓ Vi j` is scheme-theoretically dominant
    haveI : IsSchemeTheoreticallyDominant L :=
      isSchemeTheoreticallyDominant_lift_qc D.jU.toImage
        (ChowSetup.Vi D i ⊓ ChowSetup.Vi D j) hW
    have hleft := pii_lift_comp_le D i j i inf_le_left L hL
    have hright := pii_lift_comp_le D i j j inf_le_right L hL
    refine eq_of_isSchemeTheoreticallyDominant (i := L)
      (p := (ChowSetup.Vi D i ⊓ ChowSetup.Vi D j).ι ≫ ChowSetup.Ziota D ≫ D.πP)
      (q := f) ?_ ?_ ?_
    · rw [Category.assoc, piiCompF D i, Category.assoc,
        ← Category.assoc _ _ (ChowSetup.Ziota D ≫ D.πP), Scheme.homOfLE_ι]
    · rw [Category.assoc, piiCompF D j, Category.assoc,
        ← Category.assoc _ _ (ChowSetup.Ziota D ≫ D.πP), Scheme.homOfLE_ι]
    · exact hleft.trans hright.symm
  -- glue the compatible family along the open cover of `X'` by the pieces `Vi`
  let 𝒰 := Scheme.Opens.iSupOpenCover (ChowSetup.Vi D)
  have hcompat' : ∀ i j : Fin D.m,
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ ChowSetup.pii D i
      = pullback.snd (𝒰.f i) (𝒰.f j) ≫ ChowSetup.pii D j := by
    intro i j
    show pullback.fst ((ChowSetup.Z D).homOfLE (le_iSup (ChowSetup.Vi D) i))
        ((ChowSetup.Z D).homOfLE (le_iSup (ChowSetup.Vi D) j)) ≫ ChowSetup.pii D i
      = pullback.snd ((ChowSetup.Z D).homOfLE (le_iSup (ChowSetup.Vi D) i))
        ((ChowSetup.Z D).homOfLE (le_iSup (ChowSetup.Vi D) j)) ≫ ChowSetup.pii D j
    have hpb : IsPullback
        ((ChowSetup.Z D).homOfLE (inf_le_left :
          ChowSetup.Vi D i ⊓ ChowSetup.Vi D j ≤ ChowSetup.Vi D i))
        ((ChowSetup.Z D).homOfLE (inf_le_right :
          ChowSetup.Vi D i ⊓ ChowSetup.Vi D j ≤ ChowSetup.Vi D j))
        ((ChowSetup.Z D).homOfLE (le_iSup (ChowSetup.Vi D) i))
        ((ChowSetup.Z D).homOfLE (le_iSup (ChowSetup.Vi D) j)) :=
      isPullback_opens_inf_le _ _
    refine (cancel_epi hpb.isoPullback.hom).mp ?_
    calc hpb.isoPullback.hom ≫ pullback.fst
          ((ChowSetup.Z D).homOfLE (le_iSup (ChowSetup.Vi D) i))
          ((ChowSetup.Z D).homOfLE (le_iSup (ChowSetup.Vi D) j)) ≫ ChowSetup.pii D i
        = (hpb.isoPullback.hom ≫ pullback.fst
            ((ChowSetup.Z D).homOfLE (le_iSup (ChowSetup.Vi D) i))
            ((ChowSetup.Z D).homOfLE (le_iSup (ChowSetup.Vi D) j))) ≫ ChowSetup.pii D i :=
          (Category.assoc _ _ _).symm
      _ = (ChowSetup.Z D).homOfLE (inf_le_left :
            ChowSetup.Vi D i ⊓ ChowSetup.Vi D j ≤ ChowSetup.Vi D i) ≫ ChowSetup.pii D i := by
          rw [hpb.isoPullback_hom_fst]
      _ = (ChowSetup.Z D).homOfLE (inf_le_right :
            ChowSetup.Vi D i ⊓ ChowSetup.Vi D j ≤ ChowSetup.Vi D j) ≫ ChowSetup.pii D j :=
          hcompat i j
      _ = (hpb.isoPullback.hom ≫ pullback.snd
            ((ChowSetup.Z D).homOfLE (le_iSup (ChowSetup.Vi D) i))
            ((ChowSetup.Z D).homOfLE (le_iSup (ChowSetup.Vi D) j))) ≫ ChowSetup.pii D j := by
          rw [hpb.isoPullback_hom_snd]
      _ = hpb.isoPullback.hom ≫ pullback.snd
          ((ChowSetup.Z D).homOfLE (le_iSup (ChowSetup.Vi D) i))
          ((ChowSetup.Z D).homOfLE (le_iSup (ChowSetup.Vi D) j)) ≫ ChowSetup.pii D j :=
          Category.assoc _ _ _
  refine ⟨𝒰.glueMorphisms (fun i => ChowSetup.pii D i) hcompat', fun i => ?_⟩
  exact Scheme.Cover.ι_glueMorphisms 𝒰 (fun i => ChowSetup.pii D i) hcompat' i

end Work.DSG2
