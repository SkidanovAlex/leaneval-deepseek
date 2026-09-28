-- Copied verbatim from `Submission.Work.Cohomology.pd_union_hit_pos`, with imports re-routed to the
-- clash-free chain (`Work.Thom.Relocate.*` / the local copies in this directory), exactly as
-- `Submission/Work/Thom/README.md` ADDENDUM 16 did for the Thom area: the workspace contains
-- two *identical* duplicate modules `Work.Cohomology.Crux.ovlRestrictionSurjective` and
-- `Work.Cohomology.Crux.vkCruxRestr`, so a module importing one cannot be combined with a
-- module importing the other.  The `Work.ThomBordism` chapter imports
-- `ovlRestrictionSurjective` (via `Interface.lean`), hence these copies.  All declarations
-- keep their original names and proofs.
import Mathlib
import Submission.Work.ThomBordism.Port.PdUnionHitModKernel
import Submission.Work.Cohomology.pd_small_union_iso
import Submission.Work.Cohomology.homologyMV_honest_les
import Submission.Work.Cohomology.pd_goodD_incl
import Submission.Work.Cohomology.pd_goodD_natural
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_glue_defs
-- Re-pointed to the original chain (Islands subproject, 2026): the `Thom/Relocate` copies of
-- the Poincaré-duality chain declared the same names as the `Cohomology/` originals.  The
-- originals are now re-routed (`Crux/vk_transgression_cap_weak.lean` imports the `ovl` copies),
-- so the copies are no longer needed here and the two modules can be imported together.
import Submission.Work.Cohomology.pd_glue2

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## Elementary additivity of `goodD` -/

theorem goodD_add_puh {M : TopCat} [T2Space M] {N : ℕ} (c : (singularChains ℤ M).homology N)
    {W : Set M} (hW : IsOpen W) {K : Set M} (hKW : K ⊆ W) (hKc : IsCompact K)
    (k m : ℕ) (hkm : k + m = N)
    (a b : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k) :
    goodD N c W hW K hKW hKc k m hkm (a + b)
      = goodD N c W hW K hKW hKc k m hkm a + goodD N c W hW K hKW hKc k m hkm b := by
  simp only [goodD]
  rw [map_add, LinearMap.add_apply]

theorem goodD_sub_puh {M : TopCat} [T2Space M] {N : ℕ} (c : (singularChains ℤ M).homology N)
    {W : Set M} (hW : IsOpen W) {K : Set M} (hKW : K ⊆ W) (hKc : IsCompact K)
    (k m : ℕ) (hkm : k + m = N)
    (a b : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k) :
    goodD N c W hW K hKW hKc k m hkm (a - b)
      = goodD N c W hW K hKW hKc k m hkm a - goodD N c W hW K hKW hKc k m hkm b := by
  simp only [goodD]
  rw [map_sub, LinearMap.sub_apply]

/-! ## Realizing a compactly supported class of a smaller open set inside a larger one -/

/-- If `U ⊆ W` are open and `K ⊆ U` is compact, every class of `H^k(U, U∖K)` is the restriction of
one of `H^k(W, W∖K)`, and its duality class is the image of the duality class of `U`. -/
theorem goodD_push_puh {M : TopCat} [T2Space M] {N : ℕ}
    {c : (singularChains ℤ M).homology N}
    {U W : Set M} (hUW : U ⊆ W) (hW : IsOpen W) (hU : IsOpen U)
    {K : Set M} (hKU : K ⊆ U) (hKW : K ⊆ W) (hKc : IsCompact K)
    (k m : ℕ) (hkm : k + m = N)
    (x : (relComplex ℤ (TopCat.of U) (pdRelSub U K)).homology k) :
    ∃ x' : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k,
      goodD N c W hW K hKW hKc k m hkm x'
        = (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of U) (TopCat.of W)
            (pdIncl W U hUW)) m) (goodD N c U hU K hKU hKc k m hkm x) := by
  haveI hriso : CategoryTheory.IsIso (HomologicalComplex.homologyMap (relComplexMap ℤ
      (pdRelSub U K) (pdRelSub W K) (pdIncl W U hUW) (fun y hy => hy)) k) :=
    pdCohExcision (M := M) (W := W) (U := U) hUW hU hW hKU hKc k
  refine ⟨CategoryTheory.inv (HomologicalComplex.homologyMap (relComplexMap ℤ
      (pdRelSub U K) (pdRelSub W K) (pdIncl W U hUW) (fun y hy => hy)) k) x, ?_⟩
  have hrx : (HomologicalComplex.homologyMap (relComplexMap ℤ
      (pdRelSub U K) (pdRelSub W K) (pdIncl W U hUW) (fun y hy => hy)) k)
      (CategoryTheory.inv (HomologicalComplex.homologyMap (relComplexMap ℤ
        (pdRelSub U K) (pdRelSub W K) (pdIncl W U hUW) (fun y hy => hy)) k) x) = x :=
    IsIso.inv_hom_id_apply _ x
  have hkey := pd_goodD_incl (M := M) (W := W) (V := U) hUW hW hU hKU hKW hKc N c k m hkm
    (CategoryTheory.inv (HomologicalComplex.homologyMap (relComplexMap ℤ
      (pdRelSub U K) (pdRelSub W K) (pdIncl W U hUW) (fun y hy => hy)) k) x)
  rw [hrx] at hkey
  exact hkey.symm

/-! ## The positive-degree surjectivity of the gluing

This is obtained by assembling the "modulo the Mayer–Vietoris image" reduction
(`pd_union_hit_mod_kernel`) with the two easy remaining ingredients:

* the image of `H_m(U) ⊞ H_m(V) → H_m(U∪V)` is *contained* in the image of `goodD` for `U ∪ V`,
  because the duality maps of `U` and `V` are surjective and natural in the open set;
* a difference of classes realized at three compact sets is realized at their union, by the
  naturality of `goodD` in the compact set. -/

theorem pd_union_hit_pos {M : TopCat} [T2Space M] {N : ℕ}
    {c : (singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    (hUU : Good N c U hU) (hVV : Good N c V hV) (hII : Good N c (U ∩ V) hI)
    (k m : ℕ) (hkm : k + m = N) (hm : 1 ≤ m) :
    ∀ y : (singularChains ℤ (TopCat.of ↥(U ∪ V : Set M))).homology m,
      ∃ (K : Set M) (hKW : K ⊆ U ∪ V) (hKc : IsCompact K)
        (x : (relComplex ℤ (TopCat.of ↥(U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) K)).homology k),
        goodD N c (U ∪ V : Set M) (hU.union hV) K hKW hKc k m hkm x = y := by
  intro y
  have hW : IsOpen (U ∪ V : Set M) := hU.union hV
  have hUW : U ⊆ (U ∪ V : Set M) := Set.subset_union_left
  have hVW : V ⊆ (U ∪ V : Set M) := Set.subset_union_right
  obtain ⟨Φ, hΦincl, hΦiso, hΦU, hΦV⟩ := pd_small_union_iso (M := M) U V hU hV
  obtain ⟨K, hKW, hKc, x, hdiff⟩ :=
    pd_union_hit_mod_kernel hU hV hI hUU hVV hII k m hkm hm Φ hΦincl hΦiso hΦU hΦV y
  set TU : pdHomSub M U m ⟶ pdHomSub M (U ∪ V) m :=
    HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of U) (TopCat.of (U ∪ V : Set M))
      (pdIncl (U ∪ V : Set M) U hUW)) m with hTU
  set TV : pdHomSub M V m ⟶ pdHomSub M (U ∪ V) m :=
    HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of V) (TopCat.of (U ∪ V : Set M))
      (pdIncl (U ∪ V : Set M) V hVW)) m with hTV
  set G0 : pdHomBiprod M U V m ⟶ pdHomSub M (U ∪ V) m :=
    (homMVBiprodIso M U V m).inv
      ≫ HomologicalComplex.homologyMap (mvRight U V) m
      ≫ HomologicalComplex.homologyMap Φ m with hG0
  have hGinl : (biprod.inl : pdHomSub M U m ⟶ pdHomBiprod M U V m) ≫ G0 = TU := by
    dsimp only [G0, TU]
    rw [← Category.assoc, homMVBiprodIso_inl, ← Category.assoc,
      ← HomologicalComplex.homologyMap_comp, mvRight, biprod.inl_desc,
      ← HomologicalComplex.homologyMap_comp, hΦU]
  have hGinr : (biprod.inr : pdHomSub M V m ⟶ pdHomBiprod M U V m) ≫ G0 = - TV := by
    dsimp only [G0, TV]
    rw [← Category.assoc, homMVBiprodIso_inr, ← Category.assoc,
      ← HomologicalComplex.homologyMap_comp, mvRight, biprod.inr_desc,
      HomologicalComplex.homologyMap_neg, Preadditive.neg_comp,
      ← HomologicalComplex.homologyMap_comp, hΦV]
  have hGform : G0 = biprod.fst ≫ TU + biprod.snd ≫ (- TV) := by
    refine biprod.hom_ext' G0 (biprod.fst ≫ TU + biprod.snd ≫ (- TV)) ?_ ?_
    · rw [hGinl, Preadditive.comp_add, biprod.inl_fst_assoc, biprod.inl_snd_assoc]
      simp
    · rw [hGinr, Preadditive.comp_add, biprod.inr_fst_assoc, biprod.inr_snd_assoc]
      simp
  have hrangeG0 : Submodule.map (ModuleCat.Hom.hom G0) ⊤ ≤
      Submodule.map (ModuleCat.Hom.hom TU) ⊤ ⊔ Submodule.map (ModuleCat.Hom.hom TV) ⊤ := by
    have hlin : ModuleCat.Hom.hom G0 = ModuleCat.Hom.hom (biprod.fst ≫ TU)
        + ModuleCat.Hom.hom (biprod.snd ≫ (- TV)) := by
      rw [hGform, ModuleCat.hom_add]
    rw [hlin]
    refine le_trans (Submodule.map_add_le ⊤ _ _) ?_
    apply sup_le
    · rw [ModuleCat.hom_comp, Submodule.map_comp]
      exact le_trans (Submodule.map_mono le_top) le_sup_left
    · rw [ModuleCat.hom_comp, ModuleCat.hom_neg, Submodule.map_comp]
      refine le_trans (Submodule.map_mono le_top) ?_
      rw [Submodule.map_neg]
      exact le_sup_right
  have hmemG0 : goodD N c (U ∪ V : Set M) hW K hKW hKc k m hkm x - y
      ∈ Submodule.map (ModuleCat.Hom.hom G0) ⊤ := by
    rw [LinearMap.mem_range] at hdiff
    obtain ⟨w, hw⟩ := hdiff
    have hcat : ModuleCat.Hom.hom G0
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (mvRight U V) m
              ≫ HomologicalComplex.homologyMap Φ m)).comp
            (ModuleCat.Hom.hom (homMVBiprodIso M U V m).inv) := by
      rw [hG0, ModuleCat.hom_comp]
    refine ⟨(homMVBiprodIso M U V m).hom w, Submodule.mem_top, ?_⟩
    rw [hcat, LinearMap.comp_apply,
      CategoryTheory.Iso.hom_inv_id_apply (homMVBiprodIso M U V m) w]
    exact hw
  have htop : goodD N c (U ∪ V : Set M) hW K hKW hKc k m hkm x - y
      ∈ Submodule.map (ModuleCat.Hom.hom TU) ⊤
        ⊔ Submodule.map (ModuleCat.Hom.hom TV) ⊤ := hrangeG0 hmemG0
  obtain ⟨a₁, ha₁, a₂, ha₂, ha₁₂⟩ := Submodule.mem_sup.mp htop
  obtain ⟨a, -, ha⟩ := Submodule.mem_map.mp ha₁
  obtain ⟨b, -, hb⟩ := Submodule.mem_map.mp ha₂
  obtain ⟨Ka, hKaU, hKac, xa, hxa⟩ := (hUU k m hkm).1 a
  obtain ⟨Kb, hKbV, hKbc, xb, hxb⟩ := (hVV k m hkm).1 b
  obtain ⟨Xa, hXa⟩ := goodD_push_puh (M := M) hUW hW hU hKaU (hKaU.trans hUW) hKac k m hkm xa
  obtain ⟨Xb, hXb⟩ := goodD_push_puh (M := M) hVW hW hV hKbV (hKbV.trans hVW) hKbc k m hkm xb
  have hKaW : Ka ⊆ (U ∪ V : Set M) := hKaU.trans hUW
  have hKbW : Kb ⊆ (U ∪ V : Set M) := hKbV.trans hVW
  have hKtotW : K ∪ Ka ∪ Kb ⊆ (U ∪ V : Set M) :=
    Set.union_subset (Set.union_subset hKW hKaW) hKbW
  have hKtotc : IsCompact (K ∪ Ka ∪ Kb) := (hKc.union hKac).union hKbc
  have hsubK : K ⊆ K ∪ Ka ∪ Kb :=
    Set.subset_union_of_subset_left (Set.subset_union_left : K ⊆ K ∪ Ka) Kb
  have hsubKa : Ka ⊆ K ∪ Ka ∪ Kb :=
    Set.subset_union_of_subset_left (Set.subset_union_right : Ka ⊆ K ∪ Ka) Kb
  have hsubKb : Kb ⊆ K ∪ Ka ∪ Kb := Set.subset_union_right
  have ha'' : (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of U)
      (TopCat.of (U ∪ V : Set M)) (pdIncl (U ∪ V : Set M) U hUW)) m) a = a₁ := ha
  have hb'' : (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of V)
      (TopCat.of (U ∪ V : Set M)) (pdIncl (U ∪ V : Set M) V hVW)) m) b = a₂ := hb
  have hDWa : goodD N c (U ∪ V : Set M) hW Ka hKaW hKac k m hkm Xa = a₁ := by
    rw [hXa, hxa, ha'']
  have hDWb : goodD N c (U ∪ V : Set M) hW Kb hKbW hKbc k m hkm Xb = a₂ := by
    rw [hXb, hxb, hb'']
  refine ⟨K ∪ Ka ∪ Kb, hKtotW, hKtotc,
    (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hsubK) k) x
      - (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hsubKa) k) Xa
      - (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hsubKb) k) Xb,
    ?_⟩
  rw [goodD_sub_puh, goodD_sub_puh,
    pd_goodD_natural N c (U ∪ V : Set M) hW hsubK hKW hKtotW hKc hKtotc k m hkm x,
    pd_goodD_natural N c (U ∪ V : Set M) hW hsubKa hKaW hKtotW hKac hKtotc k m hkm Xa,
    pd_goodD_natural N c (U ∪ V : Set M) hW hsubKb hKbW hKtotW hKbc hKtotc k m hkm Xb,
    hDWa, hDWb]
  rw [show goodD N c (U ∪ V : Set M) hW K hKW hKc k m hkm x - a₁ - a₂
      = goodD N c (U ∪ V : Set M) hW K hKW hKc k m hkm x - (a₁ + a₂) from by abel, ha₁₂]
  abel

end

end Work.Cohomology
