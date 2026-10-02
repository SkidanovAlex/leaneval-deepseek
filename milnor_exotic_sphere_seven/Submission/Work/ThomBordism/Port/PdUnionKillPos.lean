-- Copied verbatim from `Submission.Work.Cohomology.pd_union_kill_pos`, with imports re-routed to the
-- clash-free chain (`Work.Thom.Relocate.*` / the local copies in this directory), exactly as
-- `Submission/Work/Thom/README.md` ADDENDUM 16 did for the Thom area: the workspace contains
-- two *identical* duplicate modules `Work.Cohomology.Crux.ovlRestrictionSurjective` and
-- `Work.Cohomology.Crux.vkCruxRestr`, so a module importing one cannot be combined with a
-- module importing the other.  The `Work.ThomBordism` chapter imports
-- `ovlRestrictionSurjective` (via `Interface.lean`), hence these copies.  All declarations
-- keep their original names and proofs.
import Mathlib
import Submission.Work.Cohomology.pd_good
-- Re-pointed to the original chain (Islands subproject, 2026): the `Thom/Relocate` copies of
-- the Poincaré-duality chain declared the same names as the `Cohomology/` originals.  The
-- originals are now re-routed (`Crux/vk_transgression_cap_weak.lean` imports the `ovl` copies),
-- so the copies are no longer needed here and the two modules can be imported together.
import Submission.Work.Cohomology.pd_split_kc
-- Re-pointed to the original chain (Islands subproject, 2026): the `Thom/Relocate` copies of
-- the Poincaré-duality chain declared the same names as the `Cohomology/` originals.  The
-- originals are now re-routed (`Crux/vk_transgression_cap_weak.lean` imports the `ovl` copies),
-- so the copies are no longer needed here and the two modules can be imported together.
import Submission.Work.Cohomology.pd_union_extend
import Submission.Work.ThomBordism.Port.PdRestrictionInjective
import Submission.Work.Cohomology.pd_compact_pieces
import Submission.Work.Cohomology.homologyMV_honest_les
import Submission.Work.Cohomology.pd_goodD_incl
import Submission.Work.Cohomology.pd_goodD_natural
import Submission.Work.ThomBordism.Port.PdColimDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Cohomology

noncomputable section

set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

/-! ## Auxiliary: the biproduct structure of `ModuleCat ℤ` -/

theorem biprod_fst_inl_add_inr {A B : ModuleCat ℤ} (a : A) (b : B) :
    (biprod.fst : A ⊞ B ⟶ A) ((biprod.inl : A ⟶ A ⊞ B) a + (biprod.inr : B ⟶ A ⊞ B) b) = a := by
  rw [map_add]
  have h1 : (biprod.fst : A ⊞ B ⟶ A) ((biprod.inl : A ⟶ A ⊞ B) a) = a := by
    have h := congrArg (fun (f : A ⟶ A) => (ModuleCat.Hom.hom f) a) (biprod.inl_fst (X := A) (Y := B))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h
  have h2 : (biprod.fst : A ⊞ B ⟶ A) ((biprod.inr : B ⟶ A ⊞ B) b) = 0 := by
    have h := congrArg (fun (f : B ⟶ A) => (ModuleCat.Hom.hom f) b) (biprod.inr_fst (X := A) (Y := B))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h
  rw [h1, h2, add_zero]

theorem biprod_snd_inl_add_inr {A B : ModuleCat ℤ} (a : A) (b : B) :
    (biprod.snd : A ⊞ B ⟶ B) ((biprod.inl : A ⟶ A ⊞ B) a + (biprod.inr : B ⟶ A ⊞ B) b) = b := by
  rw [map_add]
  have h1 : (biprod.snd : A ⊞ B ⟶ B) ((biprod.inl : A ⟶ A ⊞ B) a) = 0 := by
    have h := congrArg (fun (f : A ⟶ B) => (ModuleCat.Hom.hom f) a) (biprod.inl_snd (X := A) (Y := B))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h
  have h2 : (biprod.snd : A ⊞ B ⟶ B) ((biprod.inr : B ⟶ A ⊞ B) b) = b := by
    have h := congrArg (fun (f : B ⟶ B) => (ModuleCat.Hom.hom f) b) (biprod.inr_snd (X := A) (Y := B))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h
  rw [h1, h2, zero_add]

/-! ## Auxiliary: the trace homeomorphism `S ≅ W ∩ S` on homology -/

/-- `pdTrMap h` is a right inverse of `pdTrInv h`. -/
theorem pdTrMap_comp_pdTrInv {M : TopCat} {W S : Set M} (h : S ⊆ W) :
    pdTrMap h ≫ pdTrInv h = 𝟙 (TopCat.of S) := by
  ext x
  rfl

/-- On homology, the inverse of the trace map is a right inverse of the trace map. -/
theorem pdTrInv_homologyMap_comp {M : TopCat} {W S : Set M} (h : S ⊆ W) (n : ℕ) :
    HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (pdTr W S)) (TopCat.of S) (pdTrInv h)) n
      ≫ HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S)) (pdTrMap h)) n
      = 𝟙 ((singularChains ℤ (TopCat.of (pdTr W S))).homology n) := by
  rw [← HomologicalComplex.homologyMap_comp, chainMap_compPD, pdTrInv_comp_pdTrMap h,
    chainMap_id', HomologicalComplex.homologyMap_id]

/-- On homology, the trace map is a left inverse of its inverse. -/
theorem pdTrMap_homologyMap_comp {M : TopCat} {W S : Set M} (h : S ⊆ W) (n : ℕ) :
    HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S)) (pdTrMap h)) n
      ≫ HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (pdTr W S)) (TopCat.of S) (pdTrInv h)) n
      = 𝟙 ((singularChains ℤ (TopCat.of S)).homology n) := by
  rw [← HomologicalComplex.homologyMap_comp, chainMap_compPD, pdTrMap_comp_pdTrInv h,
    chainMap_id', HomologicalComplex.homologyMap_id]

/-- The square relating the trace maps of `T ⊆ S ⊆ W` to the inclusions `T ⊆ S`. -/
theorem pdTrMap_pdIncl {M : TopCat} {W S T : Set M} (hST : T ⊆ S) (hS : S ⊆ W) :
    pdTrMap (hST.trans hS)
        ≫ pdIncl (M := TopCat.of W) (pdTr W S) (pdTr W T) (fun x hx => hST hx)
      = pdIncl S T hST ≫ pdTrMap hS := by
  ext x
  rfl

/-- **Application of `pdHomIncl` to a trace-transported class.** -/
theorem pdHomIncl_pdTrMap {M : TopCat} {W S : Set M} (h : S ⊆ W) (m : ℕ)
    (x : (singularChains ℤ (TopCat.of S)).homology m) :
    (pdHomIncl (TopCat.of W) (pdTr W S) m)
        ((HomologicalComplex.homologyMap
          (chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S)) (pdTrMap h)) m) x)
      = (HomologicalComplex.homologyMap
          (chainMap ℤ (TopCat.of S) (TopCat.of W) (pdIncl W S h)) m) x := by
  have hcomp : HomologicalComplex.homologyMap
        (chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S)) (pdTrMap h)) m
      ≫ HomologicalComplex.homologyMap
        (chainMap ℤ (TopCat.of (pdTr W S)) (TopCat.of W)
          (subtypeIncl (TopCat.of W) (pdTr W S))) m
      = HomologicalComplex.homologyMap
        (chainMap ℤ (TopCat.of S) (TopCat.of W) (pdIncl W S h)) m := by
    rw [← HomologicalComplex.homologyMap_comp, chainMap_compPD, pdTrMap_comp h]
  have hh := congrArg
    (fun (f : (singularChains ℤ (TopCat.of S)).homology m
        ⟶ (singularChains ℤ (TopCat.of W)).homology m) => (ModuleCat.Hom.hom f) x) hcomp
  simpa only [pdHomIncl, ModuleCat.hom_comp, LinearMap.comp_apply] using hh

/-! ## Auxiliary lemmas for the chase -/

/-- `goodD` is additive in the cohomology class. -/
theorem goodD_sub {M : TopCat} [T2Space M] {N : ℕ} (c : (singularChains ℤ M).homology N)
    {W : Set M} (hW : IsOpen W) {K : Set M} (hKW : K ⊆ W) (hKc : IsCompact K)
    (k m : ℕ) (hkm : k + m = N)
    (a b : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k) :
    goodD N c W hW K hKW hKc k m hkm (a - b)
      = goodD N c W hW K hKW hKc k m hkm a - goodD N c W hW K hKW hKc k m hkm b := by
  simp only [goodD]
  simp

/-- The enlargement maps only depend on the pairs of sets. -/
theorem pdRelComplexEnlarge_congr_h {M : TopCat} (W : Set M) {K K' : Set M} (h h' : K ⊆ K') :
    pdRelComplexEnlarge W h = pdRelComplexEnlarge W h' := by
  unfold pdRelComplexEnlarge
  exact pd_relComplexMap_h_congr _ _ _ _ _

/-- Enlargement of the compact set is compatible with composition, on homology. -/
theorem pdRelComplexEnlarge_homologyMap_comp {M : TopCat} (W : Set M) {K K' K'' : Set M}
    (h : K ⊆ K') (h' : K' ⊆ K'') (k : ℕ) :
    HomologicalComplex.homologyMap (pdRelComplexEnlarge W h) k
        ≫ HomologicalComplex.homologyMap (pdRelComplexEnlarge W h') k
      = HomologicalComplex.homologyMap (pdRelComplexEnlarge W (h.trans h')) k := by
  rw [← HomologicalComplex.homologyMap_comp, pdRelComplexEnlarge_comp]

/-- **The square of the enlargement and the restriction to a smaller open set.** -/
theorem pdRelComplexEnlarge_restrict {M : TopCat} {W U : Set M} (hUW : U ⊆ W) {K K' : Set M}
    (hKU : K ⊆ U) (hK'U : K' ⊆ U) (h : K ⊆ K') (k : ℕ) :
    HomologicalComplex.homologyMap (pdRelComplexEnlarge W h) k
        ≫ HomologicalComplex.homologyMap (relComplexMap ℤ
            (X₁ := TopCat.of U) (X₂ := TopCat.of W) (pdRelSub U K') (pdRelSub W K')
            (pdIncl W U hUW) (fun x hx => hx)) k
      = HomologicalComplex.homologyMap (relComplexMap ℤ
            (X₁ := TopCat.of U) (X₂ := TopCat.of W) (pdRelSub U K) (pdRelSub W K)
            (pdIncl W U hUW) (fun x hx => hx)) k
        ≫ HomologicalComplex.homologyMap (pdRelComplexEnlarge U h) k := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 1
  rw [pdRelComplexEnlarge, pdRelComplexEnlarge]
  have h1 := capRel_relComplexMap_comp (R := ℤ) (pdRelSub U K') (pdRelSub W K') (pdRelSub W K)
    (pdIncl W U hUW) (𝟙 (TopCat.of W))
    (fun x hx => hx) (fun y hy => pdRelSub_mono h hy)
  have h2 := capRel_relComplexMap_comp (R := ℤ) (pdRelSub U K') (pdRelSub U K) (pdRelSub W K)
    (𝟙 (TopCat.of U)) (pdIncl W U hUW)
    (fun x hx => pdRelSub_mono h hx) (fun y hy => hy)
  have h3 := capRel_relComplexMap_congr (R := ℤ) (A₁ := pdRelSub U K') (A₂ := pdRelSub W K)
    (f := (pdIncl W U hUW) ≫ 𝟙 (TopCat.of W))
    (f' := 𝟙 (TopCat.of U) ≫ pdIncl W U hUW)
    (by simp) (fun x hx => fun hxK => hx (h hxK))
    (fun x hx => fun hxK => hx (h hxK))
  rw [← h1, ← h2]
  exact h3

/-! ## Exactness at the middle of the Mayer–Vietoris sequence of the cover `{U, V}` of `U ∪ V` -/

/-- **Mayer–Vietoris exactness at the middle term, in the honest singular-chain vocabulary.**

Let `U, V ⊆ M` be open.  If two homology classes `u ∈ H_m(U)` and `v ∈ H_m(V)` have the same image
in `H_m(U ∪ V)`, then they are the images of a common class `t ∈ H_m(U ∩ V)`. -/
theorem pdMV_exact_mid {M : TopCat} {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (m : ℕ)
    (u : (singularChains ℤ (TopCat.of U)).homology m)
    (v : (singularChains ℤ (TopCat.of V)).homology m)
    (h : (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of U) (TopCat.of (U ∪ V : Set M))
            (pdIncl (U ∪ V : Set M) U Set.subset_union_left)) m) u
        = (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of V) (TopCat.of (U ∪ V : Set M))
            (pdIncl (U ∪ V : Set M) V Set.subset_union_right)) m) v) :
    ∃ t : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).homology m,
      (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of U)
          (pdIncl U (U ∩ V : Set M) Set.inter_subset_left)) m) t = u ∧
      (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of V)
          (pdIncl V (U ∩ V : Set M) Set.inter_subset_right)) m) t = v := by
  have hUW : U ⊆ (U ∪ V : Set M) := Set.subset_union_left
  have hVW : V ⊆ (U ∪ V : Set M) := Set.subset_union_right
  have hIW : (U ∩ V : Set M) ⊆ (U ∪ V : Set M) :=
    Set.inter_subset_left.trans Set.subset_union_left
  have hU' : IsOpen (pdTr (U ∪ V : Set M) U) := hU.preimage continuous_subtype_val
  have hV' : IsOpen (pdTr (U ∪ V : Set M) V) := hV.preimage continuous_subtype_val
  have hcov' : pdTr (U ∪ V : Set M) U ∪ pdTr (U ∪ V : Set M) V = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rcases x.2 with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  -- the three trace isomorphisms on homology
  set AU := HomologicalComplex.homologyMap
    (chainMap ℤ (TopCat.of U) (TopCat.of (pdTr (U ∪ V : Set M) U)) (pdTrMap hUW)) m with hAU
  set AV := HomologicalComplex.homologyMap
    (chainMap ℤ (TopCat.of V) (TopCat.of (pdTr (U ∪ V : Set M) V)) (pdTrMap hVW)) m with hAV
  set AI := HomologicalComplex.homologyMap
    (chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of (pdTr (U ∪ V : Set M) (U ∩ V)))
      (pdTrMap hIW)) m with hAI
  set QI := HomologicalComplex.homologyMap
    (chainMap ℤ (TopCat.of (pdTr (U ∪ V : Set M) (U ∩ V))) (TopCat.of (U ∩ V : Set M))
      (pdTrInv hIW)) m with hQI
  set QU := HomologicalComplex.homologyMap
    (chainMap ℤ (TopCat.of (pdTr (U ∪ V : Set M) U)) (TopCat.of U) (pdTrInv hUW)) m with hQU
  set QV := HomologicalComplex.homologyMap
    (chainMap ℤ (TopCat.of (pdTr (U ∪ V : Set M) V)) (TopCat.of V) (pdTrInv hVW)) m with hQV
  set u' := AU u with hu'
  set v' := AV v with hv'
  -- the exactness at the middle of the trace MV sequence
  have hex := (CategoryTheory.ShortComplex.moduleCat_exact_iff _).mp
    (homMV_exact₂ (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U)
      (pdTr (U ∪ V : Set M) V) hU' hV' hcov' m)
  -- the class `(u', v')` lies in the kernel of the trace `homMVG`
  have hG0 : (homMVG (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U)
        (pdTr (U ∪ V : Set M) V) hU' hV' hcov' m)
      ((biprod.inl : (pdHomSub (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U) m)
            ⟶ pdHomBiprod (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U)
              (pdTr (U ∪ V : Set M) V) m) u'
        + (biprod.inr : (pdHomSub (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) V) m)
            ⟶ pdHomBiprod (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U)
              (pdTr (U ∪ V : Set M) V) m) v') = 0 := by
    rw [map_add]
    have h1 : (homMVG (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U)
          (pdTr (U ∪ V : Set M) V) hU' hV' hcov' m)
        ((biprod.inl : (pdHomSub (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U) m)
            ⟶ pdHomBiprod (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U)
              (pdTr (U ∪ V : Set M) V) m) u')
        = (pdHomIncl (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U) m) u' := by
      have hh := congrArg
        (fun (f : pdHomSub (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U) m
            ⟶ pdHom (TopCat.of (U ∪ V : Set M)) m) => (ModuleCat.Hom.hom f) u')
        (homMVG_inl (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U)
          (pdTr (U ∪ V : Set M) V) hU' hV' hcov' m)
      simpa only [pdHomBiprodInl, ModuleCat.hom_comp, LinearMap.comp_apply] using hh
    have h2 : (homMVG (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U)
          (pdTr (U ∪ V : Set M) V) hU' hV' hcov' m)
        ((biprod.inr : (pdHomSub (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) V) m)
            ⟶ pdHomBiprod (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U)
              (pdTr (U ∪ V : Set M) V) m) v')
        = - (pdHomIncl (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) V) m) v' := by
      have hh := congrArg
        (fun (f : pdHomSub (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) V) m
            ⟶ pdHom (TopCat.of (U ∪ V : Set M)) m) => (ModuleCat.Hom.hom f) v')
        (homMVG_inr (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U)
          (pdTr (U ∪ V : Set M) V) hU' hV' hcov' m)
      simp only [pdHomBiprodInr, pdNeg, ModuleCat.hom_comp, LinearMap.comp_apply] at hh
      simpa only [ModuleCat.hom_neg, LinearMap.neg_apply] using hh
    rw [h1, h2]
    have e1 : (pdHomIncl (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U) m) u'
        = (HomologicalComplex.homologyMap
            (chainMap ℤ (TopCat.of U) (TopCat.of (U ∪ V : Set M))
              (pdIncl (U ∪ V : Set M) U hUW)) m) u := by
      rw [hu', hAU]
      exact pdHomIncl_pdTrMap hUW m u
    have e2 : (pdHomIncl (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) V) m) v'
        = (HomologicalComplex.homologyMap
            (chainMap ℤ (TopCat.of V) (TopCat.of (U ∪ V : Set M))
              (pdIncl (U ∪ V : Set M) V hVW)) m) v := by
      rw [hv', hAV]
      exact pdHomIncl_pdTrMap hVW m v
    rw [e1, e2, h]
    abel
  obtain ⟨t', ht'⟩ := hex _ hG0
  -- components of `homMVF t'`
  have hcompU : (pdHomMap (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U)
        (pdTr (U ∪ V : Set M) U ∩ pdTr (U ∪ V : Set M) V) Set.inter_subset_left m) t' = u' := by
    have hh := congrArg
      (fun (f : pdHomInter (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U)
            (pdTr (U ∪ V : Set M) V) m
          ⟶ pdHomSub (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U) m) =>
        (ModuleCat.Hom.hom f) t') (homMVF_fst (TopCat.of (U ∪ V : Set M))
          (pdTr (U ∪ V : Set M) U) (pdTr (U ∪ V : Set M) V) m)
    simp only [pdHomBiprodFst, ModuleCat.hom_comp, LinearMap.comp_apply] at hh
    rw [ht'] at hh
    rw [← hh]
    exact biprod_fst_inl_add_inr u' v'
  have hcompV : (pdHomMap (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) V)
        (pdTr (U ∪ V : Set M) U ∩ pdTr (U ∪ V : Set M) V) Set.inter_subset_right m) t' = v' := by
    have hh := congrArg
      (fun (f : pdHomInter (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U)
            (pdTr (U ∪ V : Set M) V) m
          ⟶ pdHomSub (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) V) m) =>
        (ModuleCat.Hom.hom f) t') (homMVF_snd (TopCat.of (U ∪ V : Set M))
          (pdTr (U ∪ V : Set M) U) (pdTr (U ∪ V : Set M) V) m)
    simp only [pdHomBiprodSnd, ModuleCat.hom_comp, LinearMap.comp_apply] at hh
    rw [ht'] at hh
    rw [← hh]
    exact biprod_snd_inl_add_inr u' v'
  -- the transported class
  have hAIt : AI (QI t') = t' := by
    have hcomp : QI ≫ AI
        = 𝟙 ((singularChains ℤ (TopCat.of (pdTr (U ∪ V : Set M) (U ∩ V)))).homology m) := by
      rw [hQI, hAI]
      exact pdTrInv_homologyMap_comp hIW m
    exact congrArg
      (fun (f : (singularChains ℤ (TopCat.of (pdTr (U ∪ V : Set M) (U ∩ V)))).homology m
          ⟶ (singularChains ℤ (TopCat.of (pdTr (U ∪ V : Set M) (U ∩ V)))).homology m) =>
        (ConcreteCategory.hom f) t') hcomp
  refine ⟨QI t', ?_, ?_⟩
  · -- the `U`-component
    have hsq : AI ≫ (pdHomMap (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U)
          (pdTr (U ∪ V : Set M) U ∩ pdTr (U ∪ V : Set M) V) Set.inter_subset_left m)
        = (pdHomMap M U (U ∩ V : Set M) Set.inter_subset_left m) ≫ AU := by
      have hc := congrArg
        (fun (f : TopCat.of (U ∩ V : Set M) ⟶ TopCat.of (pdTr (U ∪ V : Set M) U)) =>
          HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (U ∩ V : Set M))
            (TopCat.of (pdTr (U ∪ V : Set M) U)) f) m)
        (pdTrMap_pdIncl (W := (U ∪ V : Set M)) (S := U) (T := (U ∩ V : Set M))
          Set.inter_subset_left hUW)
      simp only [← chainMap_compPD, HomologicalComplex.homologyMap_comp, pdHomMap,
        hAI, hAU] at hc
      exact hc
    have hcomp : (pdHomMap (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) U)
          (pdTr (U ∪ V : Set M) U ∩ pdTr (U ∪ V : Set M) V) Set.inter_subset_left m) (AI (QI t'))
        = AU ((pdHomMap M U (U ∩ V : Set M) Set.inter_subset_left m) (QI t')) :=
      congrArg
        (fun (f : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).homology m
            ⟶ (singularChains ℤ (TopCat.of (pdTr (U ∪ V : Set M) U))).homology m) =>
          (ConcreteCategory.hom f) (QI t')) hsq
    rw [hAIt, hcompU] at hcomp
    -- `hcomp : u' = AU ((pdHomMap M U (U∩V) ...) (QI t'))`
    have hAUinj : Function.Injective (fun x => (ModuleCat.Hom.hom AU) x) := by
      intro a b hab
      have ha : (ModuleCat.Hom.hom (AU ≫ QU)) (a - 0) = a - 0 := by
        have h := congrArg
          (fun (k : (singularChains ℤ (TopCat.of U)).homology m
              ⟶ (singularChains ℤ (TopCat.of U)).homology m) =>
            (ConcreteCategory.hom k) (a - 0)) (show AU ≫ QU = 𝟙 _ from by
              rw [hAU, hQU]; exact pdTrMap_homologyMap_comp hUW m)
        simpa using h
      have hb : (ModuleCat.Hom.hom (AU ≫ QU)) (b - 0) = b - 0 := by
        have h := congrArg
          (fun (k : (singularChains ℤ (TopCat.of U)).homology m
              ⟶ (singularChains ℤ (TopCat.of U)).homology m) =>
            (ConcreteCategory.hom k) (b - 0)) (show AU ≫ QU = 𝟙 _ from by
              rw [hAU, hQU]; exact pdTrMap_homologyMap_comp hUW m)
        simpa using h
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, sub_zero] at ha hb
      have hab' : (ModuleCat.Hom.hom AU) a = (ModuleCat.Hom.hom AU) b := hab
      rw [hab'] at ha
      exact ha.symm.trans hb
    exact hAUinj (hcomp.symm.trans hu')
  · -- the `V`-component
    have hsq : AI ≫ (pdHomMap (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) V)
          (pdTr (U ∪ V : Set M) U ∩ pdTr (U ∪ V : Set M) V) Set.inter_subset_right m)
        = (pdHomMap M V (U ∩ V : Set M) Set.inter_subset_right m) ≫ AV := by
      have hc := congrArg
        (fun (f : TopCat.of (U ∩ V : Set M) ⟶ TopCat.of (pdTr (U ∪ V : Set M) V)) =>
          HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (U ∩ V : Set M))
            (TopCat.of (pdTr (U ∪ V : Set M) V)) f) m)
        (pdTrMap_pdIncl (W := (U ∪ V : Set M)) (S := V) (T := (U ∩ V : Set M))
          Set.inter_subset_right hVW)
      simp only [← chainMap_compPD, HomologicalComplex.homologyMap_comp, pdHomMap,
        hAI, hAV] at hc
      exact hc
    have hcomp : (pdHomMap (TopCat.of (U ∪ V : Set M)) (pdTr (U ∪ V : Set M) V)
          (pdTr (U ∪ V : Set M) U ∩ pdTr (U ∪ V : Set M) V) Set.inter_subset_right m) (AI (QI t'))
        = AV ((pdHomMap M V (U ∩ V : Set M) Set.inter_subset_right m) (QI t')) :=
      congrArg
        (fun (f : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).homology m
            ⟶ (singularChains ℤ (TopCat.of (pdTr (U ∪ V : Set M) V))).homology m) =>
          (ConcreteCategory.hom f) (QI t')) hsq
    rw [hAIt, hcompV] at hcomp
    have hAVinj : Function.Injective (fun x => (ModuleCat.Hom.hom AV) x) := by
      intro a b hab
      have ha : (ModuleCat.Hom.hom (AV ≫ QV)) (a - 0) = a - 0 := by
        have h := congrArg
          (fun (k : (singularChains ℤ (TopCat.of V)).homology m
              ⟶ (singularChains ℤ (TopCat.of V)).homology m) =>
            (ConcreteCategory.hom k) (a - 0)) (show AV ≫ QV = 𝟙 _ from by
              rw [hAV, hQV]; exact pdTrMap_homologyMap_comp hVW m)
        simpa using h
      have hb : (ModuleCat.Hom.hom (AV ≫ QV)) (b - 0) = b - 0 := by
        have h := congrArg
          (fun (k : (singularChains ℤ (TopCat.of V)).homology m
              ⟶ (singularChains ℤ (TopCat.of V)).homology m) =>
            (ConcreteCategory.hom k) (b - 0)) (show AV ≫ QV = 𝟙 _ from by
              rw [hAV, hQV]; exact pdTrMap_homologyMap_comp hVW m)
        simpa using h
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, sub_zero] at ha hb
      have hab' : (ModuleCat.Hom.hom AV) a = (ModuleCat.Hom.hom AV) b := hab
      rw [hab'] at ha
      exact ha.symm.trans hb
    exact hAVinj (hcomp.symm.trans hv')

theorem pd_union_kill_pos {M : TopCat} [T2Space M] {N : ℕ}
    {c : (singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    (hUU : Good N c U hU) (hVV : Good N c V hV) (hII : Good N c (U ∩ V) hI)
    (k m : ℕ) (hkm : k + m = N) (hm : 1 ≤ m) :
    ∀ (K : Set M) (hKW : K ⊆ U ∪ V) (hKc : IsCompact K)
       (x : (relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K)).homology k),
       goodD N c (U ∪ V : Set M) (hU.union hV) K hKW hKc k m hkm x = 0 →
       ∃ (K' : Set M) (hKK' : K ⊆ K') (hK'W : K' ⊆ U ∪ V) (hK'c : IsCompact K'),
         (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hKK') k) x = 0 := by
  intro K hKW hKc x hx
  have hW : IsOpen (U ∪ V : Set M) := hU.union hV
  -- Step 1: split the compact set
  obtain ⟨K₁, K₂, hK₁U, hK₂V, hK₁c, hK₂c, hK12⟩ := pd_compact_pieces hU hV hKc hKW
  have hW12 : K₁ ∪ K₂ ⊆ (U ∪ V : Set M) :=
    Set.union_subset (hK₁U.trans Set.subset_union_left) (hK₂V.trans Set.subset_union_right)
  have hW12c : IsCompact (K₁ ∪ K₂) := hK₁c.union hK₂c
  set x₀ : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homology k
    := (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hK12) k) x with hx₀def
  have hx₀ : goodD N c (U ∪ V : Set M) hW (K₁ ∪ K₂) hW12 hW12c k m hkm x₀ = 0 := by
    rw [hx₀def, pd_goodD_natural N c (U ∪ V : Set M) hW hK12 hKW hW12 hKc hW12c k m hkm x, hx]
  -- Step 2: the splitting lemma
  obtain ⟨K₁', K₂', h₁, h₂, hK₁'U, hK₂'V, hK₁'c, hK₂'c, x₁, x₂, hsplit⟩ :=
    pd_split_kc hU hV hI hUU hVV hII k m hkm hm hK₁U hK₂V hK₁c hK₂c x₀ hx₀
  -- Step 3: the two duality classes agree
  have hmid : K₁ ∪ K₂ ⊆ K₁' ∪ K₂' :=
    Set.union_subset (h₁.trans Set.subset_union_left) (h₂.trans Set.subset_union_right)
  have hW1 : K₁' ∪ K₂' ⊆ (U ∪ V : Set M) :=
    Set.union_subset (hK₁'U.trans Set.subset_union_left) (hK₂'V.trans Set.subset_union_right)
  have hW1c : IsCompact (K₁' ∪ K₂') := hK₁'c.union hK₂'c
  have hK₁'W : K₁' ⊆ (U ∪ V : Set M) := hK₁'U.trans Set.subset_union_left
  have hK₂'W : K₂' ⊆ (U ∪ V : Set M) := hK₂'V.trans Set.subset_union_right
  have hD12 : goodD N c (U ∪ V : Set M) hW K₁' hK₁'W hK₁'c k m hkm x₁
      = goodD N c (U ∪ V : Set M) hW K₂' hK₂'W hK₂'c k m hkm x₂ := by
    have h := congrArg (goodD N c (U ∪ V : Set M) hW (K₁' ∪ K₂') hW1 hW1c k m hkm) hsplit
    rw [pd_goodD_natural N c (U ∪ V : Set M) hW hmid hW12 hW1 hW12c hW1c k m hkm x₀,
      hx₀] at h
    rw [goodD_sub c hW hW1 hW1c k m hkm] at h
    rw [pd_goodD_natural N c (U ∪ V : Set M) hW
          (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₂') hK₁'W hW1 hK₁'c hW1c k m hkm x₁,
        pd_goodD_natural N c (U ∪ V : Set M) hW
          (Set.subset_union_right : K₂' ⊆ K₁' ∪ K₂') hK₂'W hW1 hK₂'c hW1c k m hkm x₂] at h
    exact sub_eq_zero.mp h.symm
  -- the restrictions to `U` and to `V`
  set rU : (relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₁')).homology k
      ⟶ (relComplex ℤ (TopCat.of U) (pdRelSub U K₁')).homology k
    := (HomologicalComplex.homologyMap (relComplexMap ℤ
        (X₁ := TopCat.of U) (X₂ := TopCat.of (U ∪ V : Set M))
        (pdRelSub U K₁') (pdRelSub (U ∪ V : Set M) K₁')
        (pdIncl (U ∪ V : Set M) U Set.subset_union_left) (fun x hx => hx)) k) with hrU
  set rV : (relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₂')).homology k
      ⟶ (relComplex ℤ (TopCat.of V) (pdRelSub V K₂')).homology k
    := (HomologicalComplex.homologyMap (relComplexMap ℤ
        (X₁ := TopCat.of V) (X₂ := TopCat.of (U ∪ V : Set M))
        (pdRelSub V K₂') (pdRelSub (U ∪ V : Set M) K₂')
        (pdIncl (U ∪ V : Set M) V Set.subset_union_right) (fun x hx => hx)) k) with hrV
  have hD1 : (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of U) (TopCat.of (U ∪ V : Set M))
        (pdIncl (U ∪ V : Set M) U Set.subset_union_left)) m)
      (goodD N c U hU K₁' hK₁'U hK₁'c k m hkm (rU x₁))
      = goodD N c (U ∪ V : Set M) hW K₁' hK₁'W hK₁'c k m hkm x₁ := by
    rw [hrU]
    exact pd_goodD_incl (W := (U ∪ V : Set M)) (V := U) (K := K₁') Set.subset_union_left
      hW hU hK₁'U hK₁'W hK₁'c N c k m hkm x₁
  have hD2 : (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of V) (TopCat.of (U ∪ V : Set M))
        (pdIncl (U ∪ V : Set M) V Set.subset_union_right)) m)
      (goodD N c V hV K₂' hK₂'V hK₂'c k m hkm (rV x₂))
      = goodD N c (U ∪ V : Set M) hW K₂' hK₂'W hK₂'c k m hkm x₂ := by
    rw [hrV]
    exact pd_goodD_incl (W := (U ∪ V : Set M)) (V := V) (K := K₂') Set.subset_union_right
      hW hV hK₂'V hK₂'W hK₂'c N c k m hkm x₂
  have hMV : (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of U) (TopCat.of (U ∪ V : Set M))
        (pdIncl (U ∪ V : Set M) U Set.subset_union_left)) m)
      (goodD N c U hU K₁' hK₁'U hK₁'c k m hkm (rU x₁))
      = (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of V) (TopCat.of (U ∪ V : Set M))
        (pdIncl (U ∪ V : Set M) V Set.subset_union_right)) m)
      (goodD N c V hV K₂' hK₂'V hK₂'c k m hkm (rV x₂)) := by
    rw [hD1, hD2, hD12]
  -- Step 4: exactness of the Mayer-Vietoris sequence
  obtain ⟨t, htU, htV⟩ := pdMV_exact_mid hU hV m
    (goodD N c U hU K₁' hK₁'U hK₁'c k m hkm (rU x₁))
    (goodD N c V hV K₂' hK₂'V hK₂'c k m hkm (rV x₂)) hMV
  clear hMV hD1 hD2 hD12
  -- Step 5: surjectivity of the duality map of `U ∩ V`
  obtain ⟨K₀, hK₀I, hK₀c, s, hs⟩ := hII.hit k m hkm t
  -- Step 6: extending a class on `U ∩ V` to `U ∪ V`
  obtain ⟨K₀₁, K₀₂, hK₀K₀₁, hK₀K₀₂, hK₀₁U, hK₀₂V, hK₀₁c, hK₀₂c, y₁, y₂, hy1, hy2, hy3⟩ :=
    pd_union_extend hU hV hI hUU hVV hII k m hkm hK₀I hK₀c s
  -- the restrictions of `yᵢ` to `U`, `V`
  set rU₀ : (relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₀₁)).homology k
      ⟶ (relComplex ℤ (TopCat.of U) (pdRelSub U K₀₁)).homology k
    := (HomologicalComplex.homologyMap (relComplexMap ℤ
        (X₁ := TopCat.of U) (X₂ := TopCat.of (U ∪ V : Set M))
        (pdRelSub U K₀₁) (pdRelSub (U ∪ V : Set M) K₀₁)
        (pdIncl (U ∪ V : Set M) U Set.subset_union_left) (fun x hx => hx)) k) with hrU₀
  set rV₀ : (relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₀₂)).homology k
      ⟶ (relComplex ℤ (TopCat.of V) (pdRelSub V K₀₂)).homology k
    := (HomologicalComplex.homologyMap (relComplexMap ℤ
        (X₁ := TopCat.of V) (X₂ := TopCat.of (U ∪ V : Set M))
        (pdRelSub V K₀₂) (pdRelSub (U ∪ V : Set M) K₀₂)
        (pdIncl (U ∪ V : Set M) V Set.subset_union_right) (fun x hx => hx)) k) with hrV₀
  have hy1' : goodD N c U hU K₀₁ hK₀₁U hK₀₁c k m hkm (rU₀ y₁)
      = goodD N c U hU K₁' hK₁'U hK₁'c k m hkm (rU x₁) := by
    rw [hrU₀, hy1, hs, htU]
  -- Step 7: injectivity of the duality map of `U`
  have hK₁p0U : K₁' ∪ K₀₁ ⊆ U := Set.union_subset hK₁'U hK₀₁U
  have hK₁p0c : IsCompact (K₁' ∪ K₀₁) := hK₁'c.union hK₀₁c
  have hkillU : goodD N c U hU (K₁' ∪ K₀₁) hK₁p0U hK₁p0c k m hkm
      ((HomologicalComplex.homologyMap (pdRelComplexEnlarge U
          (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁)) k) (rU x₁)
        - (HomologicalComplex.homologyMap (pdRelComplexEnlarge U
          (Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁)) k) (rU₀ y₁)) = 0 := by
    rw [goodD_sub c hU hK₁p0U hK₁p0c k m hkm]
    rw [pd_goodD_natural N c U hU (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁) hK₁'U hK₁p0U
          hK₁'c hK₁p0c k m hkm (rU x₁),
        pd_goodD_natural N c U hU (Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁) hK₀₁U hK₁p0U
          hK₀₁c hK₁p0c k m hkm (rU₀ y₁),
        hy1']
    exact sub_self _
  obtain ⟨K₁'', hK₁p0K₁'', hK₁''U, hK₁''c, hkillU'⟩ :=
    hUU.kill k m hkm (K₁' ∪ K₀₁) hK₁p0U hK₁p0c _ hkillU
  -- the enlarged classes on `U` agree
  have hUcomp : ∀ {A B C : Set M} (h : A ⊆ B) (h' : B ⊆ C)
      (z : (relComplex ℤ (TopCat.of U) (pdRelSub U A)).homology k),
      (HomologicalComplex.homologyMap (pdRelComplexEnlarge U (h.trans h')) k) z
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge U h') k)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge U h) k) z) := by
    intro A B C h h' z
    rw [← pdRelComplexEnlarge_homologyMap_comp (M := M) U h h' k]
    rfl
  have hUeq : (HomologicalComplex.homologyMap (pdRelComplexEnlarge U
        ((Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'')) k) (rU x₁)
      = (HomologicalComplex.homologyMap (pdRelComplexEnlarge U
        ((Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'')) k) (rU₀ y₁) := by
    have h : (HomologicalComplex.homologyMap (pdRelComplexEnlarge U hK₁p0K₁'') k)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge U
            (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁)) k) (rU x₁))
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge U hK₁p0K₁'') k)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge U
            (Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁)) k) (rU₀ y₁)) := by
      have hh := hkillU'
      rw [map_sub, sub_eq_zero] at hh
      exact hh
    rw [← hUcomp (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁) hK₁p0K₁'' (rU x₁),
      ← hUcomp (Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁) hK₁p0K₁'' (rU₀ y₁)] at h
    exact h
  clear hkillU hkillU' hK₀K₀₁ hK₀K₀₂ hy1
  -- Step 8: transport to `U ∪ V` using excision
  have hWeq1 : (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
        ((Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'')) k) x₁
      = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
        ((Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'')) k) y₁ := by
    set rjU := (HomologicalComplex.homologyMap (relComplexMap ℤ
        (X₁ := TopCat.of U) (X₂ := TopCat.of (U ∪ V : Set M))
        (pdRelSub U K₁'') (pdRelSub (U ∪ V : Set M) K₁'')
        (pdIncl (U ∪ V : Set M) U Set.subset_union_left) (fun x hx => hx)) k) with hrjU
    haveI : IsIso rjU := by
      rw [hrjU]
      exact pdCohExcision Set.subset_union_left hU hW hK₁''U hK₁''c k
    have hinj : Function.Injective (ConcreteCategory.hom rjU) :=
      (ModuleCat.mono_iff_injective rjU).mp inferInstance
    have hres1 : (ConcreteCategory.hom rjU)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
            ((Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'')) k) x₁)
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge U
            ((Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'')) k) (rU x₁) := by
      rw [hrjU, hrU]
      exact congrArg (fun (f : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) K₁')).homology k
          ⟶ (relComplex ℤ (TopCat.of U) (pdRelSub U K₁'')).homology k) =>
        (ConcreteCategory.hom f) x₁)
        (pdRelComplexEnlarge_restrict (W := (U ∪ V : Set M)) (U := U) (K := K₁') (K' := K₁'')
          Set.subset_union_left hK₁'U hK₁''U
          ((Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'') k)
    have hres2 : (ConcreteCategory.hom rjU)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
            ((Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'')) k) y₁)
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge U
            ((Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'')) k) (rU₀ y₁) := by
      rw [hrjU, hrU₀]
      exact congrArg (fun (f : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) K₀₁)).homology k
          ⟶ (relComplex ℤ (TopCat.of U) (pdRelSub U K₁'')).homology k) =>
        (ConcreteCategory.hom f) y₁)
        (pdRelComplexEnlarge_restrict (W := (U ∪ V : Set M)) (U := U) (K := K₀₁) (K' := K₁'')
          Set.subset_union_left hK₀₁U hK₁''U
          ((Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁'') k)
    exact hinj (by rw [hres1, hres2, hUeq])
  clear hUeq
  -- Step 9: the same for `V`
  have hy2' : goodD N c V hV K₀₂ hK₀₂V hK₀₂c k m hkm (rV₀ y₂)
      = goodD N c V hV K₂' hK₂'V hK₂'c k m hkm (rV x₂) := by
    rw [hrV₀, hrV, hy2, hs, htV]
  have hK₂p0V : K₂' ∪ K₀₂ ⊆ V := Set.union_subset hK₂'V hK₀₂V
  have hK₂p0c : IsCompact (K₂' ∪ K₀₂) := hK₂'c.union hK₀₂c
  have hkillV : goodD N c V hV (K₂' ∪ K₀₂) hK₂p0V hK₂p0c k m hkm
      ((HomologicalComplex.homologyMap (pdRelComplexEnlarge V
          (Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂)) k) (rV x₂)
        - (HomologicalComplex.homologyMap (pdRelComplexEnlarge V
          (Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂)) k) (rV₀ y₂)) = 0 := by
    rw [goodD_sub c hV hK₂p0V hK₂p0c k m hkm]
    rw [pd_goodD_natural N c V hV (Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂) hK₂'V hK₂p0V
          hK₂'c hK₂p0c k m hkm (rV x₂),
        pd_goodD_natural N c V hV (Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂) hK₀₂V hK₂p0V
          hK₀₂c hK₂p0c k m hkm (rV₀ y₂),
        hy2']
    exact sub_self _
  obtain ⟨K₂'', hK₂p0K₂'', hK₂''V, hK₂''c, hkillV'⟩ :=
    hVV.kill k m hkm (K₂' ∪ K₀₂) hK₂p0V hK₂p0c _ hkillV
  have hVcomp : ∀ {A B C : Set M} (h : A ⊆ B) (h' : B ⊆ C)
      (z : (relComplex ℤ (TopCat.of V) (pdRelSub V A)).homology k),
      (HomologicalComplex.homologyMap (pdRelComplexEnlarge V (h.trans h')) k) z
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge V h') k)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge V h) k) z) := by
    intro A B C h h' z
    rw [← pdRelComplexEnlarge_homologyMap_comp (M := M) V h h' k]
    rfl
  have hVeq : (HomologicalComplex.homologyMap (pdRelComplexEnlarge V
        ((Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'')) k) (rV x₂)
      = (HomologicalComplex.homologyMap (pdRelComplexEnlarge V
        ((Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'')) k) (rV₀ y₂) := by
    have h : (HomologicalComplex.homologyMap (pdRelComplexEnlarge V hK₂p0K₂'') k)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge V
            (Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂)) k) (rV x₂))
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge V hK₂p0K₂'') k)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge V
            (Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂)) k) (rV₀ y₂)) := by
      have hh := hkillV'
      rw [map_sub, sub_eq_zero] at hh
      exact hh
    rw [← hVcomp (Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂) hK₂p0K₂'' (rV x₂),
      ← hVcomp (Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂) hK₂p0K₂'' (rV₀ y₂)] at h
    exact h
  have hWeq2 : (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
        ((Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'')) k) x₂
      = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
        ((Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'')) k) y₂ := by
    set rjV := (HomologicalComplex.homologyMap (relComplexMap ℤ
        (X₁ := TopCat.of V) (X₂ := TopCat.of (U ∪ V : Set M))
        (pdRelSub V K₂'') (pdRelSub (U ∪ V : Set M) K₂'')
        (pdIncl (U ∪ V : Set M) V Set.subset_union_right) (fun x hx => hx)) k) with hrjV
    haveI : IsIso rjV := by
      rw [hrjV]
      exact pdCohExcision Set.subset_union_right hV hW hK₂''V hK₂''c k
    have hinj : Function.Injective (ConcreteCategory.hom rjV) :=
      (ModuleCat.mono_iff_injective rjV).mp inferInstance
    have hres1 : (ConcreteCategory.hom rjV)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
            ((Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'')) k) x₂)
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge V
            ((Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'')) k) (rV x₂) := by
      rw [hrjV, hrV]
      exact congrArg (fun (f : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) K₂')).homology k
          ⟶ (relComplex ℤ (TopCat.of V) (pdRelSub V K₂'')).homology k) =>
        (ConcreteCategory.hom f) x₂)
        (pdRelComplexEnlarge_restrict (W := (U ∪ V : Set M)) (U := V) (K := K₂') (K' := K₂'')
          Set.subset_union_right hK₂'V hK₂''V
          ((Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'') k)
    have hres2 : (ConcreteCategory.hom rjV)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
            ((Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'')) k) y₂)
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge V
            ((Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'')) k) (rV₀ y₂) := by
      rw [hrjV, hrV₀]
      exact congrArg (fun (f : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) K₀₂)).homology k
          ⟶ (relComplex ℤ (TopCat.of V) (pdRelSub V K₂'')).homology k) =>
        (ConcreteCategory.hom f) y₂)
        (pdRelComplexEnlarge_restrict (W := (U ∪ V : Set M)) (U := V) (K := K₀₂) (K' := K₂'')
          Set.subset_union_right hK₀₂V hK₂''V
          ((Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂'') k)
    exact hinj (by rw [hres1, hres2, hVeq])
  clear hVeq hkillV hkillV' hy2 hy2'
  -- Step 10: assembly
  have hin1 : K₁' ⊆ K₁'' :=
    (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁''
  have hin0 : K₀₁ ⊆ K₁'' :=
    (Set.subset_union_right : K₀₁ ⊆ K₁' ∪ K₀₁).trans hK₁p0K₁''
  have hin2 : K₂' ⊆ K₂'' :=
    (Set.subset_union_left : K₂' ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂''
  have hin02 : K₀₂ ⊆ K₂'' :=
    (Set.subset_union_right : K₀₂ ⊆ K₂' ∪ K₀₂).trans hK₂p0K₂''
  have hsub1 : K₁'' ⊆ K₁'' ∪ K₂'' := Set.subset_union_left
  have hsub2 : K₂'' ⊆ K₁'' ∪ K₂'' := Set.subset_union_right
  have hK1'' : K₁' ⊆ K₁'' ∪ K₂'' := hin1.trans hsub1
  have hK0'' : K₀₁ ⊆ K₁'' ∪ K₂'' := hin0.trans hsub1
  have hK2'' : K₂' ⊆ K₁'' ∪ K₂'' := hin2.trans hsub2
  have hK02'' : K₀₂ ⊆ K₁'' ∪ K₂'' := hin02.trans hsub2
  have huni : K₀₁ ∪ K₀₂ ⊆ K₁'' ∪ K₂'' := Set.union_subset_union hin0 hin02
  have hmid2 : K₁' ∪ K₂' ⊆ K₁'' ∪ K₂'' := Set.union_subset_union hin1 hin2
  have hK'U : K₁'' ∪ K₂'' ⊆ (U ∪ V : Set M) := Set.union_subset_union hK₁''U hK₂''V
  have hK'c : IsCompact (K₁'' ∪ K₂'') := hK₁''c.union hK₂''c
  have hKK' : K ⊆ K₁'' ∪ K₂'' := hK12.trans (hmid.trans hmid2)
  -- evaluation forms of the enlargement identities
  have evCongr : ∀ {A B : Set M} (h h' : A ⊆ B)
      (z : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) A)).homology k),
      (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) h) k) z
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) h') k) z := by
    intro A B h h' z
    exact congrArg (fun (f : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) A)).homology k
        ⟶ (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) B)).homology k) => (ConcreteCategory.hom f) z)
      (congrArg (fun (g : relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) A) ⟶ relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) B)) => HomologicalComplex.homologyMap g k)
        (pdRelComplexEnlarge_congr_h (U ∪ V : Set M) h h'))
  have evComp : ∀ {A B C : Set M} (h : A ⊆ B) (h' : B ⊆ C)
      (z : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) A)).homology k),
      (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) (h.trans h')) k) z
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) h') k)
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) h) k) z) := by
    intro A B C h h' z
    rw [← pdRelComplexEnlarge_homologyMap_comp (M := M) (U ∪ V : Set M) h h' k]
    rfl
  -- the two `x`-sides agree
  have key : (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hK1'') k) x₁
      = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hK2'') k) x₂ := by
    calc (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hK1'') k) x₁
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hsub1) k)
            ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hin1) k) x₁) :=
          evComp hin1 hsub1 x₁
      _ = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hsub1) k)
            ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hin0) k) y₁) := by
          rw [show (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hin1) k) x₁
              = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hin0) k) y₁
              from hWeq1]
      _ = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hK0'') k) y₁ :=
          (evComp hin0 hsub1 y₁).symm
      _ = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) huni) k)
            ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
              (Set.subset_union_left : K₀₁ ⊆ K₀₁ ∪ K₀₂)) k) y₁) := by
          rw [evCongr hK0'' ((Set.subset_union_left : K₀₁ ⊆ K₀₁ ∪ K₀₂).trans huni) y₁]
          exact evComp (Set.subset_union_left : K₀₁ ⊆ K₀₁ ∪ K₀₂) huni y₁
      _ = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) huni) k)
            ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
              (Set.subset_union_right : K₀₂ ⊆ K₀₁ ∪ K₀₂)) k) y₂) := by
          rw [show (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
                (Set.subset_union_left : K₀₁ ⊆ K₀₁ ∪ K₀₂)) k) y₁
              = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
                (Set.subset_union_right : K₀₂ ⊆ K₀₁ ∪ K₀₂)) k) y₂ from hy3]
      _ = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hK02'') k) y₂ := by
          rw [evCongr ((Set.subset_union_right : K₀₂ ⊆ K₀₁ ∪ K₀₂).trans huni) hK02'' y₂]
          exact (evComp (Set.subset_union_right : K₀₂ ⊆ K₀₁ ∪ K₀₂) huni y₂).symm
      _ = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hsub2) k)
            ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hin02) k) y₂) := by
          rw [evCongr hK02'' (hin02.trans hsub2) y₂]
          exact evComp hin02 hsub2 y₂
      _ = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hsub2) k)
            ((HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hin2) k) x₂) := by
          rw [show (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hin02) k) y₂
              = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hin2) k) x₂
              from hWeq2.symm]
      _ = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hK2'') k) x₂ :=
          (evComp hin2 hsub2 x₂).symm
  refine ⟨K₁'' ∪ K₂'', hKK', hK'U, hK'c, ?_⟩
  rw [evCongr hKK' (hK12.trans (hmid.trans hmid2))]
  rw [evComp hK12 (hmid.trans hmid2)]
  rw [evComp hmid hmid2]
  rw [show (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M) hK12) k) x = x₀
      from hx₀def.symm]
  rw [hsplit, map_sub]
  rw [← evComp (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₂') hmid2 x₁,
    ← evComp (Set.subset_union_right : K₂' ⊆ K₁' ∪ K₂') hmid2 x₂,
    evCongr ((Set.subset_union_left : K₁' ⊆ K₁' ∪ K₂').trans hmid2) hK1'' x₁,
    evCongr ((Set.subset_union_right : K₂' ⊆ K₁' ∪ K₂').trans hmid2) hK2'' x₂,
    key, sub_self]

end

end Work.Cohomology
