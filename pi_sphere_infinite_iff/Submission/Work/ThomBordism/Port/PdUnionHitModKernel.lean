-- Copied verbatim from `Submission.Work.Cohomology.pd_union_hit_mod_kernel`, with imports re-routed to the
-- clash-free chain (`Work.Thom.Relocate.*` / the local copies in this directory), exactly as
-- `Submission/Work/Thom/README.md` ADDENDUM 16 did for the Thom area: the workspace contains
-- two *identical* duplicate modules `Work.Cohomology.Crux.ovlRestrictionSurjective` and
-- `Work.Cohomology.Crux.vkCruxRestr`, so a module importing one cannot be combined with a
-- module importing the other.  The `Work.ThomBordism` chapter imports
-- `ovlRestrictionSurjective` (via `Interface.lean`), hence these copies.  All declarations
-- keep their original names and proofs.
import Mathlib
import Submission.Work.Cohomology.pd_small_union_iso
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.pd_good
-- Re-pointed to the original chain (Islands subproject, 2026): the `Thom/Relocate` copies of
-- the Poincaré-duality chain declared the same names as the `Cohomology/` originals.  The
-- originals are now re-routed (`Crux/vk_transgression_cap_weak.lean` imports the `ovl` copies),
-- so the copies are no longer needed here and the two modules can be imported together.
import Submission.Work.Cohomology.pd_union_extend
import Submission.Work.Cohomology.homologyMV_honest_les
import Submission.Work.Cohomology.pd_ab_clean
import Submission.Work.Cohomology.pd_hatcher_W
import Submission.Work.Cohomology.pd_inter_rep
import Submission.Work.Cohomology.pd_mvdelta_apply
import Submission.Work.Cohomology.pd_union_crux_zero
import Submission.Work.Cohomology.pd_goodD_incl
import Submission.Work.Cohomology.pd_goodD_natural
import Submission.Work.ThomBordism.Port.PdRestrictionInjective
-- Re-pointed to the original chain (Islands subproject, 2026): the `Thom/Relocate` copies of
-- the Poincaré-duality chain declared the same names as the `Cohomology/` originals.  The
-- originals are now re-routed (`Crux/vk_transgression_cap_weak.lean` imports the `ovl` copies),
-- so the copies are no longer needed here and the two modules can be imported together.
import Submission.Work.Cohomology.pd_glue2
import Submission.Work.Cohomology.pd_crux_weak3
import Submission.Work.Cohomology.pd_alpha2_zeta
import Submission.Work.Cohomology.pd_alpha2_localFundClass
import Submission.Work.Cohomology.pdABdelta_natural
import Submission.Work.Cohomology.pd_ab_enlarge
import Submission.Work.Cohomology.pdABCoh_quasiIso
import Submission.Work.Cohomology.pd_ab_incl_rel
import Submission.Work.Cohomology.pdABInclRel_comp_pdABEnlarge
import Submission.Work.Cohomology.pd_goodD_rep
import Submission.Work.Cohomology.smallLift_injective
import Submission.Work.Cohomology.cap_d
import Submission.Work.Cohomology.cap_mem_range_inclChains
import Submission.Work.Cohomology.pd_compact_pieces
-- Re-pointed to the original chain (Islands subproject, 2026): the `Thom/Relocate` copies of
-- the Poincaré-duality chain declared the same names as the `Cohomology/` originals.  The
-- originals are now re-routed (`Crux/vk_transgression_cap_weak.lean` imports the `ovl` copies),
-- so the copies are no longer needed here and the two modules can be imported together.
import Submission.Work.Cohomology.pd_split_setup
import Submission.Work.Cohomology.pd_us_ab_resolve
import Submission.Work.Cohomology.pd_us_cycles_eq_of_class_eq
import Submission.Work.ThomBordism.Port.PdEvalEnlargeZero
import Submission.Work.Cohomology.pd_crux_chain
import Submission.Work.Cohomology.cokerSmallLemmas

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## The crux chain identity with an explicit witness -/

/-- **The crux chain identity, with the boundary made explicit.** -/
theorem pd_crux_witness {X : TopCat} {K L : Set X} {k mj : ℕ}
    (α₁ α₂ α₃ : (Work.Cohomology.singularChains ℤ X).X (k + (mj + 1)))
    (φ φA φB : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) k)
    (hφA : φA ∈ Work.Cohomology.relKern ℤ X Kᶜ k)
    (hφB : φB ∈ Work.Cohomology.relKern ℤ X Lᶜ k)
    (hlift : φ = φA - φB)
    (hL : ∃ e', (Work.Cohomology.inclChains X Lᶜ).f (k + mj) e'
      = (Work.Cohomology.singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁)
    (hK : ∃ f', (Work.Cohomology.inclChains X Kᶜ).f (k + mj) f'
      = (Work.Cohomology.singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃)
    (hd : ∃ g', (Work.Cohomology.inclChains X ((K ∪ L)ᶜ)).f (k + mj) g'
      = (Work.Cohomology.singularChains ℤ X).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃))
    (hφd : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φ = 0) :
    (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj)
        (Work.Cohomology.cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₁)
      - (-1 : ℤ) ^ (k + 1) •
          Work.Cohomology.cap ℤ (TopCat.toSSet.obj X)
            (Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA) mj
            ((Work.Cohomology.capIdx k mj) ▸ α₂))
      = - (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj)
          (Work.Cohomology.cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂)) := by
  obtain ⟨e', he'⟩ := hL
  obtain ⟨f', hf'⟩ := hK
  obtain ⟨g', hg'⟩ := hd
  have hsub : ((K ∪ L)ᶜ : Set X) ⊆ Kᶜ :=
    Set.compl_subset_compl.mpr Set.subset_union_left
  have hzeroB : cap ℤ (TopCat.toSSet.obj X) φB mj
      ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁) = 0 := by
    rw [← he']
    exact cap_inclChains_eq_zero X Lᶜ φB hφB mj e'
  have hzeroA3 : cap ℤ (TopCat.toSSet.obj X) φA mj
      ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃) = 0 := by
    rw [← hf']
    exact cap_inclChains_eq_zero X Kᶜ φA hφA mj f'
  have hzeroAtot : cap ℤ (TopCat.toSSet.obj X) φA mj
      ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃)) = 0 := by
    rw [← hg']
    exact cap_eq_zero_of_mem_range_inclChains X Kᶜ ((K ∪ L)ᶜ) hsub φA hφA ⟨g', rfl⟩
  have hdsum : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃)
      = (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁
        + (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂
        + (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃ := by
    rw [map_add, map_add]
  have hA2 : cap ℤ (TopCat.toSSet.obj X) φA mj
        ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂)
      = - cap ℤ (TopCat.toSSet.obj X) φA mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁) := by
    have hsum : cap ℤ (TopCat.toSSet.obj X) φA mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁)
        + cap ℤ (TopCat.toSSet.obj X) φA mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂) = 0 := by
      have h := hzeroAtot
      rw [hdsum] at h
      rw [map_add, map_add, hzeroA3, add_zero] at h
      exact h
    exact eq_neg_of_add_eq_zero_right hsum
  have hP : cap ℤ (TopCat.toSSet.obj X) φ mj
        ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁)
      = - cap ℤ (TopCat.toSSet.obj X) φA mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂) := by
    rw [hlift, cap_sub_apply, hzeroB, sub_zero, hA2, neg_neg]
  have hA : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj))
        (cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₁)
      = (-1 : ℤ) ^ k • cap ℤ (TopCat.toSSet.obj X) φ mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁) := by
    have h := cap_d ℤ (TopCat.toSSet.obj X) (n := k) (m := mj) φ α₁
    rw [hφd, cap_zero, LinearMap.zero_apply, sub_zero] at h
    exact h.trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ (↑((singularChains ℤ X).X mj)))
        ((-1 : ℤ) ^ k) (cap ℤ (TopCat.toSSet.obj X) φ mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁)))
  have hB : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj))
        (cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂)
      = (-1 : ℤ) ^ k • (cap ℤ (TopCat.toSSet.obj X) φA mj
            ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂)
          - cap ℤ (TopCat.toSSet.obj X)
            (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂)) := by
    have h := cap_d ℤ (TopCat.toSSet.obj X) (n := k) (m := mj) φA α₂
    exact h.trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ (↑((singularChains ℤ X).X mj)))
        ((-1 : ℤ) ^ k) (cap ℤ (TopCat.toSSet.obj X) φA mj
            ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂)
          - cap ℤ (TopCat.toSSet.obj X)
            (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂)))
  have key : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj)
        (cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₁)
      - (-1 : ℤ) ^ (k + 1) •
          cap ℤ (TopCat.toSSet.obj X)
            (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂))
      = - (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj)
        (cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂)) := by
    rw [hA, hP, hB]
    rw [zsmul_neg]
    rw [show (-1 : ℤ) ^ (k + 1) = -(-1 : ℤ) ^ k by rw [pow_succ]; ring, neg_zsmul, zsmul_sub]
    abel
  exact key

/-! ## The transport of a class of the intersection to the union

Spliced from `Submission/Work/Cohomology/pd_transport_psi.lean` (proved by a colleague). -/


/-- The underlying cochain of the differential of the relative cochain complex is `cochainDiff`. -/
theorem relComplex_d_coe {X : TopCat} {A : Set X} {n : ℕ} (x : (relComplex ℤ X A).X n) :
    (((relComplex ℤ X A).d n (n + 1)).hom x).1 = cochainDiff ℤ (TopCat.toSSet.obj X) x.1 := by
  rw [relComplex_d, relDiff, ModuleCat.hom_ofHom]
  exact (relDiffLM_coe ℤ X A n x).trans (pd_us_ab_resolve_singularD_eq_cochainDiff X n x.1)

/-- A relative cochain is a cocycle as soon as its underlying cochain is a cocycle. -/
theorem relComplex_d_eq_zero {X : TopCat} {A : Set X} {n : ℕ}
    (x : (relComplex ℤ X A).X n)
    (h : cochainDiff ℤ (TopCat.toSSet.obj X) (n := n) x.1 = 0) :
    (relComplex ℤ X A).d n (n + 1) x = 0 := by
  apply Subtype.ext
  rw [relComplex_d_coe x]
  exact h

/-- The enlargement of the excluded set does not change the underlying cochain. -/
theorem pdRelComplexEnlarge_coe {M : TopCat} {W : Set M} {K K' : Set M} (h : K ⊆ K')
    {n : ℕ} (x : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).X n) :
    (((pdRelComplexEnlarge W h).f n).hom x).1 = x.1 := by
  rw [pdRelComplexEnlarge, relComplexMap_f, ModuleCat.hom_ofHom]
  exact PDABClean.relMapLM_id_coe (TopCat.of W) (pdRelSub_mono h) n x

/-- The underlying cochain of the `iCycles` of an enlarged cycle is the underlying cochain of the
original cycle. -/
theorem pdRelComplexEnlarge_iCycles_coe {M : TopCat} {W : Set M} {K K' : Set M} (h : K ⊆ K')
    {n : ℕ} (z : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).cycles n) :
    (((relComplex ℤ (TopCat.of W) (pdRelSub W K')).iCycles n)
      ((HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h) n).hom z)).1
      = (((relComplex ℤ (TopCat.of W) (pdRelSub W K)).iCycles n) z).1 := by
  have h1 : (ConcreteCategory.hom ((relComplex ℤ (TopCat.of W) (pdRelSub W K')).iCycles n))
        (ConcreteCategory.hom (HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h) n) z)
      = ConcreteCategory.hom ((pdRelComplexEnlarge W h).f n)
        (ConcreteCategory.hom ((relComplex ℤ (TopCat.of W) (pdRelSub W K)).iCycles n) z) := by
    have hh := congrArg (fun (g : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).cycles n ⟶
        (relComplex ℤ (TopCat.of W) (pdRelSub W K')).X n) =>
          (ConcreteCategory.hom g) z)
      (HomologicalComplex.cyclesMap_i (pdRelComplexEnlarge W h) n)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  exact (congrArg Subtype.val h1).trans (pdRelComplexEnlarge_coe h _)

/-- **A relative cycle whose class dies after enlarging the excluded set has a primitive.**

If `z` is a relative cycle of `(W, W∖K)` whose cohomology class vanishes after enlarging `K` to
`K'`, then there is a relative cochain `φ ∈ C^k(W, W∖K')` whose coboundary is the underlying cochain
of `z`. -/
theorem pd_enlarge_primitive {M : TopCat} {W : Set M} {K K' : Set M} (h : K ⊆ K') {k : ℕ}
    (z : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).cycles (k + 1))
    (hz : (HomologicalComplex.homologyMap (pdRelComplexEnlarge W h) (k + 1)).hom
        ((HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of W) (pdRelSub W K)) (k + 1)) z) = 0) :
    ∃ (φ : (relComplex ℤ (TopCat.of W) (pdRelSub W K')).X k),
      (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of W)) (n := k) φ.1
        = (((relComplex ℤ (TopCat.of W) (pdRelSub W K)).iCycles (k + 1) z)).1) ∧
      (φ.1 ∈ relKern ℤ (TopCat.of W) (pdRelSub W K') k) := by
  have hzA0 : (HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of W) (pdRelSub W K')) (k + 1)).hom
      ((HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h) (k + 1)).hom z) = 0 := by
    have hnat := congrArg (fun (g : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).cycles (k+1) ⟶
        HomologicalComplex.homology (relComplex ℤ (TopCat.of W) (pdRelSub W K')) (k+1)) =>
          (ModuleCat.Hom.hom g) z)
      (HomologicalComplex.homologyπ_naturality (φ := pdRelComplexEnlarge W h) (i := k + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
    rw [← hnat]
    exact hz
  obtain ⟨φ, hφ⟩ := pd_us_ab_resolve_exists_of_homologyπ_eq_zero
    (relComplex ℤ (TopCat.of W) (pdRelSub W K')) k
    ((HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h) (k + 1)).hom z) hzA0
  refine ⟨φ, ?_, φ.2⟩
  have h1 : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of W)) (n := k) φ.1
      = (((relComplex ℤ (TopCat.of W) (pdRelSub W K')).iCycles (k + 1))
          ((HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h) (k + 1)).hom z)).1 := by
    rw [← relComplex_d_coe φ]
    exact congrArg Subtype.val hφ
  rw [h1, pdRelComplexEnlarge_iCycles_coe h z]

/-- **Enlargement of the excluded set after restricting to a smaller open set.**

If a class of `H^n(W, W∖K)` has the property that its restriction to a smaller open `Z ⊆ W` dies
after enlarging `K` to `K' ⊆ Z`, then the class itself dies after that enlargement.  The point is
that the restriction `H^n(W,W∖K') → H^n(Z,Z∖K')` is an isomorphism by excision (`pdCohExcision`),
while the enlargement is natural (`pdRelComplexEnlarge_id_map`). -/
theorem pd_transport_enlarge_zero {M : TopCat} [T2Space M] {W Z : Set M} (hZW : Z ⊆ W)
    (hZ : IsOpen Z) (hW : IsOpen W) {K K' : Set M} (hKK' : K ⊆ K') (hK'Z : K' ⊆ Z)
    (hK'c : IsCompact K') {n : ℕ}
    (y : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology n)
    (hy : (HomologicalComplex.homologyMap (pdRelComplexEnlarge Z hKK') n).hom
            ((HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub Z K) (pdRelSub W K)
              (pdIncl W Z hZW) (fun x hx => hx)) n).hom y) = 0) :
    (HomologicalComplex.homologyMap (pdRelComplexEnlarge W hKK') n).hom y = 0 := by
  have hsq := pdRelComplexEnlarge_id_map (M := M) (W := W) (I := Z) hZW (K := K) (K' := K') hKK'
  haveI hiso : IsIso (HomologicalComplex.homologyMap (relComplexMap ℤ
      (X₁ := TopCat.of Z) (X₂ := TopCat.of W) (pdRelSub Z K') (pdRelSub W K')
      (pdIncl W Z hZW) (fun x hx => hx)) n) :=
    pdCohExcision (M := M) (W := W) (U := Z) hZW hZ hW hK'Z hK'c n
  have hhom := congrArg (fun φ => HomologicalComplex.homologyMap φ n) hsq
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hhom
  have happ := congrArg (fun φ => φ.hom y) hhom
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at happ
  have hzero := happ.trans hy
  have h2 := IsIso.hom_inv_id_apply (HomologicalComplex.homologyMap (relComplexMap ℤ
      (X₁ := TopCat.of Z) (X₂ := TopCat.of W) (pdRelSub Z K') (pdRelSub W K')
      (pdIncl W Z hZW) (fun x hx => hx)) n)
      ((HomologicalComplex.homologyMap (pdRelComplexEnlarge W hKK') n) y)
  rw [hzero] at h2
  simpa using h2.symm

/-! ## The target -/

/-- **Transport of a class of the intersection to the union.**  Given a class `w` on `U ∩ V`
supported in the compact `K₀ ⊆ U ∩ V` whose duality class dies in the Mayer–Vietoris middle term,
there are compact `K₁ ⊆ U`, `K₂ ⊆ V` containing `K₀`, a relative cocycle `zψ` of `(U∪V, (U∪V)∖K₀)`
representing the excision-preimage of `w`, cochains `φA`, `φB` with `dφA = dφB` equal to the
underlying cochain of `zψ` which kill `K₁ᶜ`- and `K₂ᶜ`-chains, and the relative cocycle `zx` of
`(U∪V, (U∪V)∖(K₁∪K₂))` with underlying cochain `φA - φB`.  Finally the restriction of `zψ` to the
intersection is `w`. -/
theorem pd_transport_psi {M : TopCat} [T2Space M] {N : ℕ}
    {c : (singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    (hUU : Good N c U hU) (hVV : Good N c V hV)
    (hII : Good N c (U ∩ V) hI)
    (k m' : ℕ) (hN : k + (m' + 1) = N) (hN' : k + 1 + m' = N)
    {K₀ : Set M} (hK₀I : K₀ ⊆ U ∩ V) (hK₀c : IsCompact K₀)
    (w : (relComplex ℤ (TopCat.of (U ∩ V : Set M))
      (pdRelSub (U ∩ V : Set M) K₀)).homology (k + 1))
    (hdead : (HomologicalComplex.homologyMap (mvLeft U V) m').hom
      (goodD N c (U ∩ V : Set M) hI K₀ hK₀I hK₀c (k + 1) m' hN' w) = 0) :
    ∃ (K₁ K₂ : Set M) (hK₁U : K₁ ⊆ U) (hK₂V : K₂ ⊆ V)
      (hK₀K₁ : K₀ ⊆ K₁) (hK₀K₂ : K₀ ⊆ K₂)
      (hK₁c : IsCompact K₁) (hK₂c : IsCompact K₂)
      (zx : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).cycles k)
      (zψ : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₀)).cycles (k + 1))
      (φA φB : ↑((singularCochainComplex ℤ (TopCat.of (U ∪ V : Set M))).X k)),
      (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M)))
        (n := k) φA
        = (((relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) K₀)).iCycles (k + 1) zψ).1)) ∧
      (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M)))
        (n := k) φB
        = (((relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) K₀)).iCycles (k + 1) zψ).1)) ∧
      (φA ∈ relKern ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₁) k) ∧
      (φB ∈ relKern ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₂) k) ∧
      (((relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k zx).1
        = φA - φB) ∧
      ((HomologicalComplex.homologyMap (relComplexMap ℤ
        (pdRelSub (U ∩ V : Set M) K₀)
        (pdRelSub (U ∪ V : Set M) K₀)
        (pdIncl (U ∪ V : Set M) (U ∩ V)
          (Set.inter_subset_left.trans Set.subset_union_left)) (fun x hx => hx)) (k + 1)).hom
        ((HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) K₀)) (k + 1)) zψ) = w) := by
  classical
  have hK₀U : K₀ ⊆ U := hK₀I.trans Set.inter_subset_left
  have hK₀V : K₀ ⊆ V := hK₀I.trans Set.inter_subset_right
  have hW : IsOpen (U ∪ V : Set M) := hU.union hV
  -- ### the two components of `hdead`
  have hinclU : inclUVU U V = pdIncl U (U ∩ V) Set.inter_subset_left := by
    apply TopCat.ext; intro x; rfl
  have hinclV : inclUVV U V = pdIncl V (U ∩ V) Set.inter_subset_right := by
    apply TopCat.ext; intro x; rfl
  have hLfst : mvLeft U V ≫ biprod.fst (X := singularChains ℤ (TopCat.of U))
      (Y := singularChains ℤ (TopCat.of V))
      = chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of U) (inclUVU U V) := by
    rw [mvLeft]; exact biprod.lift_fst _ _
  have hLsnd : mvLeft U V ≫ biprod.snd (X := singularChains ℤ (TopCat.of U))
      (Y := singularChains ℤ (TopCat.of V))
      = chainMap ℤ (TopCat.of (U ∩ V : Set M)) (TopCat.of V) (inclUVV U V) := by
    rw [mvLeft]; exact biprod.lift_snd _ _
  have hD0 : (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (U ∩ V : Set M))
      (TopCat.of U) (inclUVU U V)) m').hom
      (goodD N c (U ∩ V : Set M) hI K₀ hK₀I hK₀c (k + 1) m' hN' w) = 0 := by
    have hfst : HomologicalComplex.homologyMap (mvLeft U V) m' ≫
        HomologicalComplex.homologyMap (biprod.fst (X := singularChains ℤ (TopCat.of U))
          (Y := singularChains ℤ (TopCat.of V))) m'
        = HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (U ∩ V : Set M))
            (TopCat.of U) (inclUVU U V)) m' := by
      rw [← HomologicalComplex.homologyMap_comp, hLfst]
    have h := congrArg (fun (g : HomologicalComplex.homology
        (singularChains ℤ (TopCat.of (U ∩ V : Set M))) m' ⟶
        HomologicalComplex.homology (singularChains ℤ (TopCat.of U)) m') =>
          (ModuleCat.Hom.hom g)
            (goodD N c (U ∩ V : Set M) hI K₀ hK₀I hK₀c (k + 1) m' hN' w)) hfst
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hdead, map_zero] using h.symm
  have hD1 : (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (U ∩ V : Set M))
      (TopCat.of V) (inclUVV U V)) m').hom
      (goodD N c (U ∩ V : Set M) hI K₀ hK₀I hK₀c (k + 1) m' hN' w) = 0 := by
    have hsnd : HomologicalComplex.homologyMap (mvLeft U V) m' ≫
        HomologicalComplex.homologyMap (biprod.snd (X := singularChains ℤ (TopCat.of U))
          (Y := singularChains ℤ (TopCat.of V))) m'
        = HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (U ∩ V : Set M))
            (TopCat.of V) (inclUVV U V)) m' := by
      rw [← HomologicalComplex.homologyMap_comp, hLsnd]
    have h := congrArg (fun (g : HomologicalComplex.homology
        (singularChains ℤ (TopCat.of (U ∩ V : Set M))) m' ⟶
        HomologicalComplex.homology (singularChains ℤ (TopCat.of V)) m') =>
          (ModuleCat.Hom.hom g)
            (goodD N c (U ∩ V : Set M) hI K₀ hK₀I hK₀c (k + 1) m' hN' w)) hsnd
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hdead, map_zero] using h.symm
  -- ### the class `y ∈ H^{k+1}(U∪V, (U∪V)∖K₀)` whose restriction to `U ∩ V` is `w`
  haveI hIso : IsIso (pdMapMtIHom U V K₀ (k + 1)) :=
    pdMapMtIHom_isIso hU hV hK₀U hK₀V hK₀c (k + 1)
  let z : (relComplex ℤ M (K₀ᶜ)).homology (k + 1) :=
    (CategoryTheory.inv (pdMapMtIHom U V K₀ (k + 1))).hom w
  let y : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) K₀)).homology (k + 1) :=
    (pdMapMtWHom U V K₀ (k + 1)).hom z
  have hz : (pdMapMtIHom U V K₀ (k + 1)).hom z = w := IsIso.inv_hom_id_apply _ _
  have hy : (pdMapInterHom U V K₀ (k + 1)).hom y = w := by
    have h := pdRestr_comp_subtype_apply (M := M) (V := U ∩ V) (W := U ∪ V) (K := K₀)
      (Set.inter_subset_left.trans Set.subset_union_left) (k + 1) z
    exact h.trans hz
  let yU : (relComplex ℤ (TopCat.of U) (pdRelSub U K₀)).homology (k + 1) :=
    (pdMapWUHom U V K₀ (k + 1)).hom y
  let yV : (relComplex ℤ (TopCat.of V) (pdRelSub V K₀)).homology (k + 1) :=
    (pdMapWVHom U V K₀ (k + 1)).hom y
  have hσU : (HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub (U ∩ V : Set M) K₀)
      (pdRelSub U K₀) (pdIncl U (U ∩ V) Set.inter_subset_left) (fun x hx => hx)) (k + 1)).hom
      yU = w := by
    have h := pdRestr_comp_apply (M := M) (V := U ∩ V) (U := U) (W := U ∪ V) (K := K₀)
      Set.inter_subset_left Set.subset_union_left (k + 1) y
    exact h.trans hy
  have hσV : (HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub (U ∩ V : Set M) K₀)
      (pdRelSub V K₀) (pdIncl V (U ∩ V) Set.inter_subset_right) (fun x hx => hx)) (k + 1)).hom
      yV = w := by
    have h := pdRestr_comp_apply (M := M) (V := U ∩ V) (U := V) (W := U ∪ V) (K := K₀)
      Set.inter_subset_right Set.subset_union_right (k + 1) y
    have hc := pdMapInterHom_congr_h (M := M) (U := U) (V := V) (K := K₀)
      (h := Set.inter_subset_right.trans Set.subset_union_right)
      (h' := Set.inter_subset_left.trans Set.subset_union_left) (k + 1) y
    exact h.trans (hc.trans hy)
  -- ### the duality classes of the two restrictions vanish
  have hDU : goodD N c U hU K₀ hK₀U hK₀c (k + 1) m' hN' yU = 0 := by
    have hnat := pd_goodD_incl (M := M) (W := U) (V := U ∩ V) Set.inter_subset_left hU hI
      hK₀I hK₀U hK₀c N c (k + 1) m' hN' yU
    rw [hσU] at hnat
    have hconv : HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (U ∩ V : Set M))
        (TopCat.of U) (inclUVU U V)) m'
        = HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (U ∩ V : Set M))
            (TopCat.of U) (pdIncl U (U ∩ V) Set.inter_subset_left)) m' := by
      rw [hinclU]
    rw [← hnat, ← hconv]
    exact hD0
  have hDV : goodD N c V hV K₀ hK₀V hK₀c (k + 1) m' hN' yV = 0 := by
    have hnat := pd_goodD_incl (M := M) (W := V) (V := U ∩ V) Set.inter_subset_right hV hI
      hK₀I hK₀V hK₀c N c (k + 1) m' hN' yV
    rw [hσV] at hnat
    have hconv : HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (U ∩ V : Set M))
        (TopCat.of V) (inclUVV U V)) m'
        = HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (U ∩ V : Set M))
            (TopCat.of V) (pdIncl V (U ∩ V) Set.inter_subset_right)) m' := by
      rw [hinclV]
    rw [← hnat, ← hconv]
    exact hD1
  -- ### the enlargements inside `U` and inside `V`
  obtain ⟨K₁, hK₀K₁, hK₁U, hK₁c, hkillU⟩ :=
    hUU.kill (k + 1) m' hN' K₀ hK₀U hK₀c yU hDU
  obtain ⟨K₂, hK₀K₂, hK₂V, hK₂c, hkillV⟩ :=
    hVV.kill (k + 1) m' hN' K₀ hK₀V hK₀c yV hDV
  have hkillUW : (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V) hK₀K₁)
      (k + 1)).hom y = 0 :=
    pd_transport_enlarge_zero (M := M) (W := U ∪ V) (Z := U) Set.subset_union_left hU hW
      hK₀K₁ hK₁U hK₁c (n := k + 1) y hkillU
  have hkillVW : (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V) hK₀K₂)
      (k + 1)).hom y = 0 :=
    pd_transport_enlarge_zero (M := M) (W := U ∪ V) (Z := V) Set.subset_union_right hV hW
      hK₀K₂ hK₂V hK₂c (n := k + 1) y hkillV
  -- ### a cycle `zψ` representing `y`
  obtain ⟨zψ, hzψ⟩ := (ModuleCat.epi_iff_surjective
    (HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) K₀)) (k + 1))).mp inferInstance y
  -- ### the two primitive cochains
  have hzeA : (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V) hK₀K₁) (k + 1)).hom
      ((HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₀)) (k + 1)) zψ) = 0 := by
    rw [hzψ]; exact hkillUW
  obtain ⟨φA, hφAd, hφAmem⟩ := pd_enlarge_primitive (M := M) (W := U ∪ V) (K := K₀) (K' := K₁)
    hK₀K₁ (k := k) zψ hzeA
  have hzeB : (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V) hK₀K₂) (k + 1)).hom
      ((HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₀)) (k + 1)) zψ) = 0 := by
    rw [hzψ]; exact hkillVW
  obtain ⟨φB, hφBd, hφBmem⟩ := pd_enlarge_primitive (M := M) (W := U ∪ V) (K := K₀) (K' := K₂)
    hK₀K₂ (k := k) zψ hzeB
  -- ### the class `zx` of the union of the two supports
  have hmemAB : φA.1 - φB.1 ∈ relKern ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)) k := by
    have hA : φA.1 ∈ relKern ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)) k :=
      relKern_mono (R := ℤ) (X := TopCat.of (U ∪ V : Set M))
        (A := pdRelSub (U ∪ V : Set M) K₁) (C := pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))
        (pdRelSub_mono (Set.subset_union_left : K₁ ⊆ K₁ ∪ K₂)) (n := k) hφAmem
    have hB : φB.1 ∈ relKern ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)) k :=
      relKern_mono (R := ℤ) (X := TopCat.of (U ∪ V : Set M))
        (A := pdRelSub (U ∪ V : Set M) K₂) (C := pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))
        (pdRelSub_mono (Set.subset_union_right : K₂ ⊆ K₁ ∪ K₂)) (n := k) hφBmem
    exact Submodule.sub_mem _ hA hB
  let ψ : Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) k := φA.1 - φB.1
  have hψmem : ψ ∈ relKern ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)) k := hmemAB
  have hψd : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) ψ = 0 := by
    show cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k)
      (φA.1 - φB.1) = 0
    rw [← cochainDiffLM_apply ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) k
        (φA.1 - φB.1), map_sub, cochainDiffLM_apply, cochainDiffLM_apply, hφAd, hφBd, sub_self]
  have hdAB : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).d k (k + 1) ⟨ψ, hψmem⟩ = 0 :=
    relComplex_d_eq_zero ⟨ψ, hψmem⟩ hψd
  let zx : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).cycles k :=
    cocycleOfK _ ⟨ψ, hψmem⟩ hdAB
  have hzx : (((relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k zx)).1 = φA.1 - φB.1 := by
    have h := iCycles_cocycleOfK (relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) ⟨ψ, hψmem⟩ hdAB
    exact (congrArg Subtype.val h).trans (show ψ = φA.1 - φB.1 from rfl)
  refine ⟨K₁, K₂, hK₁U, hK₂V, hK₀K₁, hK₀K₂, hK₁c, hK₂c, zx, zψ, φA.1, φB.1,
    hφAd, hφBd, hφAmem, hφBmem, hzx, ?_⟩
  have hlast : (HomologicalComplex.homologyMap (relComplexMap ℤ
      (pdRelSub (U ∩ V : Set M) K₀) (pdRelSub (U ∪ V : Set M) K₀)
      (pdIncl (U ∪ V : Set M) (U ∩ V) (Set.inter_subset_left.trans Set.subset_union_left))
      (fun x hx => hx)) (k + 1)).hom
      ((HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₀)) (k + 1)) zψ) = w := by
    rw [hzψ]
    exact hy
  exact hlast

/-! ## The crux square

Spliced from `Submission/Work/Cohomology/pd_crux_goodD_strong.lean` (proved by a colleague). -/

lemma pdCruxD_comp_f_apply {K L M : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L) (g : L ⟶ M) (n : ℕ)
    (x : K.X n) : (ModuleCat.Hom.hom (g.f n)) ((ModuleCat.Hom.hom (f.f n)) x)
      = (ModuleCat.Hom.hom ((f ≫ g).f n)) x := by
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp]; rfl

lemma pdCruxD_modCat_comp {A B C : ModuleCat ℤ} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    (ModuleCat.Hom.hom g) ((ModuleCat.Hom.hom f) x) = (ModuleCat.Hom.hom (f ≫ g)) x := by
  rw [ModuleCat.hom_comp]; rfl

lemma pdCruxD_biprod_ext {K L : ChainComplex (ModuleCat ℤ) ℕ} {n : ℕ} {x y : (K ⊞ L).X n}
    (h1 : (biprod.fst : K ⊞ L ⟶ K).f n x = (biprod.fst : K ⊞ L ⟶ K).f n y)
    (h2 : (biprod.snd : K ⊞ L ⟶ L).f n x = (biprod.snd : K ⊞ L ⟶ L).f n y) : x = y := by
  rw [← biprodX_total_apply (K := K) (L := L) (x := x), h1, h2]
  exact biprodX_total_apply (K := K) (L := L) (x := y)

lemma pdCruxD_biprod_fst_d {K L : ChainComplex (ModuleCat ℤ) ℕ} (n : ℕ) (x : (K ⊞ L).X (n+1)) :
    (biprod.fst : K ⊞ L ⟶ K).f n ((K ⊞ L).d (n+1) n x)
      = K.d (n+1) n ((biprod.fst : K ⊞ L ⟶ K).f (n+1) x) := by
  have h := congrArg (fun (g : (K ⊞ L).X (n+1) ⟶ K.X n) => (ModuleCat.Hom.hom g) x)
    ((biprod.fst : K ⊞ L ⟶ K).comm (n+1) n)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

lemma pdCruxD_biprod_snd_d {K L : ChainComplex (ModuleCat ℤ) ℕ} (n : ℕ) (x : (K ⊞ L).X (n+1)) :
    (biprod.snd : K ⊞ L ⟶ L).f n ((K ⊞ L).d (n+1) n x)
      = L.d (n+1) n ((biprod.snd : K ⊞ L ⟶ L).f (n+1) x) := by
  have h := congrArg (fun (g : (K ⊞ L).X (n+1) ⟶ L.X n) => (ModuleCat.Hom.hom g) x)
    ((biprod.snd : K ⊞ L ⟶ L).comm (n+1) n)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

lemma pdCruxD_fst_inl {K L : ChainComplex (ModuleCat ℤ) ℕ} {n : ℕ} (a : K.X n) :
    (biprod.fst : K ⊞ L ⟶ K).f n ((biprod.inl : K ⟶ K ⊞ L).f n a) = a := by
  have h : (biprod.inl : K ⟶ K ⊞ L) ≫ (biprod.fst : K ⊞ L ⟶ K) = 𝟙 K := biprod.inl_fst
  rw [pdCruxD_comp_f_apply (biprod.inl : K ⟶ K ⊞ L) (biprod.fst : K ⊞ L ⟶ K) n a, h]
  simp

lemma pdCruxD_fst_inr {K L : ChainComplex (ModuleCat ℤ) ℕ} {n : ℕ} (b : L.X n) :
    (biprod.fst : K ⊞ L ⟶ K).f n ((biprod.inr : L ⟶ K ⊞ L).f n b) = 0 := by
  have h : (biprod.inr : L ⟶ K ⊞ L) ≫ (biprod.fst : K ⊞ L ⟶ K) = 0 := biprod.inr_fst
  rw [pdCruxD_comp_f_apply (biprod.inr : L ⟶ K ⊞ L) (biprod.fst : K ⊞ L ⟶ K) n b, h]
  rfl

lemma pdCruxD_snd_inl {K L : ChainComplex (ModuleCat ℤ) ℕ} {n : ℕ} (a : K.X n) :
    (biprod.snd : K ⊞ L ⟶ L).f n ((biprod.inl : K ⟶ K ⊞ L).f n a) = 0 := by
  have h : (biprod.inl : K ⟶ K ⊞ L) ≫ (biprod.snd : K ⊞ L ⟶ L) = 0 := biprod.inl_snd
  rw [pdCruxD_comp_f_apply (biprod.inl : K ⟶ K ⊞ L) (biprod.snd : K ⊞ L ⟶ L) n a, h]
  rfl

lemma pdCruxD_snd_inr {K L : ChainComplex (ModuleCat ℤ) ℕ} {n : ℕ} (b : L.X n) :
    (biprod.snd : K ⊞ L ⟶ L).f n ((biprod.inr : L ⟶ K ⊞ L).f n b) = b := by
  have h : (biprod.inr : L ⟶ K ⊞ L) ≫ (biprod.snd : K ⊞ L ⟶ L) = 𝟙 L := biprod.inr_snd
  rw [pdCruxD_comp_f_apply (biprod.inr : L ⟶ K ⊞ L) (biprod.snd : K ⊞ L ⟶ L) n b, h]
  simp

lemma pdCruxD_fst_mvLeft {M : TopCat} {U V : Set M} {n : ℕ}
    (w : (singularChains ℤ (TopCat.of ↥(U ∩ V))).X n) :
    (biprod.fst : singularChains ℤ (TopCat.of ↥U) ⊞ singularChains ℤ (TopCat.of ↥V) ⟶
        singularChains ℤ (TopCat.of ↥U)).f n ((mvLeft U V).f n w)
      = (chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥U) (inclUVU U V)).f n w := by
  have h : (mvLeft U V) ≫ (biprod.fst : singularChains ℤ (TopCat.of ↥U) ⊞
      singularChains ℤ (TopCat.of ↥V) ⟶ singularChains ℤ (TopCat.of ↥U))
      = chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥U) (inclUVU U V) := by
    have h1 : mvLeft U V = biprod.lift
        (chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥U) (inclUVU U V))
        (chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥V) (inclUVV U V)) := rfl
    rw [h1, biprod.lift_fst]
  rw [pdCruxD_comp_f_apply (mvLeft U V) (biprod.fst : singularChains ℤ (TopCat.of ↥U) ⊞
    singularChains ℤ (TopCat.of ↥V) ⟶ singularChains ℤ (TopCat.of ↥U)) n w, h]

lemma pdCruxD_snd_mvLeft {M : TopCat} {U V : Set M} {n : ℕ}
    (w : (singularChains ℤ (TopCat.of ↥(U ∩ V))).X n) :
    (biprod.snd : singularChains ℤ (TopCat.of ↥U) ⊞ singularChains ℤ (TopCat.of ↥V) ⟶
        singularChains ℤ (TopCat.of ↥V)).f n ((mvLeft U V).f n w)
      = (chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥V) (inclUVV U V)).f n w := by
  have h : (mvLeft U V) ≫ (biprod.snd : singularChains ℤ (TopCat.of ↥U) ⊞
      singularChains ℤ (TopCat.of ↥V) ⟶ singularChains ℤ (TopCat.of ↥V))
      = chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥V) (inclUVV U V) := by
    have h1 : mvLeft U V = biprod.lift
        (chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥U) (inclUVU U V))
        (chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥V) (inclUVV U V)) := rfl
    rw [h1, biprod.lift_snd]
  rw [pdCruxD_comp_f_apply (mvLeft U V) (biprod.snd : singularChains ℤ (TopCat.of ↥U) ⊞
    singularChains ℤ (TopCat.of ↥V) ⟶ singularChains ℤ (TopCat.of ↥V)) n w, h]

lemma pdCruxD_inl_mvRight {M : TopCat} {U V : Set M} :
    (biprod.inl : singularChains ℤ (TopCat.of ↥U) ⟶
        singularChains ℤ (TopCat.of ↥U) ⊞ singularChains ℤ (TopCat.of ↥V)) ≫ mvRight U V
      = smallOfU U V := by
  rw [show mvRight U V = biprod.desc (smallOfU U V) (-(smallOfV U V)) from rfl, biprod.inl_desc]

lemma pdCruxD_inr_mvRight {M : TopCat} {U V : Set M} :
    (biprod.inr : singularChains ℤ (TopCat.of ↥V) ⟶
        singularChains ℤ (TopCat.of ↥U) ⊞ singularChains ℤ (TopCat.of ↥V)) ≫ mvRight U V
      = -(smallOfV U V) := by
  rw [show mvRight U V = biprod.desc (smallOfU U V) (-(smallOfV U V)) from rfl, biprod.inr_desc]

lemma pdCruxD_chainMap_inclUVU (M : TopCat) (U V : Set M) :
    chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥U) (inclUVU U V)
      = inclChainsSub M (U ∩ V) U (fun x hx => Set.mem_of_mem_inter_left hx) := by
  have h1 : inclUVU U V = pdIncl U (U ∩ V) (fun x hx => Set.mem_of_mem_inter_left hx) := by
    ext x; rfl
  have h2 := pdIncl_eq_inclChainsSub (M := M) (W := U) (S := U ∩ V)
    (fun x hx => Set.mem_of_mem_inter_left hx)
  rw [h1]
  exact h2

lemma pdCruxD_chainMap_inclUVV (M : TopCat) (U V : Set M) :
    chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥V) (inclUVV U V)
      = inclChainsSub M (U ∩ V) V (fun x hx => Set.mem_of_mem_inter_right hx) := by
  have h1 : inclUVV U V = pdIncl V (U ∩ V) (fun x hx => Set.mem_of_mem_inter_right hx) := by
    ext x; rfl
  have h2 := pdIncl_eq_inclChainsSub (M := M) (W := V) (S := U ∩ V)
    (fun x hx => Set.mem_of_mem_inter_right hx)
  rw [h1]
  exact h2

/-- If two cycles of a chain complex differ by a boundary, their homology classes agree. -/
lemma pdCruxD_homologyπ_eq_of_d_eq_sub {K : ChainComplex (ModuleCat ℤ) ℕ} {n : ℕ}
    (z₁ z₂ : K.cycles n) (y : K.X (n+1))
    (h : (ModuleCat.Hom.hom (K.d (n+1) n)) y
        = (ModuleCat.Hom.hom (HomologicalComplex.iCycles K n)) z₁
          - (ModuleCat.Hom.hom (HomologicalComplex.iCycles K n)) z₂) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K n)) z₁
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K n)) z₂ := by
  have hsub : z₁ - z₂ = (HomologicalComplex.toCycles K (n+1) n) y := by
    apply (Preadditive.mono_iff_injective (HomologicalComplex.iCycles K n)).1 inferInstance
    change (ModuleCat.Hom.hom (HomologicalComplex.iCycles K n)) (z₁ - z₂)
      = (ModuleCat.Hom.hom (HomologicalComplex.iCycles K n))
          ((ModuleCat.Hom.hom (HomologicalComplex.toCycles K (n+1) n)) y)
    rw [map_sub, ← h, pdCruxD_modCat_comp (HomologicalComplex.toCycles K (n+1) n)
      (HomologicalComplex.iCycles K n) y, HomologicalComplex.toCycles_i]
  have h2 : (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K n)) (z₁ - z₂) = 0 := by
    rw [hsub]
    change (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K n))
      ((ModuleCat.Hom.hom (HomologicalComplex.toCycles K (n+1) n)) y) = 0
    rw [pdCruxD_modCat_comp (HomologicalComplex.toCycles K (n+1) n)
      (HomologicalComplex.homologyπ K n) y, HomologicalComplex.toCycles_comp_homologyπ]
    simp
  have h3 : (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K n)) z₁
      - (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K n)) z₂ = 0 := by
    rw [← map_sub]; exact h2
  exact sub_eq_zero.mp h3

/-- Naturality of `homologyπ` for cochain complexes. -/
lemma pdCruxD_homologyMap_homologyπ_cyclesMap {C D : CochainComplex (ModuleCat ℤ) ℕ}
    (φ : C ⟶ D) (n : ℕ) (z : C.cycles n) :
    (HomologicalComplex.homologyMap φ n).hom ((C.homologyπ n).hom z)
      = (D.homologyπ n).hom ((HomologicalComplex.cyclesMap φ n).hom z) := by
  have h2 := congrArg (fun (g : C.cycles n ⟶ D.homology n) => g.hom z)
    (HomologicalComplex.homologyπ_naturality φ n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- The underlying cochain of the image cycle is the image of the underlying cochain. -/
lemma pdCruxD_iCycles_cyclesMap_apply {C D : CochainComplex (ModuleCat ℤ) ℕ}
    (φ : C ⟶ D) (n : ℕ) (z : C.cycles n) :
    (D.iCycles n).hom ((HomologicalComplex.cyclesMap φ n).hom z)
      = (φ.f n).hom ((C.iCycles n).hom z) := by
  have h2 := congrArg (fun (g : C.cycles n ⟶ D.X n) => g.hom z)
    (HomologicalComplex.cyclesMap_i φ n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-! ## Functoriality of `relComplexMap` (local copies) -/

lemma pdCruxD_relComplexMap_f_coe {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ) (x : relKern ℤ X₂ A₂ n) :
    ((relComplexMap ℤ A₁ A₂ f h).f n x).1 = ((dualChainMap ℤ X₁ X₂ f).f n).hom x.1 := by
  rw [relComplexMap_f ℤ A₁ A₂ f h n]
  rfl

lemma pdCruxD_relComplexMap_id {X : TopCat} (A : Set X) (h : ∀ x ∈ A, (𝟙 X : X ⟶ X) x ∈ A) :
    relComplexMap ℤ A A (𝟙 X) h = 𝟙 (relComplex ℤ X A) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [relComplexMap_f ℤ A A (𝟙 X) h n]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, relMapLM_coe, dualChainMap_id,
    HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
  rfl

lemma pdCruxD_relComplexMap_comp {X₀ X₁ X₂ : TopCat} (A₀ : Set X₀) (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (hf : ∀ x ∈ A₀, f x ∈ A₁) (hg : ∀ y ∈ A₁, g y ∈ A₂) :
    relComplexMap ℤ A₀ A₂ (f ≫ g) (fun x hx => hg (f x) (hf x hx))
      = relComplexMap ℤ A₁ A₂ g hg ≫ relComplexMap ℤ A₀ A₁ f hf := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, relComplexMap_f ℤ A₀ A₂ (f ≫ g) _ n,
    relComplexMap_f ℤ A₁ A₂ g hg n, relComplexMap_f ℤ A₀ A₁ f hf n]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.comp_apply, relMapLM_coe,
    dualChainMap_comp, HomologicalComplex.comp_f]
  rfl

lemma pdCruxD_relComplexMap_congr {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    {f f' : X₁ ⟶ X₂} (hf : f = f') (h : ∀ x ∈ A₁, f x ∈ A₂) (h' : ∀ x ∈ A₁, f' x ∈ A₂) :
    relComplexMap ℤ A₁ A₂ f h = relComplexMap ℤ A₁ A₂ f' h' := by
  subst hf
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- **The square of the enlargement and the restriction.** -/
lemma pdCruxD_enlarge_restrict {M : TopCat} {W U : Set M} (hUW : U ⊆ W) {K K' : Set M}
    (hKU : K ⊆ U) (hK'U : K' ⊆ U) (h : K ⊆ K') :
    pdRelComplexEnlarge W h
      ≫ relComplexMap ℤ (X₁ := TopCat.of U) (X₂ := TopCat.of W)
          (pdRelSub U K') (pdRelSub W K') (pdIncl W U hUW) (fun x hx => hx)
      = relComplexMap ℤ (X₁ := TopCat.of U) (X₂ := TopCat.of W)
          (pdRelSub U K) (pdRelSub W K) (pdIncl W U hUW) (fun x hx => hx)
        ≫ pdRelComplexEnlarge U h := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [show (pdRelComplexEnlarge W h)
        = relComplexMap ℤ (pdRelSub W K') (pdRelSub W K) (𝟙 (TopCat.of W)) (pdRelSub_mono_id h)
      from rfl,
      show (pdRelComplexEnlarge U h)
        = relComplexMap ℤ (pdRelSub U K') (pdRelSub U K) (𝟙 (TopCat.of U)) (pdRelSub_mono_id h)
      from rfl]
  rw [pdCruxD_relComplexMap_f_coe, pdCruxD_relComplexMap_f_coe,
      pdCruxD_relComplexMap_f_coe, pdCruxD_relComplexMap_f_coe]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, dualChainMap_id, HomologicalComplex.id_f,
    ModuleCat.hom_id, LinearMap.id_apply]

theorem pd_crux_goodD_strong {M : TopCat} [T2Space M] {N : ℕ}
    {c : (singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    {K₁ K₂ K₀ : Set M} (hK₁U : K₁ ⊆ U) (hK₂V : K₂ ⊆ V)
    (hK₁c : IsCompact K₁) (hK₂c : IsCompact K₂)
    (hK₀I : K₀ ⊆ U ∩ V) (hK₀c : IsCompact K₀) (hK₀K₁ : K₀ ⊆ K₁) (hK₀K₂ : K₀ ⊆ K₂)
    (k m' : ℕ) (hN : k + (m' + 1) = N) (hN' : k + 1 + m' = N)
    (zx : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).cycles k)
    (zψ : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) K₀)).cycles (k + 1))
    (φA φB : ↑((singularCochainComplex ℤ (TopCat.of (U ∪ V : Set M))).X k))
    (hφA : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M)))
      (n := k) φA
      = (((relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₀)).iCycles (k + 1) zψ).1))
    (hφB : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M)))
      (n := k) φB
      = (((relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₀)).iCycles (k + 1) zψ).1))
    (hφAk : φA ∈ relKern ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) K₁) k)
    (hφBk : φB ∈ relKern ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) K₂) k)
    (hzx : (((relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k zx).1
      = φA - φB))
    (wres : (relComplex ℤ (TopCat.of (U ∩ V : Set M))
      (pdRelSub (U ∩ V : Set M) K₀)).homology (k + 1))
    (hwres : wres = (HomologicalComplex.homologyMap (relComplexMap ℤ
      (pdRelSub (U ∩ V : Set M) K₀)
      (pdRelSub (U ∪ V : Set M) K₀)
      (pdIncl (U ∪ V : Set M) (U ∩ V)
        (Set.inter_subset_left.trans Set.subset_union_left)) (fun x hx => hx)) (k + 1)).hom
      ((HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₀)) (k + 1)) zψ))
    (D : (singularChains ℤ (TopCat.of (U ∩ V : Set M))).homology m')
    (hD : D = goodD N c (U ∩ V : Set M) (hU.inter hV) K₀ hK₀I hK₀c
      (k + 1) m' hN' wres)
    (Φ : smallChains U V ⟶
      singularChains ℤ (TopCat.of (U ∪ V : Set M)))
    (hΦiso : ∀ n, CategoryTheory.IsIso (HomologicalComplex.homologyMap Φ n))
    (hΦU : CategoryTheory.CategoryStruct.comp (smallOfU U V) Φ
      = chainMap ℤ (TopCat.of U) (TopCat.of (U ∪ V : Set M))
          (pdIncl (U ∪ V : Set M) U Set.subset_union_left))
    (hΦV : CategoryTheory.CategoryStruct.comp (smallOfV U V) Φ
      = chainMap ℤ (TopCat.of V) (TopCat.of (U ∪ V : Set M))
          (pdIncl (U ∪ V : Set M) V Set.subset_union_right)) :
    (mvδ U V m').hom
        ((CategoryTheory.inv (HomologicalComplex.homologyMap Φ (m' + 1))).hom
          (goodD N c (U ∪ V : Set M) (hU.union hV) (K₁ ∪ K₂)
            (Set.union_subset (hK₁U.trans Set.subset_union_left)
              (hK₂V.trans Set.subset_union_right)) (hK₁c.union hK₂c) k (m' + 1) hN
            ((HomologicalComplex.homologyπ (relComplex ℤ
              (TopCat.of (U ∪ V : Set M))
              (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k) zx)))
      = D
      ∨ (mvδ U V m').hom
        ((CategoryTheory.inv (HomologicalComplex.homologyMap Φ (m' + 1))).hom
          (goodD N c (U ∪ V : Set M) (hU.union hV) (K₁ ∪ K₂)
            (Set.union_subset (hK₁U.trans Set.subset_union_left)
              (hK₂V.trans Set.subset_union_right)) (hK₁c.union hK₂c) k (m' + 1) hN
            ((HomologicalComplex.homologyπ (relComplex ℤ
              (TopCat.of (U ∪ V : Set M))
              (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k) zx)))
      = -D := by
  classical
  subst N
  -- ## preliminary set-theoretic facts
  have hKW : K₁ ∪ K₂ ⊆ (U ∪ V : Set M) :=
    Set.union_subset (hK₁U.trans Set.subset_union_left) (hK₂V.trans Set.subset_union_right)
  have hKc : IsCompact (K₁ ∪ K₂) := hK₁c.union hK₂c
  have hW : IsOpen (U ∪ V : Set M) := hU.union hV
  have hIW : (U ∩ V : Set M) ⊆ (U ∪ V : Set M) :=
    Set.inter_subset_left.trans Set.subset_union_left
  have hKstI : K₁ ∩ K₂ ⊆ U ∩ V := Set.inter_subset_inter hK₁U hK₂V
  have hKstc : IsCompact (K₁ ∩ K₂) := hK₁c.inter hK₂c
  have hK0st : K₀ ⊆ K₁ ∩ K₂ := fun x hx => ⟨hK₀K₁ hx, hK₀K₂ hx⟩
  -- ## Step 1: the cocycle `φ` of the relative class `zx`
  set φ : Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) k :=
    ((relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k zx).1 with hφdef
  have hφzmem : φ ∈ relKern ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)) k := by
    rw [hφdef]
    exact ((relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k zx).2
  have hlift : φ = φA - φB := by
    rw [hφdef]
    exact hzx
  have hφd : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) φ = 0 := by
    have hφ_eq : (SSetCochainComplex ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M)))).iCycles k
        (HomologicalComplex.cyclesMap (relIncl ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k zx) = φ := by
      change (ModuleCat.Hom.hom (HomologicalComplex.iCycles
          (singularCochainComplex ℤ (TopCat.of (U ∪ V : Set M))) k))
        ((ModuleCat.Hom.hom (HomologicalComplex.cyclesMap (relIncl ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k)) zx) = φ
      rw [pdCruxD_iCycles_cyclesMap_apply (relIncl ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k zx]
      rw [relIncl_f, ModuleCat.hom_ofHom]
      rw [hφdef]
      rfl
    rw [← hφ_eq]
    exact cochainDiff_iCycles ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) k _
  -- ## Step 2: the Hatcher decomposition
  obtain ⟨α₁, α₂, α₃, γ, ξ, hγc, hγi, hξ, hα₁mem, hα₂mem, hα₃mem, hdα₁, hdα₃⟩ :=
    pd_hatcher_W (c := c) (U := U) (V := V) (K := K₁) (L := K₂)
      hU hV hK₁c hK₂c hK₁U hK₂V
  -- ## Step 3: the boundary of `ξ`
  have hdξ : ∃ g', (inclChains (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).f (k + m') g'
      = (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k + (m' + 1)) (k + m') ξ := by
    have hcyc : (cokernel.π (inclChains (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)))).f (k + m')
        ((singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k + (m' + 1)) (k + m') ξ) = 0 := by
      change (ModuleCat.Hom.hom ((cokernel.π (inclChains (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)))).f (k + m')))
        ((ModuleCat.Hom.hom ((singularChains ℤ (TopCat.of (U ∪ V : Set M))).d
          (k + (m' + 1)) (k + m'))) ξ) = 0
      have hcomm := congrArg (fun (g : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X (k+(m'+1)) ⟶
          (relChains (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).X (k+m')) =>
          (ModuleCat.Hom.hom g) ξ)
        ((cokernel.π (inclChains (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)))).comm (k+(m'+1)) (k+m'))
      simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
      erw [← hcomm, ← hγi]
      have h2 : (ModuleCat.Hom.hom ((relChains (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).d (k+(m'+1)) (k+m')))
          ((ModuleCat.Hom.hom ((relChains (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles (k+(m'+1)))) γ) = 0 := by
        rw [pdCruxD_modCat_comp ((relChains (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles (k+(m'+1)))
          ((relChains (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).d (k+(m'+1)) (k+m')) γ]
        rw [show ((relChains (TopCat.of (U ∪ V : Set M))
              (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles (k+(m'+1))
              ≫ (relChains (TopCat.of (U ∪ V : Set M))
                (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).d (k+(m'+1)) (k+m')) = 0
          from HomologicalComplex.iCycles_d (K := relChains (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) (i := k+(m'+1)) (j := k+m')]
        rfl
      change (ModuleCat.Hom.hom ((relChains (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).d (k+(m'+1)) (k+m')))
          ((ModuleCat.Hom.hom ((relChains (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles (k+(m'+1)))) γ) = 0
      exact h2
    have h3 := (cokernel_pi_f_eq_zero_iff (inclChains (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) (k + m')
      ((singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k + (m' + 1)) (k + m') ξ)).mp hcyc
    obtain ⟨g, hg⟩ := h3
    exact ⟨g, hg⟩
  have hdsum : ∃ g, (inclChains (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).f (k + m') g
      = (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k + (m' + 1)) (k + m') (α₁ + α₂ + α₃) := by
    obtain ⟨g, hg⟩ := hdξ
    exact ⟨g, by rw [← hξ]; exact hg⟩
  have hdα₁' : ∃ e, (inclChains (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₂)).f (k + m') e
      = (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k + (m' + 1)) (k + m') α₁ := by
    simpa using hdα₁
  have hdα₃' : ∃ f, (inclChains (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₁)).f (k + m') f
      = (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k + (m' + 1)) (k + m') α₃ := by
    simpa using hdα₃
  -- ## Step 4: the chain-level crux data
  obtain ⟨a, b, wc, h_a, h_b, hwa, hwb, s'', hs''⟩ :=
    pd_crux_chain (M := M) (U := U) (V := V) (K := K₁) (L := K₂) (k := k) (mj := m')
      φ φA φB hφAk hφBk hlift hφd α₁ α₂ α₃ hα₁mem hα₂mem hα₃mem hdα₁' hdα₃' hdsum
  -- ## Step 5: the small chain realising the duality class
  let z₂ : (singularChains ℤ (TopCat.of ↥U) ⊞ singularChains ℤ (TopCat.of ↥V)).X (m'+1) :=
    (biprod.inl : singularChains ℤ (TopCat.of ↥U) ⟶
        singularChains ℤ (TopCat.of ↥U) ⊞ singularChains ℤ (TopCat.of ↥V)).f (m'+1) a
      + (biprod.inr : singularChains ℤ (TopCat.of ↥V) ⟶
        singularChains ℤ (TopCat.of ↥U) ⊞ singularChains ℤ (TopCat.of ↥V)).f (m'+1) b
  have hz₂def : z₂ = (biprod.inl : singularChains ℤ (TopCat.of ↥U) ⟶
        singularChains ℤ (TopCat.of ↥U) ⊞ singularChains ℤ (TopCat.of ↥V)).f (m'+1) a
      + (biprod.inr : singularChains ℤ (TopCat.of ↥V) ⟶
        singularChains ℤ (TopCat.of ↥U) ⊞ singularChains ℤ (TopCat.of ↥V)).f (m'+1) b := rfl
  have hfst_z₂ : (biprod.fst : singularChains ℤ (TopCat.of ↥U) ⊞
      singularChains ℤ (TopCat.of ↥V) ⟶ singularChains ℤ (TopCat.of ↥U)).f (m'+1) z₂ = a := by
    rw [hz₂def, map_add, pdCruxD_fst_inl, pdCruxD_fst_inr, add_zero]
  have hsnd_z₂ : (biprod.snd : singularChains ℤ (TopCat.of ↥U) ⊞
      singularChains ℤ (TopCat.of ↥V) ⟶ singularChains ℤ (TopCat.of ↥V)).f (m'+1) z₂ = b := by
    rw [hz₂def, map_add, pdCruxD_snd_inl, pdCruxD_snd_inr, zero_add]
  have hdz₂ : (singularChains ℤ (TopCat.of ↥U) ⊞ singularChains ℤ (TopCat.of ↥V)).d (m'+1) m' z₂
      = (mvLeft U V).f m'
          ((singularChains ℤ (TopCat.of ↥(U ∩ V))).iCycles m' wc) := by
    refine pdCruxD_biprod_ext ?_ ?_
    · rw [pdCruxD_biprod_fst_d m', hfst_z₂, pdCruxD_fst_mvLeft]
      exact hwa.symm
    · rw [pdCruxD_biprod_snd_d m', hsnd_z₂, pdCruxD_snd_mvLeft]
      exact hwb.symm
  have hz₂cyc : (smallChains U V).d (m'+1) m' ((mvRight U V).f (m'+1) z₂) = 0 := by
    have hnat := congrArg (fun (g : (singularChains ℤ (TopCat.of ↥U) ⊞
          singularChains ℤ (TopCat.of ↥V)).X (m'+1) ⟶ (smallChains U V).X m') =>
          (ModuleCat.Hom.hom g) z₂) ((mvRight U V).comm (m'+1) m')
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
    rw [hnat, hdz₂]
    rw [pdCruxD_comp_f_apply (mvLeft U V) (mvRight U V) m'
      ((singularChains ℤ (TopCat.of ↥(U ∩ V))).iCycles m' wc), mvComp]
    rfl
  let z : (smallChains U V).cycles (m'+1) := cycleOf (m'+1) ((mvRight U V).f (m'+1) z₂) hz₂cyc
  have hz_ic : (mvRight U V).f (m'+1) z₂ = (smallChains U V).iCycles (m'+1) z :=
    (iCycles_cycleOf (m'+1) ((mvRight U V).f (m'+1) z₂) hz₂cyc).symm
  -- ## Step 6: `mvδ` of the duality class
  have hmvδ := pd_mvdelta_apply (X := M) (U := U) (V := V) (n := m') z z₂ hz_ic wc hdz₂.symm
  -- ## Step 7: the value of `Φ` on the small chain
  have hmvform : (mvRight U V).f (m'+1) z₂
      = (smallOfU U V).f (m'+1) a - (smallOfV U V).f (m'+1) b := by
    rw [hz₂def, map_add,
      pdCruxD_comp_f_apply (biprod.inl : singularChains ℤ (TopCat.of ↥U) ⟶
        singularChains ℤ (TopCat.of ↥U) ⊞ singularChains ℤ (TopCat.of ↥V)) (mvRight U V) (m'+1) a,
      pdCruxD_comp_f_apply (biprod.inr : singularChains ℤ (TopCat.of ↥V) ⟶
        singularChains ℤ (TopCat.of ↥U) ⊞ singularChains ℤ (TopCat.of ↥V)) (mvRight U V) (m'+1) b,
      pdCruxD_inl_mvRight, pdCruxD_inr_mvRight,
      HomologicalComplex.neg_f_apply, ModuleCat.hom_neg, LinearMap.neg_apply]
    rw [sub_eq_add_neg]
  have hΦchain : (ModuleCat.Hom.hom (Φ.f (m'+1))) ((mvRight U V).f (m'+1) z₂)
      = cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) φ (m'+1) ξ := by
    rw [hmvform, map_sub]
    have e3 : (ModuleCat.Hom.hom (Φ.f (m'+1))) ((smallOfU U V).f (m'+1) a)
        = cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) φ (m'+1) α₁ := by
      rw [pdCruxD_comp_f_apply (smallOfU U V) Φ (m'+1) a, hΦU, pdIncl_eq_inclChainsSub]
      exact h_a
    have e4 : (ModuleCat.Hom.hom (Φ.f (m'+1))) ((smallOfV U V).f (m'+1) b)
        = -(cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) φ (m'+1) α₂
            + cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) φ (m'+1) α₃) := by
      rw [pdCruxD_comp_f_apply (smallOfV U V) Φ (m'+1) b, hΦV, pdIncl_eq_inclChainsSub]
      exact h_b
    rw [e3, e4, hξ, map_add, map_add]
    abel
  have hcapξcyc : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (m'+1) m'
      (cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) φ (m'+1) ξ) = 0 := by
    have hcd := cap_d ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) (m := m') φ ξ
    have hzero : cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M)))
        (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) φ) m'
        ((capIdx k m') ▸ ξ) = 0 := by
      rw [hφd, cap_zero]
      rfl
    rw [hzero] at hcd
    have hzeroξ : cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) φ m'
        ((ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M)))).d
          (k+(m'+1)) (k+m'))) ξ) = 0 := by
      change cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) φ m'
        ((singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k+(m'+1)) (k+m') ξ) = 0
      obtain ⟨g, hg⟩ := hdξ
      erw [← hg]
      exact cap_inclChains_eq_zero (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)) φ hφzmem m' g
    rw [hzeroξ] at hcd
    rw [sub_zero, smul_zero] at hcd
    exact hcd
  have hzW : goodD (k + (m'+1)) c (U ∪ V : Set M) hW (K₁ ∪ K₂) hKW hKc
        k (m'+1) rfl
        (((relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homologyπ k) zx)
      = (singularChains ℤ (TopCat.of (U ∪ V : Set M))).homologyπ (m'+1)
          (cycleOf (m'+1) (cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M)))
            φ (m'+1) ξ) hcapξcyc) := by
    have h1 := goodD_homologyπ (N := k + (m'+1)) c (U ∪ V : Set M) hW (K₁ ∪ K₂)
      hKW hKc k (m'+1) rfl zx γ hγc ξ hγi
    rw [h1]
    have hrc : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).iCycles (m'+1)
        (relCapPairZ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)) k (m'+1) zx γ)
        = cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) φ (m'+1) ξ := by
      rw [relCapPairZ_iCycles_apply (X := TopCat.of (U ∪ V : Set M))
        (A := pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)) (n := k) (m := m'+1) (ξ := ξ) zx γ hγi]
    have hcyc_eq : relCapPairZ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂)) k (m'+1) zx γ
        = cycleOf (m'+1) (cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M)))
            φ (m'+1) ξ) hcapξcyc := by
      apply (Preadditive.mono_iff_injective (HomologicalComplex.iCycles
        (singularChains ℤ (TopCat.of (U ∪ V : Set M))) (m'+1))).1 inferInstance
      erw [hrc, iCycles_cycleOf]
    erw [hcyc_eq]
  have hΦz : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap Φ (m'+1)))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (smallChains U V) (m'+1))) z)
      = goodD (k + (m'+1)) c (U ∪ V : Set M) hW (K₁ ∪ K₂) hKW hKc k (m'+1) rfl
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (relComplex ℤ
            (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k)) zx) := by
    rw [homologyMap_homologyπ_cyclesMap Φ (m'+1) z]
    rw [hzW]
    apply congrArg (fun z : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).cycles (m'+1) =>
      (ModuleCat.Hom.hom (HomologicalComplex.homologyπ
        (singularChains ℤ (TopCat.of (U ∪ V : Set M))) (m'+1))) z)
    apply (Preadditive.mono_iff_injective (HomologicalComplex.iCycles
      (singularChains ℤ (TopCat.of (U ∪ V : Set M))) (m'+1))).1 inferInstance
    erw [iCycles_cyclesMap_apply, ← hz_ic, hΦchain]
    exact (iCycles_cycleOf (m'+1) (cap ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M)))
      φ (m'+1) ξ) hcapξcyc).symm
  have hΦinv : (ModuleCat.Hom.hom (HomologicalComplex.homologyπ (smallChains U V) (m'+1))) z
      = (ModuleCat.Hom.hom (CategoryTheory.inv (HomologicalComplex.homologyMap Φ (m'+1))))
          (goodD (k + (m'+1)) c (U ∪ V : Set M) hW (K₁ ∪ K₂) hKW hKc k (m'+1) rfl
            ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (relComplex ℤ
              (TopCat.of (U ∪ V : Set M))
              (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k)) zx)) := by
    have h := IsIso.hom_inv_id_apply (HomologicalComplex.homologyMap Φ (m'+1))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (smallChains U V) (m'+1))) z)
    rw [hΦz] at h
    exact h.symm
  have hLHS : (mvδ U V m').hom
        ((ModuleCat.Hom.hom (CategoryTheory.inv (HomologicalComplex.homologyMap Φ (m'+1))))
          (goodD (k + (m'+1)) c (U ∪ V : Set M) hW (K₁ ∪ K₂) hKW hKc k (m'+1) rfl
            ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (relComplex ℤ
              (TopCat.of (U ∪ V : Set M))
              (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k)) zx)))
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyπ
          (singularChains ℤ (TopCat.of ↥(U ∩ V))) m')) wc := by
    rw [← hΦinv]
    exact hmvδ
  -- ## Step 8: the `K⋆`-cycle of `zψ`
  let zψst : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂))).cycles (k+1) :=
    HomologicalComplex.cyclesMap (pdRelComplexEnlarge (U ∪ V : Set M) hK0st) (k+1) zψ
  have hzψst : zψst = HomologicalComplex.cyclesMap
      (pdRelComplexEnlarge (U ∪ V : Set M) hK0st) (k+1) zψ := rfl
  have hψst : ((relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂))).iCycles (k+1) zψst).1
      = cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) φA := by
    rw [hzψst]
    rw [pdCruxD_iCycles_cyclesMap_apply (pdRelComplexEnlarge (U ∪ V : Set M) hK0st) (k+1) zψ]
    rw [show (pdRelComplexEnlarge (U ∪ V : Set M) hK0st)
        = relComplexMap ℤ (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂))
            (pdRelSub (U ∪ V : Set M) K₀) (𝟙 (TopCat.of (U ∪ V : Set M)))
            (pdRelSub_mono_id hK0st) from rfl]
    rw [pdCruxD_relComplexMap_f_coe]
    rw [dualChainMap_id, HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
    exact hφA.symm
  have hχd : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k)
      (0 : Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) k)
      = cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) φA
        - pdCohUnderCycle (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂)) (k+1) zψst := by
    rw [show pdCohUnderCycle (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂)) (k+1) zψst
        = cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) φA
        from hψst]
    rw [sub_self]
    simp [cochainDiff]
  -- ## Step 9: the intersection-side computation
  obtain ⟨β, hβ⟩ := hα₂mem
  have hrel : ∃ g, (inclChains (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂))).f (k + m') g
      = (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k + (m'+1)) (k + m') α₂ := by
    obtain ⟨g₀, hg₀⟩ := hdα₁'
    obtain ⟨f₀, hf₀⟩ := hdα₃'
    have hsubA : pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂) ⊆
        pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂) := by
      intro y hy h
      exact hy (Or.inl h.1)
    have hsubB : pdRelSub (U ∪ V : Set M) K₁ ⊆
        pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂) := by
      intro y hy h
      exact hy h.1
    have hsubC : pdRelSub (U ∪ V : Set M) K₂ ⊆
        pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂) := by
      intro y hy h
      exact hy h.2
    have hmemg : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k+(m'+1)) (k+m') ξ ∈
        LinearMap.range ((inclChains (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂))).f (k+m')).hom :=
      mem_range_inclChains_of_subset hsubA hdξ
    have hmemf : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k+(m'+1)) (k+m') α₃ ∈
        LinearMap.range ((inclChains (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂))).f (k+m')).hom :=
      mem_range_inclChains_of_subset hsubB ⟨f₀, hf₀⟩
    have hmeme : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k+(m'+1)) (k+m') α₁ ∈
        LinearMap.range ((inclChains (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂))).f (k+m')).hom :=
      mem_range_inclChains_of_subset hsubC ⟨g₀, hg₀⟩
    obtain ⟨G, hG⟩ := hmemg
    obtain ⟨E, hE⟩ := hmeme
    obtain ⟨F, hF⟩ := hmemf
    refine ⟨G - E - F, ?_⟩
    rw [map_sub, map_sub, hG, hE, hF]
    rw [show (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k+(m'+1)) (k+m') ξ
        = (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k+(m'+1)) (k+m') (α₁ + α₂ + α₃)
        from by rw [hξ], map_add, map_add]
    abel
  obtain ⟨ζ, hζi, hζc⟩ := pd_alpha2_zeta (N := k+(m'+1)) (c := c) (U := U) (V := V)
    (K := K₁) (L := K₂) hU hV hK₁c hK₂c hK₁U hK₂V ξ γ hγi hγc α₁ α₂ α₃ hξ hα₁mem hα₃mem
  obtain ⟨γ₂, hγ₂i, hγ₂c⟩ := pd_alpha2_localFundClass (N := k+(m'+1)) (c := c) (U := U)
    (V := V) (K := K₁) (L := K₂) hU hV (hU.inter hV) hK₁c hK₂c hK₁U hK₂V α₂ β hβ hrel ζ hζi hζc
  have hdα₂ : ∃ (g e f : (singularChains ℤ (TopCat.of (U ∪ V : Set M))).X (k+m')),
      (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k+(m'+1)) (k+m') α₂ = g - e - f ∧
      g ∈ LinearMap.range ((inclChains (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).f (k+m')).hom ∧
      e ∈ LinearMap.range ((inclChains (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₂)).f (k+m')).hom ∧
      f ∈ LinearMap.range ((inclChains (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) K₁)).f (k+m')).hom := by
    obtain ⟨g₀, hg₀⟩ := hdα₁'
    obtain ⟨f₀, hf₀⟩ := hdα₃'
    obtain ⟨e₀, he₀⟩ := hdξ
    exact ⟨(singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k+(m'+1)) (k+m') ξ,
      (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k+(m'+1)) (k+m') α₁,
      (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k+(m'+1)) (k+m') α₃,
      by rw [show (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k+(m'+1)) (k+m') ξ
            = (singularChains ℤ (TopCat.of (U ∪ V : Set M))).d (k+(m'+1)) (k+m') (α₁ + α₂ + α₃)
            from by rw [hξ], map_add, map_add]
         abel,
      ⟨e₀, he₀⟩, ⟨g₀, hg₀⟩, ⟨f₀, hf₀⟩⟩
  obtain ⟨s, hs1, hs2⟩ := pd_inter_rep (c := c) (k := k) (mj := m') (U := U) (V := V)
    (K := K₁) (L := K₂) hU hV (hU.inter hV) hK₁c hK₂c hK₁U hK₂V
    φA α₂ β hβ zψst (0 : Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) k)
    (Submodule.zero_mem _) (Submodule.zero_mem _) hχd hdα₂ γ₂ hγ₂i hγ₂c
  -- ## Step 10: the two values of `D`
  have hwres_star : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relComplexMap ℤ
        (pdRelSub (U ∩ V : Set M) (K₁ ∩ K₂))
        (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂))
        (pdIncl (U ∪ V : Set M) (U ∩ V) hIW) (fun x hx => hx)) (k + 1)))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (relComplex ℤ
          (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂))) (k + 1))) zψst)
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (pdRelComplexEnlarge (U ∩ V : Set M) hK0st) (k + 1))) wres := by
    rw [hzψst]
    rw [← pdCruxD_homologyMap_homologyπ_cyclesMap
      (pdRelComplexEnlarge (U ∪ V : Set M) hK0st) (k+1) zψ]
    erw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp]
    erw [pdCruxD_enlarge_restrict (W := (U ∪ V : Set M)) (U := (U ∩ V : Set M)) hIW
      hK₀I hKstI hK0st]
    rw [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    erw [← hwres]
  have hDst : goodD (k + (m'+1)) c (U ∩ V : Set M) (hU.inter hV) (K₁ ∩ K₂)
        hKstI hKstc (k + 1) m' hN'
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relComplexMap ℤ
          (pdRelSub (U ∩ V : Set M) (K₁ ∩ K₂))
          (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂))
          (pdIncl (U ∪ V : Set M) (U ∩ V) hIW) (fun x hx => hx)) (k + 1)))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (relComplex ℤ
            (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∩ K₂))) (k + 1))) zψst))
      = D := by
    rw [hwres_star]
    rw [pd_goodD_natural (N := k + (m'+1)) c (U ∩ V : Set M) (hU.inter hV)
      (K := K₀) (K' := K₁ ∩ K₂) hK0st hK₀I hKstI hK₀c hKstc (k+1) m' hN' wres]
    exact hD.symm
  have hs_eq_D : (ModuleCat.Hom.hom (HomologicalComplex.homologyπ
      (singularChains ℤ (TopCat.of ↥(U ∩ V))) m')) s = D := by
    rw [← hs2]
    exact hDst
  -- ## Step 11: the relation between the two cycles of `U ∩ V`
  have hchain : (ModuleCat.Hom.hom (HomologicalComplex.iCycles
        (singularChains ℤ (TopCat.of ↥(U ∩ V))) m')) wc
      = (ModuleCat.Hom.hom ((singularChains ℤ (TopCat.of ↥(U ∩ V))).d (m'+1) m')) s''
        + ((-1 : ℤ) ^ (k+1)) •
          (ModuleCat.Hom.hom (HomologicalComplex.iCycles
            (singularChains ℤ (TopCat.of ↥(U ∩ V))) m')) s := by
    have hlin : (ModuleCat.Hom.hom ((inclChains M (U ∩ V)).f m'))
        (((-1 : ℤ) ^ (k+1)) • (ModuleCat.Hom.hom (HomologicalComplex.iCycles
          (singularChains ℤ (TopCat.of ↥(U ∩ V))) m')) s)
        = ((-1 : ℤ) ^ (k+1)) • (ModuleCat.Hom.hom ((inclChains M (U ∩ V)).f m'))
            ((ModuleCat.Hom.hom (HomologicalComplex.iCycles
              (singularChains ℤ (TopCat.of ↥(U ∩ V))) m')) s) :=
      map_zsmul _ _ _
    apply inclChains_f_injective M (U ∩ V) m'
    rw [map_add, hlin, hs'', ← hs1]
  have hhom : (ModuleCat.Hom.hom (HomologicalComplex.homologyπ
      (singularChains ℤ (TopCat.of ↥(U ∩ V))) m')) wc
      = ((-1 : ℤ) ^ (k+1)) • D := by
    have hsub : (ModuleCat.Hom.hom ((singularChains ℤ (TopCat.of ↥(U ∩ V))).d (m'+1) m')) s''
        = (ModuleCat.Hom.hom (HomologicalComplex.iCycles
              (singularChains ℤ (TopCat.of ↥(U ∩ V))) m')) wc
          - (ModuleCat.Hom.hom (HomologicalComplex.iCycles
              (singularChains ℤ (TopCat.of ↥(U ∩ V))) m')) (((-1 : ℤ) ^ (k+1)) • s) := by
      have hlin2 : (ModuleCat.Hom.hom (HomologicalComplex.iCycles
            (singularChains ℤ (TopCat.of ↥(U ∩ V))) m')) (((-1 : ℤ) ^ (k+1)) • s)
          = ((-1 : ℤ) ^ (k+1)) • (ModuleCat.Hom.hom (HomologicalComplex.iCycles
              (singularChains ℤ (TopCat.of ↥(U ∩ V))) m')) s :=
        map_zsmul _ _ _
      rw [hlin2, hchain]
      abel
    have h2 := pdCruxD_homologyπ_eq_of_d_eq_sub wc (((-1 : ℤ) ^ (k+1)) • s) s'' hsub
    have hlin3 : (ModuleCat.Hom.hom (HomologicalComplex.homologyπ
          (singularChains ℤ (TopCat.of ↥(U ∩ V))) m')) (((-1 : ℤ) ^ (k+1)) • s)
        = ((-1 : ℤ) ^ (k+1)) • (ModuleCat.Hom.hom (HomologicalComplex.homologyπ
            (singularChains ℤ (TopCat.of ↥(U ∩ V))) m')) s :=
      map_zsmul _ _ _
    rw [h2, hlin3, hs_eq_D]
  -- ## Step 12: the parity of the sign
  have hfin : (mvδ U V m').hom
        ((ModuleCat.Hom.hom (CategoryTheory.inv (HomologicalComplex.homologyMap Φ (m'+1))))
          (goodD (k + (m'+1)) c (U ∪ V : Set M) hW (K₁ ∪ K₂) hKW hKc k (m'+1) rfl
            ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (relComplex ℤ
              (TopCat.of (U ∪ V : Set M))
              (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k)) zx)))
      = ((-1 : ℤ) ^ (k+1)) • D := by
    rw [hLHS, hhom]
  rcases Nat.even_or_odd (k+1) with h | h
  · left
    rw [h.neg_one_pow, one_smul] at hfin
    simpa using hfin
  · right
    rw [h.neg_one_pow] at hfin
    simpa using hfin


theorem pd_union_hit_mod_kernel {M : TopCat} [T2Space M] {N : ℕ}
    {c : (Work.Cohomology.singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    (hUU : Work.Cohomology.Good N c U hU) (hVV : Work.Cohomology.Good N c V hV)
    (hII : Work.Cohomology.Good N c (U ∩ V) hI)
    (k m : ℕ) (hkm : k + m = N) (hm : 1 ≤ m)
    (Φ : Work.Cohomology.smallChains U V ⟶
      Work.Cohomology.singularChains ℤ (TopCat.of (U ∪ V : Set M)))
    (hΦincl : CategoryTheory.CategoryStruct.comp Φ
        (Work.Cohomology.inclChains M (U ∪ V : Set M)) = Work.Cohomology.smallToSing U V)
    (hΦiso : ∀ n, CategoryTheory.IsIso (HomologicalComplex.homologyMap Φ n))
    (hΦU : CategoryTheory.CategoryStruct.comp (Work.Cohomology.smallOfU U V) Φ
      = Work.Cohomology.chainMap ℤ (TopCat.of U) (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdIncl (U ∪ V : Set M) U Set.subset_union_left))
    (hΦV : CategoryTheory.CategoryStruct.comp (Work.Cohomology.smallOfV U V) Φ
      = Work.Cohomology.chainMap ℤ (TopCat.of V) (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdIncl (U ∪ V : Set M) V Set.subset_union_right)) :
    ∀ y : (Work.Cohomology.singularChains ℤ (TopCat.of (U ∪ V : Set M))).homology m,
      ∃ (K : Set M) (hKW : K ⊆ U ∪ V) (hKc : IsCompact K)
        (x : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) K)).homology k),
        Work.Cohomology.goodD N c (U ∪ V : Set M) (hU.union hV) K hKW hKc k m hkm x - y
          ∈ LinearMap.range (ModuleCat.Hom.hom
              (CategoryTheory.CategoryStruct.comp
                (HomologicalComplex.homologyMap (Work.Cohomology.mvRight U V) m)
                (HomologicalComplex.homologyMap Φ m))) := by
  intro y
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hN : k + (m' + 1) = N := hkm
  have hN' : k + 1 + m' = N := by omega
  have hW : IsOpen (U ∪ V : Set M) := hU.union hV
  haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap Φ (m' + 1)) := hΦiso (m' + 1)
  -- the lifted class and the Mayer-Vietoris connecting class
  set yt : (Work.Cohomology.smallChains U V).homology (m' + 1) :=
    (CategoryTheory.inv (HomologicalComplex.homologyMap Φ (m' + 1))).hom y with hyt
  set t : (Work.Cohomology.singularChains ℤ (TopCat.of (U ∩ V : Set M))).homology m' :=
    (Work.Cohomology.mvδ U V m').hom yt with ht
  have hdead : (HomologicalComplex.homologyMap (Work.Cohomology.mvLeft U V) m').hom t = 0 := by
    have h2 : (ModuleCat.Hom.hom ((Work.Cohomology.mvδ U V m') ≫
        HomologicalComplex.homologyMap (Work.Cohomology.mvLeft U V) m')) yt = 0 := by
      rw [Work.Cohomology.mvδ_comp U V m']
      rfl
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    simpa only [← ht] using h2
  -- `Good (U∩V)` realises `t`
  obtain ⟨K₀, hK₀I, hK₀c, w, hw⟩ := (hII (k + 1) m' hN').1 t
  -- the transport to the union
  obtain ⟨K₁, K₂, hK₁U, hK₂V, hK₀K₁, hK₀K₂, hK₁c, hK₂c, zx, zψ, φA, φB,
      hφA, hφB, hφAk, hφBk, hzx, hzψres⟩ :=
    pd_transport_psi hU hV hI hUU hVV hII k m' hN hN' hK₀I hK₀c w (by rw [hw]; exact hdead)
  -- the crux square
  have hcrux : (Work.Cohomology.mvδ U V m').hom
        ((CategoryTheory.inv (HomologicalComplex.homologyMap Φ (m' + 1))).hom
          (goodD N c (U ∪ V : Set M) hW (K₁ ∪ K₂)
            (Set.union_subset (hK₁U.trans Set.subset_union_left)
              (hK₂V.trans Set.subset_union_right)) (hK₁c.union hK₂c) k (m' + 1) hN
            ((HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k) zx)))
      = t
      ∨ (Work.Cohomology.mvδ U V m').hom
        ((CategoryTheory.inv (HomologicalComplex.homologyMap Φ (m' + 1))).hom
          (goodD N c (U ∪ V : Set M) hW (K₁ ∪ K₂)
            (Set.union_subset (hK₁U.trans Set.subset_union_left)
              (hK₂V.trans Set.subset_union_right)) (hK₁c.union hK₂c) k (m' + 1) hN
            ((HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k) zx)))
      = -t := by
    have hD : t = goodD N c (U ∩ V : Set M) hI K₀ hK₀I hK₀c (k + 1) m' hN'
        ((HomologicalComplex.homologyMap (relComplexMap ℤ
          (pdRelSub (U ∩ V : Set M) K₀)
          (pdRelSub (U ∪ V : Set M) K₀)
          (pdIncl (U ∪ V : Set M) (U ∩ V)
            (Set.inter_subset_left.trans Set.subset_union_left)) (fun x hx => hx)) (k + 1)).hom
          ((HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) K₀)) (k + 1)) zψ)) := by
      rw [hzψres, ← hw]
    exact pd_crux_goodD_strong hU hV hK₁U hK₂V hK₁c hK₂c hK₀I hK₀c hK₀K₁ hK₀K₂ k m' hN hN'
      zx zψ φA φB hφA hφB hφAk hφBk hzx w hzψres.symm t hw.symm Φ hΦiso hΦU hΦV
  -- conclusion
  have hKW : K₁ ∪ K₂ ⊆ U ∪ V :=
    Set.union_subset (hK₁U.trans Set.subset_union_left) (hK₂V.trans Set.subset_union_right)
  have hKc : IsCompact (K₁ ∪ K₂) := hK₁c.union hK₂c
  -- the final step: a class whose duality image has the connecting class `t` is `y` modulo the
  -- Mayer-Vietoris image
  have finish : ∀ (wx : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homology k),
      (Work.Cohomology.mvδ U V m').hom
        ((CategoryTheory.inv (HomologicalComplex.homologyMap Φ (m' + 1))).hom
          (goodD N c (U ∪ V : Set M) hW (K₁ ∪ K₂) hKW hKc k (m' + 1) hN wx)) = t →
      (goodD N c (U ∪ V : Set M) hW (K₁ ∪ K₂) hKW hKc k (m' + 1) hN wx - y)
        ∈ LinearMap.range (ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp
            (HomologicalComplex.homologyMap (Work.Cohomology.mvRight U V) (m' + 1))
            (HomologicalComplex.homologyMap Φ (m' + 1)))) := by
    intro wx hwx
    have hzero : (ModuleCat.Hom.hom (Work.Cohomology.mvδ U V m'))
        (((CategoryTheory.inv (HomologicalComplex.homologyMap Φ (m' + 1))).hom
        (goodD N c (U ∪ V : Set M) hW (K₁ ∪ K₂) hKW hKc k (m' + 1) hN wx)) - yt) = 0 := by
      rw [map_sub, hwx, ← ht, sub_self]
    have hex : LinearMap.range (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (Work.Cohomology.mvRight U V) (m' + 1)))
        = LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.mvδ U V m')) :=
      (CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker (S :=
        CategoryTheory.ShortComplex.mk
          (HomologicalComplex.homologyMap (Work.Cohomology.mvRight U V) (m' + 1))
          (Work.Cohomology.mvδ U V m') (Work.Cohomology.mv_comp_δ U V m'))).mp
        (Work.Cohomology.mv_H_exact₃ U V m')
    obtain ⟨z₂, hz₂⟩ := LinearMap.mem_range.mp (by
      rw [hex]
      exact LinearMap.mem_ker.mpr hzero)
    refine ⟨z₂, ?_⟩
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, hz₂, map_sub]
    have hy1 : (HomologicalComplex.homologyMap Φ (m' + 1)).hom
        ((CategoryTheory.inv (HomologicalComplex.homologyMap Φ (m' + 1))).hom
          (goodD N c (U ∪ V : Set M) hW (K₁ ∪ K₂) hKW hKc k (m' + 1) hN wx))
        = goodD N c (U ∪ V : Set M) hW (K₁ ∪ K₂) hKW hKc k (m' + 1) hN wx :=
      CategoryTheory.IsIso.inv_hom_id_apply _ _
    have hy2 : (HomologicalComplex.homologyMap Φ (m' + 1)).hom yt = y := by
      rw [hyt]
      exact CategoryTheory.IsIso.inv_hom_id_apply _ _
    rw [hy1, hy2]
  rcases hcrux with hcrux | hcrux
  · refine ⟨K₁ ∪ K₂, hKW, hKc, (HomologicalComplex.homologyπ (relComplex ℤ
      (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k) zx, ?_⟩
    exact finish _ hcrux
  · refine ⟨K₁ ∪ K₂, hKW, hKc, -((HomologicalComplex.homologyπ (relComplex ℤ
      (TopCat.of (U ∪ V : Set M))
      (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k) zx), ?_⟩
    refine finish _ ?_
    have hgoodD_neg : goodD N c (U ∪ V : Set M) hW (K₁ ∪ K₂) hKW hKc k (m' + 1) hN
        (-((HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k) zx))
        = -(goodD N c (U ∪ V : Set M) hW (K₁ ∪ K₂) hKW hKc k (m' + 1) hN
            ((HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))) k) zx)) := by
      simp only [goodD]
      rw [map_neg, LinearMap.neg_apply]
    rw [hgoodD_neg]
    simp only [map_neg]
    rw [hcrux, neg_neg]

end

end Work.Cohomology
