import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_goodD_incl
import Submission.Work.Cohomology.pd_goodD_natural
import Submission.Work.Cohomology.pd_goodD_rep
import Submission.Work.Cohomology.pd_hatcher_data
import Submission.Work.Cohomology.pd_hatcher_W
import Submission.Work.Cohomology.pd_hatcher_Xdata
import Submission.Work.Cohomology.pd_hatcher_cycles_inter
import Submission.Work.Cohomology.cap_mem_range_inclChains
import Submission.Work.Cohomology.cap_natural
import Submission.Work.Cohomology.capRelAux
import Submission.Work.Cohomology.pd_ab_clean
import Submission.Work.Cohomology.pd_glue2
import Submission.Work.Cohomology.mem_range_inclChains_of_image
import Submission.Work.Cohomology.chainRetract_mem_range_inclChains
import Submission.Work.Cohomology.pd_relsub_aux
import Submission.Work.Cohomology.pd_localFundClass_of_cycle
import Submission.Work.Cohomology.pd_union_crux_zero_wk
import Submission.Work.Cohomology.cap_cochainDiff_mem_range
import Submission.Work.Cohomology.pdABInclRel_comp_pdABEnlarge
import Submission.Work.Cohomology.pdABdelta_natural
import Submission.Work.Cohomology.pdABCoh_quasiIso
import Submission.Work.Cohomology.pd_boundary_of_zero_class
import Submission.Work.Cohomology.pd_split_aux
import Submission.Work.Cohomology.pd_split_setup
import Submission.Work.Cohomology.pd_us_frame
import Submission.Work.Cohomology.pd_hatcher_inter4
import Submission.Work.Cohomology.pd_inter_cap_boundary
import Submission.Work.Cohomology.pd_us_cycles_eq_of_class_eq
import Submission.Work.Cohomology.pd_us_cap_cochainDiff
import Submission.Work.Cohomology.pd_us_ab_resolve

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The final assembly of `pd_union_split`

This module contains the last part of the proof of `Work.Cohomology.pd_union_split`: given a
relative cocycle `u` of the "`A ∪ B`" slot of the pair `(U ∪ V, (U ∪ V)∖(K₁ ∪ K₂))` whose
restriction to `U ∩ V` is killed after enlarging inside `U ∩ V`, together with primitives
`φA, φB` of its differential and a correction `χ`, produce the enlargement `(K₁', K₂')` of
`(K₁, K₂)` and the two classes `x₁, x₂` with `enl x = enl x₁ - enl x₂`.

It is split out of `pd_us_aux` so that the proof runs in a small local context (the long proof of
`pd_us_main` has hundreds of hypotheses, which makes the elaborator very slow).
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable {M : TopCat}

set_option backward.isDefEq.respectTransparency false in
/-- The underlying cochain of the differential of a relative cochain complex. -/
theorem pd_us_relComplex_d_coe {X : TopCat} {A : Set X} {n : ℕ} (x : (relComplex ℤ X A).X n) :
    (((relComplex ℤ X A).d n (n + 1)).hom x).1
      = cochainDiff ℤ (TopCat.toSSet.obj X) (n := n) x.1 := by
  rw [relComplex_d, relDiff, ModuleCat.hom_ofHom]
  exact (relDiffLM_coe ℤ X A n x).trans
    (pd_us_ab_resolve_singularD_eq_cochainDiff X n x.1)

set_option backward.isDefEq.respectTransparency false in
/-- A relative cochain whose underlying cochain is a cocycle is a cocycle. -/
theorem pd_us_relComplex_d_eq_zero {X : TopCat} {A : Set X} {n : ℕ}
    (x : (relComplex ℤ X A).X n)
    (h : cochainDiff ℤ (TopCat.toSSet.obj X) (n := n) x.1 = 0) :
    (relComplex ℤ X A).d n (n + 1) x = 0 := by
  apply Subtype.ext
  rw [pd_us_relComplex_d_coe x, h]
  exact Submodule.coe_zero.symm

set_option backward.isDefEq.respectTransparency false in
/-- The pair map along the identity is the identity on underlying cochains. -/
theorem pd_us_relComplexMap_id_coe {X : TopCat} {A B : Set X} (h : ∀ x ∈ A, (𝟙 X) x ∈ B)
    (n : ℕ) (x : (relComplex ℤ X B).X n) :
    (((((relComplexMap ℤ A B (𝟙 X) h).f n)).hom) x).1 = x.1 := by
  rw [relComplexMap_f, ModuleCat.hom_ofHom]
  exact PDABClean.relMapLM_id_coe X h n x

set_option backward.isDefEq.respectTransparency false in
/-- The enlargement of a relative complex is the identity on underlying cochains. -/
theorem pd_us_pdRelComplexEnlarge_coe {M : TopCat} {W : Set M} {K K' : Set M} (h : K ⊆ K')
    {n : ℕ} (x : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).X n) :
    ((((pdRelComplexEnlarge W h).f n)).hom x).1 = x.1 := by
  rw [pdRelComplexEnlarge, relComplexMap_f, ModuleCat.hom_ofHom]
  exact PDABClean.relMapLM_id_coe (TopCat.of W) (pdRelSub_mono h) n x

set_option backward.isDefEq.respectTransparency false in
/-- The underlying cochain of the enlargement of a cycle. -/
theorem pd_us_pdRelComplexEnlarge_iCycles_coe {M : TopCat} {W : Set M} {K K' : Set M}
    (h : K ⊆ K') {n : ℕ} (z : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).cycles n) :
    ((((relComplex ℤ (TopCat.of W) (pdRelSub W K')).iCycles n).hom)
      ((HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h) n).hom z)).1
      = ((((relComplex ℤ (TopCat.of W) (pdRelSub W K)).iCycles n).hom) z).1 := by
  rw [Crux.cruxCyclesMap_i_apply' (pdRelComplexEnlarge W h) n z]
  exact pd_us_pdRelComplexEnlarge_coe h _

set_option backward.isDefEq.respectTransparency false in
/-- `pdRelComplexEnlarge` does not depend on the proof of the inclusion. -/
theorem pd_us_pdRelComplexEnlarge_congr {M : TopCat} {W : Set M} {K K' : Set M}
    (h h' : K ⊆ K') : pdRelComplexEnlarge W h = pdRelComplexEnlarge W h' :=
  congrArg (fun (h : K ⊆ K') => pdRelComplexEnlarge W h) (Subsingleton.elim h h')

set_option backward.isDefEq.respectTransparency false in
/-- A cycle is determined by its underlying chain. -/
theorem pd_us_cycles_eq_of_iCycles_eq {K : CochainComplex (ModuleCat ℤ) ℕ} {n : ℕ}
    (z₁ z₂ : K.cycles n) (h : K.iCycles n z₁ = K.iCycles n z₂) : z₁ = z₂ :=
  (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance h

set_option backward.isDefEq.respectTransparency false in
/-- Set algebra for the relative complements: if `K₁ ∩ K₂ ⊆ L`, then
`pdRelSub W (K₁ ∪ L) ∪ pdRelSub W (K₂ ∪ L) = pdRelSub W L`. -/
theorem pd_us_pdRelSub_union_union {M : TopCat} (W : Set M) {K₁ K₂ L : Set M}
    (h : K₁ ∩ K₂ ⊆ L) :
    pdRelSub W (K₁ ∪ L) ∪ pdRelSub W (K₂ ∪ L) = pdRelSub W L := by
  rw [pdRelSub_union W K₁ L, pdRelSub_union W K₂ L, ← Set.union_inter_distrib_right,
    pdRelSub_union_sub W K₁ K₂]
  exact Set.inter_eq_right.mpr (pdRelSub_mono h)

set_option backward.isDefEq.respectTransparency false in
/-- **The final assembly of `pd_union_split`.** -/
theorem pd_us_finish {M : TopCat} [T2Space M]
    {U V : Set M} (hI : IsOpen (U ∩ V)) (hW : IsOpen (U ∪ V : Set M))
    (hUVm : U ∩ V ⊆ (U ∪ V : Set M))
    {K₁ K₂ : Set M} (hK₁U : K₁ ⊆ U) (hK₂V : K₂ ⊆ V)
    (hK₁c : IsCompact K₁) (hK₂c : IsCompact K₂)
    {k : ℕ}
    {x : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homology k}
    {z : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).cycles k}
    (hz : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homologyπ k z = x)
    {u : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) K₁ ∪ pdRelSub (U ∪ V : Set M) K₂)).cycles (k + 1)}
    {φA : (relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₁)).X k}
    {φB : (relComplex ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₂)).X k}
    (hdecomp : ((relComplex ℤ (TopCat.of (U ∪ V : Set M))
        (pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k z).1 = φA.1 - φB.1)
    (hψB : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) φB.1
      = cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) φA.1)
    {χ : Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) k}
    (hχmem : χ ∈ relKern ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₁) k ⊓
      relKern ℤ (TopCat.of (U ∪ V : Set M)) (pdRelSub (U ∪ V : Set M) K₂) k)
    (hχd : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) χ
      = (show Cochain ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (k + 1) from
          ((relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (pdRelSub (U ∪ V : Set M) K₁ ∪ pdRelSub (U ∪ V : Set M) K₂)).iCycles (k + 1) u).1)
        - cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))) (n := k) φA.1)
    (hkill0 : ∃ (L'' : Set M) (h₁ : K₁ ∩ K₂ ⊆ L'') (h₂ : L'' ⊆ U ∩ V) (h₃ : IsCompact L''),
      (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∩ V) h₁) (k + 1)).hom
        ((HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub (U ∩ V) (K₁ ∩ K₂))
          (pdRelSub (U ∪ V : Set M) K₁ ∪ pdRelSub (U ∪ V : Set M) K₂)
          (pdIncl (U ∪ V : Set M) (U ∩ V) hUVm) (fun x hx => not_and_or.mp hx)) (k + 1)).hom
        ((HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (pdRelSub (U ∪ V : Set M) K₁ ∪ pdRelSub (U ∪ V : Set M) K₂)) (k + 1)).hom u)) = 0) :
    ∃ (K₁' K₂' : Set M) (h₁ : K₁ ⊆ K₁') (h₂ : K₂ ⊆ K₂') (hK₁'U : K₁' ⊆ U) (hK₂'V : K₂' ⊆ V)
      (hK₁'c : IsCompact K₁') (hK₂'c : IsCompact K₂')
      (x₁ : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (pdRelSub (U ∪ V : Set M) K₁')).homology k)
      (x₂ : (relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (pdRelSub (U ∪ V : Set M) K₂')).homology k),
      (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
        (Set.union_subset (h₁.trans Set.subset_union_left)
          (h₂.trans Set.subset_union_right) : K₁ ∪ K₂ ⊆ K₁' ∪ K₂')) k) x
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
            (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₂')) k) x₁
          - (HomologicalComplex.homologyMap (pdRelComplexEnlarge (U ∪ V : Set M)
            (Set.subset_union_right : K₂' ⊆ K₁' ∪ K₂')) k) x₂ := by

  classical
  let W := U ∪ V
  let X := TopCat.of W
  have hWo : IsOpen W := hW
  let φAc : Cochain ℤ (TopCat.toSSet.obj X) k := φA.1
  let φBc : Cochain ℤ (TopCat.toSSet.obj X) k := φB.1
  let χc : Cochain ℤ (TopCat.toSSet.obj X) k := χ
  let ψuX : Cochain ℤ (TopCat.toSSet.obj X) (k + 1) :=
    (show Cochain ℤ (TopCat.toSSet.obj X) (k + 1) from
      ((relComplex ℤ X (pdRelSub W K₁ ∪ pdRelSub W K₂)).iCycles (k + 1) u).1)
  have hχmc : χc ∈ relKern ℤ X (pdRelSub W K₁) k ⊓ relKern ℤ X (pdRelSub W K₂) k := hχmem
  have hχdc : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) χc
      = ψuX - cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φAc := hχd
  have hdec : ((relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).iCycles k z).1 = φAc - φBc := hdecomp
  obtain ⟨L'', hK₀L'', hL''I, hL''c, hL''zero⟩ := hkill0
  let φAB :=
    relComplexMap ℤ (pdRelSub (U ∩ V) (K₁ ∩ K₂)) (pdRelSub W K₁ ∪ pdRelSub W K₂)
      (pdIncl W (U ∩ V) hUVm) (fun x hx => not_and_or.mp hx)
  -- ================= Step 9: transport to the union =================
  have hK₁'U : K₁ ∪ L'' ⊆ U := Set.union_subset hK₁U (hL''I.trans Set.inter_subset_left)
  have hK₂'V : K₂ ∪ L'' ⊆ V := Set.union_subset hK₂V (hL''I.trans Set.inter_subset_right)
  have hK₁'c : IsCompact (K₁ ∪ L'') := hK₁c.union hL''c
  have hK₂'c : IsCompact (K₂ ∪ L'') := hK₂c.union hL''c
  have hunion : pdRelSub W (K₁ ∪ L'') ∪ pdRelSub W (K₂ ∪ L'') = pdRelSub W L'' :=
    pd_us_pdRelSub_union_union W hK₀L''
  let enlW :=
    relComplexMap ℤ (pdRelSub W L'') (pdRelSub W K₁ ∪ pdRelSub W K₂) (𝟙 X)
      (fun x hx => not_and_or.mp (fun hk => hx (hK₀L'' hk)))
  let restrL :=
    relComplexMap ℤ (pdRelSub (U ∩ V) L'') (pdRelSub W L'') (pdIncl W (U ∩ V) hUVm)
      (fun x hx => hx)
  let enlI := relComplexMap ℤ (pdRelSub (U ∩ V) L'') (pdRelSub (U ∩ V) (K₁ ∩ K₂))
    (𝟙 (TopCat.of (U ∩ V : Set M))) (fun x hx => pdRelSub_mono hK₀L'' hx)
  have hrestrIso : IsIso (HomologicalComplex.homologyMap restrL (k + 1)) :=
    pdCohExcision hUVm hI hWo hL''I hL''c (k + 1)
  have hsquare : enlW ≫ restrL = φAB ≫ enlI := by
    have h1 := capRel_relComplexMap_comp ℤ (pdRelSub (U ∩ V) L'') (pdRelSub W L'')
      (pdRelSub W K₁ ∪ pdRelSub W K₂) (pdIncl W (U ∩ V) hUVm) (𝟙 X)
      (fun x hx => hx) (fun x hx => not_and_or.mp (fun hk => hx (hK₀L'' hk)))
    have h2 := capRel_relComplexMap_comp ℤ (pdRelSub (U ∩ V) L'')
      (pdRelSub (U ∩ V) (K₁ ∩ K₂)) (pdRelSub W K₁ ∪ pdRelSub W K₂)
      (𝟙 (TopCat.of (U ∩ V : Set M))) (pdIncl W (U ∩ V) hUVm)
      (fun x hx => pdRelSub_mono hK₀L'' hx) (fun x hx => not_and_or.mp hx)
    have h3 : relComplexMap ℤ (pdRelSub (U ∩ V) L'') (pdRelSub W K₁ ∪ pdRelSub W K₂)
        (pdIncl W (U ∩ V) hUVm ≫ 𝟙 X)
        (fun x hx => not_and_or.mp (fun hk => hx (hK₀L'' hk)))
        = relComplexMap ℤ (pdRelSub (U ∩ V) L'') (pdRelSub W K₁ ∪ pdRelSub W K₂)
          (𝟙 (TopCat.of (U ∩ V : Set M)) ≫ pdIncl W (U ∩ V) hUVm)
          (fun x hx => not_and_or.mp (fun hk => pdRelSub_mono hK₀L'' hx hk)) :=
      capRel_relComplexMap_congr ℤ (pdRelSub (U ∩ V) L'')
        (pdRelSub W K₁ ∪ pdRelSub W K₂)
        (f := pdIncl W (U ∩ V) hUVm ≫ 𝟙 X)
        (f' := 𝟙 (TopCat.of (U ∩ V : Set M)) ≫ pdIncl W (U ∩ V) hUVm)
        (by rw [Category.id_comp, Category.comp_id])
        (fun x hx => not_and_or.mp (fun hk => hx (hK₀L'' hk)))
        (fun x hx => not_and_or.mp (fun hk => pdRelSub_mono hK₀L'' hx hk))
    exact h1.symm.trans (h3.trans h2)
  have hkill : (HomologicalComplex.homologyMap enlW (k + 1)).hom
      ((HomologicalComplex.homologyπ (relComplex ℤ X (pdRelSub W K₁ ∪ pdRelSub W K₂))
        (k + 1)).hom u) = 0 := by
    haveI := hrestrIso
    have hinj : Function.Injective (HomologicalComplex.homologyMap restrL (k + 1)).hom :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    apply hinj
    rw [map_zero]
    have hcomp : (HomologicalComplex.homologyMap restrL (k + 1)).hom
        ((HomologicalComplex.homologyMap enlW (k + 1)).hom
          ((HomologicalComplex.homologyπ (relComplex ℤ X (pdRelSub W K₁ ∪ pdRelSub W K₂))
            (k + 1)).hom u))
        = (HomologicalComplex.homologyMap (enlW ≫ restrL) (k + 1)).hom
          ((HomologicalComplex.homologyπ (relComplex ℤ X (pdRelSub W K₁ ∪ pdRelSub W K₂))
            (k + 1)).hom u) := by
      rw [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]
      rfl
    rw [hcomp, hsquare, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp,
      LinearMap.comp_apply]
    exact hL''zero
  -- ================= Step 10: a common primitive `θ` =================
  have hze : (HomologicalComplex.homologyπ (relComplex ℤ X (pdRelSub W L'')) (k + 1)).hom
      ((HomologicalComplex.cyclesMap enlW (k + 1)).hom u) = 0 := by
    have hnat := congrArg (fun (g : (relComplex ℤ X (pdRelSub W K₁ ∪ pdRelSub W K₂)).cycles
          (k + 1) ⟶ HomologicalComplex.homology (relComplex ℤ X (pdRelSub W L'')) (k + 1)) =>
        g.hom u)
      (HomologicalComplex.homologyπ_naturality (φ := enlW) (i := k + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
    rw [← hnat]
    exact hkill
  obtain ⟨θ₀, hθ₀⟩ := pd_us_ab_resolve_exists_of_homologyπ_eq_zero
    (relComplex ℤ X (pdRelSub W L'')) k ((HomologicalComplex.cyclesMap enlW (k + 1)).hom u) hze
  have hθ₀c : (show Cochain ℤ (TopCat.toSSet.obj X) k from θ₀.1) = θ₀.1 := rfl
  have hθ₀coe : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) θ₀.1 = ψuX := by
    have h1 : ((((relComplex ℤ X (pdRelSub W L'')).d k (k + 1)).hom) θ₀).1
        = ((((relComplex ℤ X (pdRelSub W K₁ ∪ pdRelSub W K₂)).iCycles (k + 1)).hom) u).1 := by
      rw [hθ₀, Crux.cruxCyclesMap_i_apply' enlW (k + 1) u]
      exact pd_us_relComplexMap_id_coe (X := X) (A := pdRelSub W L'')
        (B := pdRelSub W K₁ ∪ pdRelSub W K₂)
        (fun x hx => not_and_or.mp (fun hk => hx (hK₀L'' hk))) (k + 1) _
    rw [pd_us_relComplex_d_coe θ₀] at h1
    exact h1
  have hθ₀memU : θ₀.1 ∈ relKern ℤ X (pdRelSub W (K₁ ∪ L'') ∪ pdRelSub W (K₂ ∪ L'')) k := by
    rw [hunion]
    exact θ₀.2
  have hθmem₁ : θ₀.1 ∈ relKern ℤ X (pdRelSub W (K₁ ∪ L'')) k :=
    relKern_mono (R := ℤ) (X := X) (A := pdRelSub W (K₁ ∪ L'') ∪ pdRelSub W (K₂ ∪ L''))
      (C := pdRelSub W (K₁ ∪ L'')) Set.subset_union_left (n := k) hθ₀memU
  have hθmem₂ : θ₀.1 ∈ relKern ℤ X (pdRelSub W (K₂ ∪ L'')) k :=
    relKern_mono (R := ℤ) (X := X) (A := pdRelSub W (K₁ ∪ L'') ∪ pdRelSub W (K₂ ∪ L''))
      (C := pdRelSub W (K₂ ∪ L'')) Set.subset_union_right (n := k) hθ₀memU
  have hχmem₁ : χc ∈ relKern ℤ X (pdRelSub W (K₁ ∪ L'')) k :=
    relKern_mono (R := ℤ) (X := X) (A := pdRelSub W K₁) (C := pdRelSub W (K₁ ∪ L''))
      (pdRelSub_mono Set.subset_union_left) (n := k) hχmc.1
  have hχmem₂ : χc ∈ relKern ℤ X (pdRelSub W (K₂ ∪ L'')) k :=
    relKern_mono (R := ℤ) (X := X) (A := pdRelSub W K₂) (C := pdRelSub W (K₂ ∪ L''))
      (pdRelSub_mono Set.subset_union_left) (n := k) hχmc.2
  let θ : Cochain ℤ (TopCat.toSSet.obj X) k := (show Cochain ℤ (TopCat.toSSet.obj X) k from θ₀.1) - χc
  have hθmem : θ ∈ relKern ℤ X (pdRelSub W (K₁ ∪ L'')) k ⊓
      relKern ℤ X (pdRelSub W (K₂ ∪ L'')) k :=
    ⟨Submodule.sub_mem _ (show θ₀.1 ∈ relKern ℤ X (pdRelSub W (K₁ ∪ L'')) k from hθmem₁) hχmem₁,
      Submodule.sub_mem _ (show θ₀.1 ∈ relKern ℤ X (pdRelSub W (K₂ ∪ L'')) k from hθmem₂) hχmem₂⟩
  have hθcoe : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) θ
      = cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φAc := by
    show cochainDiff ℤ (TopCat.toSSet.obj X) (n := k)
        ((show Cochain ℤ (TopCat.toSSet.obj X) k from θ₀.1) - χc)
      = cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φAc
    rw [← cochainDiffLM_apply ℤ (TopCat.toSSet.obj X) k _,
      map_sub, cochainDiffLM_apply, cochainDiffLM_apply, hθ₀coe, hχdc]
    abel_nf
  -- ================= Step 11: assemble =================
  have hφA'mem : φAc - θ ∈ relKern ℤ X (pdRelSub W (K₁ ∪ L'')) k :=
    Submodule.sub_mem _ (relKern_mono (R := ℤ) (X := X) (A := pdRelSub W K₁)
      (C := pdRelSub W (K₁ ∪ L'')) (pdRelSub_mono Set.subset_union_left) (n := k) φA.2)
      (show θ ∈ relKern ℤ X (pdRelSub W (K₁ ∪ L'')) k from hθmem.1)
  have hφB'mem : φBc - θ ∈ relKern ℤ X (pdRelSub W (K₂ ∪ L'')) k :=
    Submodule.sub_mem _ (relKern_mono (R := ℤ) (X := X) (A := pdRelSub W K₂)
      (C := pdRelSub W (K₂ ∪ L'')) (pdRelSub_mono Set.subset_union_left) (n := k) φB.2)
      (show θ ∈ relKern ℤ X (pdRelSub W (K₂ ∪ L'')) k from hθmem.2)
  have hφA'd : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) (φAc - θ) = 0 := by
    rw [← cochainDiffLM_apply ℤ (TopCat.toSSet.obj X) k (φAc - θ), map_sub, cochainDiffLM_apply,
      cochainDiffLM_apply, hθcoe]
    abel_nf
  have hφB'd : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) (φBc - θ) = 0 := by
    rw [← cochainDiffLM_apply ℤ (TopCat.toSSet.obj X) k (φBc - θ), map_sub, cochainDiffLM_apply,
      cochainDiffLM_apply, hψB, hθcoe]
    first
      | rfl
      | rw [sub_self]
      | abel_nf
  refine ⟨K₁ ∪ L'', K₂ ∪ L'', Set.subset_union_left, Set.subset_union_left, hK₁'U, hK₂'V,
    hK₁'c, hK₂'c, ?_, ?_, ?_⟩
  · exact (relComplex ℤ X (pdRelSub W (K₁ ∪ L''))).homologyπ k
      (cocycleOfK (relComplex ℤ X (pdRelSub W (K₁ ∪ L''))) ⟨φAc - θ, hφA'mem⟩
        (pd_us_relComplex_d_eq_zero ⟨φAc - θ, hφA'mem⟩ hφA'd))
  · exact (relComplex ℤ X (pdRelSub W (K₂ ∪ L''))).homologyπ k
      (cocycleOfK (relComplex ℤ X (pdRelSub W (K₂ ∪ L''))) ⟨φBc - θ, hφB'mem⟩
        (pd_us_relComplex_d_eq_zero ⟨φBc - θ, hφB'mem⟩ hφB'd))
  · have h0x : K₁ ∪ K₂ ⊆ (K₁ ∪ L'') ∪ (K₂ ∪ L'') :=
      Set.union_subset (Set.subset_union_left.trans Set.subset_union_left)
        (Set.subset_union_left.trans Set.subset_union_right)
    have h1x : K₁ ∪ L'' ⊆ (K₁ ∪ L'') ∪ (K₂ ∪ L'') := Set.subset_union_left
    have h2x : K₂ ∪ L'' ⊆ (K₁ ∪ L'') ∪ (K₂ ∪ L'') := Set.subset_union_right
    have key : (HomologicalComplex.homologyMap (pdRelComplexEnlarge W h0x) k).hom x
        = (HomologicalComplex.homologyMap (pdRelComplexEnlarge W h1x) k).hom
            ((relComplex ℤ X (pdRelSub W (K₁ ∪ L''))).homologyπ k
              (cocycleOfK (relComplex ℤ X (pdRelSub W (K₁ ∪ L''))) ⟨φAc - θ, hφA'mem⟩
                (pd_us_relComplex_d_eq_zero ⟨φAc - θ, hφA'mem⟩ hφA'd)))
          - (HomologicalComplex.homologyMap (pdRelComplexEnlarge W h2x) k).hom
            ((relComplex ℤ X (pdRelSub W (K₂ ∪ L''))).homologyπ k
              (cocycleOfK (relComplex ℤ X (pdRelSub W (K₂ ∪ L''))) ⟨φBc - θ, hφB'mem⟩
                (pd_us_relComplex_d_eq_zero ⟨φBc - θ, hφB'mem⟩ hφB'd))) := by
      rw [← hz]
      have e0z : (HomologicalComplex.homologyMap (pdRelComplexEnlarge W h0x) k).hom
          ((HomologicalComplex.homologyπ (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))) k).hom z)
          = (HomologicalComplex.homologyπ (relComplex ℤ X
              (pdRelSub W ((K₁ ∪ L'') ∪ (K₂ ∪ L'')))) k).hom
            ((HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h0x) k).hom z) := by
        have hnat := congrArg (fun (g : (relComplex ℤ X (pdRelSub W (K₁ ∪ K₂))).cycles k ⟶
            HomologicalComplex.homology (relComplex ℤ X
              (pdRelSub W ((K₁ ∪ L'') ∪ (K₂ ∪ L'')))) k) => g.hom z)
          (HomologicalComplex.homologyπ_naturality (φ := pdRelComplexEnlarge W h0x) (i := k))
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hnat
      have e1z : (HomologicalComplex.homologyMap (pdRelComplexEnlarge W h1x) k).hom
          ((HomologicalComplex.homologyπ (relComplex ℤ X (pdRelSub W (K₁ ∪ L''))) k).hom
            (cocycleOfK (relComplex ℤ X (pdRelSub W (K₁ ∪ L''))) ⟨φAc - θ, hφA'mem⟩
              (pd_us_relComplex_d_eq_zero ⟨φAc - θ, hφA'mem⟩ hφA'd)))
          = (HomologicalComplex.homologyπ (relComplex ℤ X
              (pdRelSub W ((K₁ ∪ L'') ∪ (K₂ ∪ L'')))) k).hom
            ((HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h1x) k).hom
              (cocycleOfK (relComplex ℤ X (pdRelSub W (K₁ ∪ L''))) ⟨φAc - θ, hφA'mem⟩
                (pd_us_relComplex_d_eq_zero ⟨φAc - θ, hφA'mem⟩ hφA'd))) := by
        have hnat := congrArg (fun (g : (relComplex ℤ X (pdRelSub W (K₁ ∪ L''))).cycles k ⟶
            HomologicalComplex.homology (relComplex ℤ X
              (pdRelSub W ((K₁ ∪ L'') ∪ (K₂ ∪ L'')))) k) => g.hom
              (cocycleOfK (relComplex ℤ X (pdRelSub W (K₁ ∪ L''))) ⟨φAc - θ, hφA'mem⟩
                (pd_us_relComplex_d_eq_zero ⟨φAc - θ, hφA'mem⟩ hφA'd)))
          (HomologicalComplex.homologyπ_naturality (φ := pdRelComplexEnlarge W h1x) (i := k))
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hnat
      have e2z : (HomologicalComplex.homologyMap (pdRelComplexEnlarge W h2x) k).hom
          ((HomologicalComplex.homologyπ (relComplex ℤ X (pdRelSub W (K₂ ∪ L''))) k).hom
            (cocycleOfK (relComplex ℤ X (pdRelSub W (K₂ ∪ L''))) ⟨φBc - θ, hφB'mem⟩
              (pd_us_relComplex_d_eq_zero ⟨φBc - θ, hφB'mem⟩ hφB'd)))
          = (HomologicalComplex.homologyπ (relComplex ℤ X
              (pdRelSub W ((K₁ ∪ L'') ∪ (K₂ ∪ L'')))) k).hom
            ((HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h2x) k).hom
              (cocycleOfK (relComplex ℤ X (pdRelSub W (K₂ ∪ L''))) ⟨φBc - θ, hφB'mem⟩
                (pd_us_relComplex_d_eq_zero ⟨φBc - θ, hφB'mem⟩ hφB'd))) := by
        have hnat := congrArg (fun (g : (relComplex ℤ X (pdRelSub W (K₂ ∪ L''))).cycles k ⟶
            HomologicalComplex.homology (relComplex ℤ X
              (pdRelSub W ((K₁ ∪ L'') ∪ (K₂ ∪ L'')))) k) => g.hom
              (cocycleOfK (relComplex ℤ X (pdRelSub W (K₂ ∪ L''))) ⟨φBc - θ, hφB'mem⟩
                (pd_us_relComplex_d_eq_zero ⟨φBc - θ, hφB'mem⟩ hφB'd)))
          (HomologicalComplex.homologyπ_naturality (φ := pdRelComplexEnlarge W h2x) (i := k))
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hnat
      have hseq : (HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h0x) k).hom z
          - ((HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h1x) k).hom
              (cocycleOfK (relComplex ℤ X (pdRelSub W (K₁ ∪ L''))) ⟨φAc - θ, hφA'mem⟩
                (pd_us_relComplex_d_eq_zero ⟨φAc - θ, hφA'mem⟩ hφA'd))
            - (HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h2x) k).hom
              (cocycleOfK (relComplex ℤ X (pdRelSub W (K₂ ∪ L''))) ⟨φBc - θ, hφB'mem⟩
                (pd_us_relComplex_d_eq_zero ⟨φBc - θ, hφB'mem⟩ hφB'd))) = 0 := by
        apply pd_us_cycles_eq_of_iCycles_eq
        rw [map_sub, map_sub, map_zero]
        apply Subtype.ext
        show ((((relComplex ℤ X (pdRelSub W ((K₁ ∪ L'') ∪ (K₂ ∪ L'')))).iCycles k).hom)
              ((HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h0x) k).hom z)).1
            - (((((relComplex ℤ X (pdRelSub W ((K₁ ∪ L'') ∪ (K₂ ∪ L'')))).iCycles k).hom)
              ((HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h1x) k).hom
                (cocycleOfK (relComplex ℤ X (pdRelSub W (K₁ ∪ L''))) ⟨φAc - θ, hφA'mem⟩
                  (pd_us_relComplex_d_eq_zero ⟨φAc - θ, hφA'mem⟩ hφA'd)))).1
            - ((((relComplex ℤ X (pdRelSub W ((K₁ ∪ L'') ∪ (K₂ ∪ L'')))).iCycles k).hom)
              ((HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h2x) k).hom
                (cocycleOfK (relComplex ℤ X (pdRelSub W (K₂ ∪ L''))) ⟨φBc - θ, hφB'mem⟩
                  (pd_us_relComplex_d_eq_zero ⟨φBc - θ, hφB'mem⟩ hφB'd)))).1) = 0
        rw [pd_us_pdRelComplexEnlarge_iCycles_coe h0x z,
          pd_us_pdRelComplexEnlarge_iCycles_coe h1x _,
          pd_us_pdRelComplexEnlarge_iCycles_coe h2x _,
          iCycles_cocycleOfK, iCycles_cocycleOfK, hdec]
        change (φAc - φBc) - ((φAc - θ) - (φBc - θ)) = 0
        abel_nf
      have hseq' : (HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h0x) k).hom z
          = (HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h1x) k).hom
              (cocycleOfK (relComplex ℤ X (pdRelSub W (K₁ ∪ L''))) ⟨φAc - θ, hφA'mem⟩
                (pd_us_relComplex_d_eq_zero ⟨φAc - θ, hφA'mem⟩ hφA'd))
            - (HomologicalComplex.cyclesMap (pdRelComplexEnlarge W h2x) k).hom
              (cocycleOfK (relComplex ℤ X (pdRelSub W (K₂ ∪ L''))) ⟨φBc - θ, hφB'mem⟩
                (pd_us_relComplex_d_eq_zero ⟨φBc - θ, hφB'mem⟩ hφB'd)) :=
        sub_eq_zero.mp hseq
      rw [e0z, e1z, e2z, hseq', map_sub]
    exact key

end

end Work.Cohomology
