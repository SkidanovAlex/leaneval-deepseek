import Mathlib
import Submission.Work.Serre.mvDeltaAuxDefs

/-!
# The homology map of the honest cup chain map with a relative cocycle

This file proves `Work.Serre.mvDeltaAuxCupHom`: for a space `Y`, a subset `B ⊆ Y` and a relative
cocycle `t ∈ C^{n₀}(Y,B;ℚ)`, the honest cup chain map `ψ ↦ ψ ⌣ t`
(`Work.Serre.cupRelChain Y B n₀ t ht : C^*(Y,∅) ⟶ shK (C^*(Y,B)) n₀`) induces on cohomology the
mixed cup product with the class of `t`, after forgetting that the source is the *relative* complex
of the pair `(Y,∅)`:

  `H(cupRelChain) k ≫ shK_homologyIso = relToAbs_∅ k ≫ (· ⌣ [t])`

in every degree `k ≥ 1`, and the analogous statement at `k = 0` with `shK_homologyZero`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace Work.Serre

noncomputable section

open Work.Cohomology

/-! ## The shift comparison, on cycles and on homology -/

/-- The comparison `shK_homologyIso` of the degree shift, read on the homology of the shift. -/
theorem shK_homologyπ_shK_homologyIso (D : CochainComplex (ModuleCat ℚ) ℕ) (n k : ℕ)
    (hk : 1 ≤ k) :
    HomologicalComplex.homologyπ (MVShift.shK D n) k ≫ (MVShift.shK_homologyIso D n k hk).hom
      = (MVShift.shK_cyclesIso D n k).hom ≫ HomologicalComplex.homologyπ D (k + n) := by
  simp only [MVShift.shK_homologyIso, MVShift.shK_cyclesIso,
    HomologicalComplex.homologyπ_restrictionHomologyIso_hom]

/-- **The element formula for the cycles comparison of the shift.**  If `z` is a cycle of `K` in
degree `k` and `u` is the image of `z` under `φ` in degree `k` (an element of `L.X (k+n)`), then the
comparison `shK_cyclesIso` sends the cycle `cyclesMap φ k z` of the shift to the cycle associated
with the cocycle `u`. -/
theorem shK_cyclesIso_cyclesMap {K L : CochainComplex (ModuleCat ℚ) ℕ} (n k : ℕ)
    (φ : K ⟶ MVShift.shK L n) (z : ↥(HomologicalComplex.cycles K k))
    (u : ↥(L.X (k + n))) (hu : u = (φ.f k).hom ((HomologicalComplex.iCycles K k) z))
    (hu' : (L.d (k + n) ((k + n) + 1)).hom u = 0) :
    (MVShift.shK_cyclesIso L n k).hom (HomologicalComplex.cyclesMap φ k z)
      = Work.Cohomology.cocycleOfK L u hu' := by
  have h0 : (MVShift.shK_cyclesIso L n k).hom ≫ (HomologicalComplex.iCycles L (k + n))
      = (HomologicalComplex.iCycles (MVShift.shK L n) k) := by
    simp only [MVShift.shK_cyclesIso, HomologicalComplex.restrictionCyclesIso_hom_iCycles]
    simp only [HomologicalComplex.restrictionXIso, eqToIso.hom, eqToHom_refl]
    simp
  have key : (HomologicalComplex.iCycles L (k + n))
        ((MVShift.shK_cyclesIso L n k).hom (HomologicalComplex.cyclesMap φ k z))
      = (φ.f k).hom ((HomologicalComplex.iCycles K k) z) := by
    have hh0 := congrArg (fun (g : (MVShift.shK L n).cycles k ⟶ L.X (k + n)) =>
      g (HomologicalComplex.cyclesMap φ k z)) h0
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh0
    have hh1 := congrArg (fun (g : (HomologicalComplex.cycles K k) ⟶
      (MVShift.shK L n).X k) => g z) (HomologicalComplex.cyclesMap_i φ k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh1
    exact hh0.trans hh1
  apply Work.Cohomology.iCycles_injective_K L (k + n)
  refine key.trans ?_
  have hb : (HomologicalComplex.iCycles L (k + n)) (Work.Cohomology.cocycleOfK L u hu') = u :=
    Work.Cohomology.iCycles_cocycleOfK L u hu'
  exact hu.symm.trans hb.symm

/-- The element formula for `shK_homologyIso` on the homology class of a cycle. -/
theorem shK_homologyIso_apply_cyclesMap {K L : CochainComplex (ModuleCat ℚ) ℕ} (n k : ℕ)
    (hk : 1 ≤ k) (φ : K ⟶ MVShift.shK L n) (z : ↥(HomologicalComplex.cycles K k))
    (u : ↥(L.X (k + n))) (hu : u = (φ.f k).hom ((HomologicalComplex.iCycles K k) z))
    (hu' : (L.d (k + n) ((k + n) + 1)).hom u = 0) :
    (MVShift.shK_homologyIso L n k hk).hom
        ((MVShift.shK L n).homologyπ k (HomologicalComplex.cyclesMap φ k z))
      = (L.homologyπ (k + n)) (Work.Cohomology.cocycleOfK L u hu') := by
  have key := congrArg (fun (g : (MVShift.shK L n).cycles k ⟶ L.homology (k + n)) =>
      g (HomologicalComplex.cyclesMap φ k z))
    (shK_homologyπ_shK_homologyIso L n k hk)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at key
  refine key.trans ?_
  exact congrArg (fun x => (L.homologyπ (k + n)) x)
    (shK_cyclesIso_cyclesMap n k φ z u hu hu')

/-- The element formula for `shK_homologyZero` (the `k = 0` boundary) on the homology class of a
cycle. -/
theorem shK_homologyZero_apply_cyclesMap {K L : CochainComplex (ModuleCat ℚ) ℕ} (n : ℕ)
    (φ : K ⟶ MVShift.shK L n) (z : ↥(HomologicalComplex.cycles K 0))
    (u : ↥(L.X (0 + n))) (hu : u = (φ.f 0).hom ((HomologicalComplex.iCycles K 0) z))
    (hu' : (L.d (0 + n) ((0 + n) + 1)).hom u = 0) :
    (MVShift.shK_homologyZero L n)
        ((MVShift.shK L n).homologyπ 0 (HomologicalComplex.cyclesMap φ 0 z))
      = (L.homologyπ (0 + n)) (Work.Cohomology.cocycleOfK L u hu') := by
  have key := congrArg (fun (g : (MVShift.shK L n).cycles 0 ⟶ L.homology (0 + n)) =>
      g (HomologicalComplex.cyclesMap φ 0 z))
    (MVShift.shK_homologyZero_spec L n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at key
  refine key.trans ?_
  have hcz : (MVShift.shK_cyclesZeroTo L n) (HomologicalComplex.cyclesMap φ 0 z)
      = Work.Cohomology.cocycleOfK L u hu' := by
    rw [MVShift.shK_cyclesZeroTo_eq]
    exact shK_cyclesIso_cyclesMap n 0 φ z u hu hu'
  exact congrArg (fun x => (L.homologyπ (0 + n)) x) hcz

/-- The naturality of `homologyMap` on the homology class of a cycle. -/
theorem homologyMap_homologyπ_apply {K L : CochainComplex (ModuleCat ℚ) ℕ} (φ : K ⟶ L) (k : ℕ)
    (z : ↥(HomologicalComplex.cycles K k)) :
    ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ k)
        (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K k) z)
      = ModuleCat.Hom.hom (HomologicalComplex.homologyπ L k)
          (HomologicalComplex.cyclesMap φ k z) := by
  have h := congrArg (fun (g : HomologicalComplex.cycles K k ⟶ L.homology k) =>
      ModuleCat.Hom.hom g z)
    (HomologicalComplex.homologyπ_naturality φ k)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-! ## The relative complex of the pair `(Y,∅)` -/

/-- A cycle of `C^*(Y,∅)` has vanishing differential, read on the underlying cochain. -/
theorem cochainDiff_iCycles_relComplex_empty (Y : TopCat) (k : ℕ)
    (z : ↥(HomologicalComplex.cycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k)) :
    Work.Cohomology.cochainDiff ℚ (TopCat.toSSet.obj Y)
      ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k) z).1 = 0 := by
  have hz := Work.Cohomology.iCycles_d_apply_K (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k z
  rw [Work.Cohomology.relComplex_d_apply] at hz
  have hz2 := congrArg Subtype.val hz
  rw [Submodule.coe_zero, Work.Cohomology.relDiffLM_coe,
      Work.Cohomology.singularCochain_d_apply] at hz2
  exact hz2

/-- The forgetful map `H^k(Y,∅) → H^k(Y)`, on the homology class of a cycle. -/
theorem relIncl_empty_apply_cycles (Y : TopCat) (k : ℕ)
    (z : ↥(HomologicalComplex.cycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k))
    (h : Work.Cohomology.cochainDiff ℚ (TopCat.toSSet.obj Y)
      ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k) z).1 = 0) :
    ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl ℚ Y (∅ : Set Y)) k)
        (ModuleCat.Hom.hom
          (HomologicalComplex.homologyπ (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k) z)
      = Work.Cohomology.cohomologyClassOf ℚ (TopCat.toSSet.obj Y)
          ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k) z).1 h := by
  rw [homologyMap_homologyπ_apply]
  have hcyc : HomologicalComplex.cyclesMap (Work.Cohomology.relIncl ℚ Y (∅ : Set Y)) k z
      = Work.Cohomology.cocycleOf ℚ (TopCat.toSSet.obj Y)
          ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k) z).1 h := by
    apply Work.Cohomology.iCycles_injective ℚ (TopCat.toSSet.obj Y) k
    have hh0 := congrArg (fun (g : (HomologicalComplex.cycles
          (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k) ⟶
          (Work.Cohomology.SSetCochainComplex ℚ (TopCat.toSSet.obj Y)).X k) => g z)
      (HomologicalComplex.cyclesMap_i (Work.Cohomology.relIncl ℚ Y (∅ : Set Y)) k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh0
    have ha : ((Work.Cohomology.relIncl ℚ Y (∅ : Set Y)).f k).hom
        ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k) z)
        = ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k) z).1 := by
      rw [Work.Cohomology.relIncl_f, ModuleCat.hom_ofHom]
      rfl
    have hb : (HomologicalComplex.iCycles
          (Work.Cohomology.SSetCochainComplex ℚ (TopCat.toSSet.obj Y)) k)
          (Work.Cohomology.cocycleOf ℚ (TopCat.toSSet.obj Y)
            ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k) z).1 h)
        = ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k) z).1 :=
      Work.Cohomology.iCycles_cocycleOf ℚ (TopCat.toSSet.obj Y) _ h
    exact hh0.trans (ha.trans hb.symm)
  rw [hcyc]
  rfl

/-! ## The computation rule for the rational mixed cup product -/

/-- The computation rule for the rational mixed cup product `Work.Thom.mixedCupC`, on the classes
of a cocycle and a relative cocycle. -/
theorem mixedCupC_apply_rat (Y : TopCat) (B : Set Y) (m n : ℕ)
    (a : Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj Y) m)
    (b : ↥(Work.Cohomology.relKern ℚ Y B n))
    (ha : Work.Cohomology.cochainDiff ℚ (TopCat.toSSet.obj Y) a = 0)
    (hb : Work.Cohomology.relDiffLM ℚ Y B n b = 0) :
    ∃ (hmem : Work.Cohomology.cup ℚ (TopCat.toSSet.obj Y) a
          (b.1 : Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj Y) n) ∈
        Work.Cohomology.relKern ℚ Y B (m + n)),
      ∃ (h : Work.Cohomology.relDiffLM ℚ Y B (m + n)
            ⟨Work.Cohomology.cup ℚ (TopCat.toSSet.obj Y) a b.1, hmem⟩ = 0),
        Work.Thom.mixedCupC ℚ B m n
            (Work.Cohomology.cohomologyClassOf ℚ (TopCat.toSSet.obj Y) a ha)
            (Work.Cohomology.relClassOf ℚ Y B b hb)
          = Work.Cohomology.relClassOf ℚ Y B
              ⟨Work.Cohomology.cup ℚ (TopCat.toSSet.obj Y) a b.1, hmem⟩ h :=
  (Classical.choose_spec (Work.Cohomology.mixedRelCupH ℚ Y B)) m n a b ha hb

/-! ## The main theorem -/

end

end Work.Serre

namespace Work.Serre

noncomputable section

open Work.Cohomology

theorem mvDeltaAuxCupHom (Y : TopCat) (B : Set Y) (n₀ : ℕ)
    (t : ↥(Work.Cohomology.relKern ℚ Y B n₀))
    (ht : Work.Cohomology.relDiffLM ℚ Y B n₀ t = 0) :
    (∀ (k : ℕ) (hk : 1 ≤ k),
      CategoryTheory.CategoryStruct.comp
          (HomologicalComplex.homologyMap (Work.Serre.cupRelChain Y B n₀ t ht) k)
          (Work.Serre.MVShift.shK_homologyIso (Work.Cohomology.relComplex ℚ Y B) n₀ k hk).hom
        = CategoryTheory.CategoryStruct.comp (Work.Thom.relToAbs ℚ (∅ : Set Y) k)
            (ModuleCat.ofHom ((Work.Thom.mixedCupC ℚ B k n₀).flip
              (Work.Cohomology.relClassOf ℚ Y B t ht))))
    ∧ (CategoryTheory.CategoryStruct.comp
          (HomologicalComplex.homologyMap (Work.Serre.cupRelChain Y B n₀ t ht) 0)
          (Work.Serre.MVShift.shK_homologyZero (Work.Cohomology.relComplex ℚ Y B) n₀)
        = CategoryTheory.CategoryStruct.comp (Work.Thom.relToAbs ℚ (∅ : Set Y) 0)
            (ModuleCat.ofHom ((Work.Thom.mixedCupC ℚ B 0 n₀).flip
              (Work.Cohomology.relClassOf ℚ Y B t ht)))) := by
  have ht' : (ModuleCat.Hom.hom ((Work.Cohomology.relComplex ℚ Y B).d n₀ (n₀ + 1))) t = 0 := by
    rw [Work.Cohomology.relComplex_d_apply]
    exact ht
  constructor
  · intro k hk
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
      (HomologicalComplex.homologyπ (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k)).mp
      inferInstance x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.flip_apply,
      ModuleCat.hom_ofHom]
    have hcoc : Work.Cohomology.cochainDiff ℚ (TopCat.toSSet.obj Y)
        ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k) z).1 = 0 :=
      cochainDiff_iCycles_relComplex_empty Y k z
    set u : ↥((Work.Cohomology.relComplex ℚ Y B).X (k + n₀)) :=
      (Work.Cohomology.mixedRelStar ℚ Y B k n₀)
        ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k) z).1 t
      with hu_def
    have hu : u = ((Work.Serre.cupRelChain Y B n₀ t ht).f k).hom
        ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k) z) := by
      rw [hu_def, Work.Serre.cupRelChain_f, ModuleCat.hom_ofHom]
      rfl
    have hu' : (ModuleCat.Hom.hom
        ((Work.Cohomology.relComplex ℚ Y B).d (k + n₀) ((k + n₀) + 1))) u = 0 := by
      rw [hu_def]
      refine Work.Cohomology.mstar_cocycle_cochain
        (Work.Cohomology.mixedLeibniz_mixedRelStar ℚ Y B) k n₀ _ t ?_ ht'
      rw [Work.Cohomology.SSetCochainComplex_d_hom]
      exact hcoc
    have hue : Work.Cohomology.relDiffLM ℚ Y B (k + n₀) u = 0 := by
      rw [← Work.Cohomology.relComplex_d_apply]
      exact hu'
    have hL : (ModuleCat.Hom.hom (Work.Serre.MVShift.shK_homologyIso
          (Work.Cohomology.relComplex ℚ Y B) n₀ k hk).hom)
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (Work.Serre.cupRelChain Y B n₀ t ht) k))
            ((ConcreteCategory.hom (HomologicalComplex.homologyπ
              (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k)) z))
        = Work.Cohomology.relClassOf ℚ Y B u hue := by
      refine (congrArg (fun y => (ModuleCat.Hom.hom (Work.Serre.MVShift.shK_homologyIso
          (Work.Cohomology.relComplex ℚ Y B) n₀ k hk).hom) y)
        (homologyMap_homologyπ_apply (Work.Serre.cupRelChain Y B n₀ t ht) k z)).trans ?_
      refine (shK_homologyIso_apply_cyclesMap n₀ k hk
        (Work.Serre.cupRelChain Y B n₀ t ht) z u hu hu').trans ?_
      exact (Work.Cohomology.relClassOf_eq_homologyπ_cocycleOfK ℚ Y B u hue hu').symm
    have hR : (ModuleCat.Hom.hom (Work.Thom.relToAbs ℚ (∅ : Set Y) k))
          ((ConcreteCategory.hom (HomologicalComplex.homologyπ
            (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k)) z)
        = Work.Cohomology.cohomologyClassOf ℚ (TopCat.toSSet.obj Y)
            ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k) z).1
            hcoc :=
      relIncl_empty_apply_cycles Y k z hcoc
    obtain ⟨hmem, hcupcoc, hcup⟩ := mixedCupC_apply_rat Y B k n₀
      ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) k) z).1 t hcoc ht
    rw [hL, hR, hcup]
    refine Work.Cohomology.relClassOf_congr ℚ Y B hue hcupcoc (Subtype.ext ?_)
    rw [hu_def, Work.Cohomology.mixedRelStar_coe]
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
      (HomologicalComplex.homologyπ (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) 0)).mp
      inferInstance x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.flip_apply,
      ModuleCat.hom_ofHom]
    have hcoc : Work.Cohomology.cochainDiff ℚ (TopCat.toSSet.obj Y)
        ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) 0) z).1 = 0 :=
      cochainDiff_iCycles_relComplex_empty Y 0 z
    set u : ↥((Work.Cohomology.relComplex ℚ Y B).X (0 + n₀)) :=
      (Work.Cohomology.mixedRelStar ℚ Y B 0 n₀)
        ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) 0) z).1 t
      with hu_def
    have hu : u = ((Work.Serre.cupRelChain Y B n₀ t ht).f 0).hom
        ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) 0) z) := by
      rw [hu_def, Work.Serre.cupRelChain_f, ModuleCat.hom_ofHom]
      rfl
    have hu' : (ModuleCat.Hom.hom
        ((Work.Cohomology.relComplex ℚ Y B).d (0 + n₀) ((0 + n₀) + 1))) u = 0 := by
      rw [hu_def]
      refine Work.Cohomology.mstar_cocycle_cochain
        (Work.Cohomology.mixedLeibniz_mixedRelStar ℚ Y B) 0 n₀ _ t ?_ ht'
      rw [Work.Cohomology.SSetCochainComplex_d_hom]
      exact hcoc
    have hue : Work.Cohomology.relDiffLM ℚ Y B (0 + n₀) u = 0 := by
      rw [← Work.Cohomology.relComplex_d_apply]
      exact hu'
    have hL : (ModuleCat.Hom.hom (Work.Serre.MVShift.shK_homologyZero
          (Work.Cohomology.relComplex ℚ Y B) n₀))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (Work.Serre.cupRelChain Y B n₀ t ht) 0))
            ((ConcreteCategory.hom (HomologicalComplex.homologyπ
              (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) 0)) z))
        = Work.Cohomology.relClassOf ℚ Y B u hue := by
      refine (congrArg (fun y => (ModuleCat.Hom.hom (Work.Serre.MVShift.shK_homologyZero
          (Work.Cohomology.relComplex ℚ Y B) n₀)) y)
        (homologyMap_homologyπ_apply (Work.Serre.cupRelChain Y B n₀ t ht) 0 z)).trans ?_
      refine (shK_homologyZero_apply_cyclesMap n₀
        (Work.Serre.cupRelChain Y B n₀ t ht) z u hu hu').trans ?_
      exact (Work.Cohomology.relClassOf_eq_homologyπ_cocycleOfK ℚ Y B u hue hu').symm
    have hR : (ModuleCat.Hom.hom (Work.Thom.relToAbs ℚ (∅ : Set Y) 0))
          ((ConcreteCategory.hom (HomologicalComplex.homologyπ
            (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) 0)) z)
        = Work.Cohomology.cohomologyClassOf ℚ (TopCat.toSSet.obj Y)
            ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) 0) z).1
            hcoc :=
      relIncl_empty_apply_cycles Y 0 z hcoc
    obtain ⟨hmem, hcupcoc, hcup⟩ := mixedCupC_apply_rat Y B 0 n₀
      ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ Y (∅ : Set Y)) 0) z).1 t hcoc ht
    rw [hL, hR, hcup]
    refine Work.Cohomology.relClassOf_congr ℚ Y B hue hcupcoc (Subtype.ext ?_)
    rw [hu_def, Work.Cohomology.mixedRelStar_coe]

end

end Work.Serre
