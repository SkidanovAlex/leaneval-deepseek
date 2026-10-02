import Mathlib
import Submission.Work.Serre.MVShift.cupRelChainHomology
import Submission.Work.Serre.MVShift.shKZeroRat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The homology of the honest cup `ψ ↦ ψ ⌣ t`, including the boundary degree

`Work.Serre.cupRelChain X A n₀ t ht` is the honest chain map `ψ ↦ ψ ⌣ t` from the absolute
cochains of `X` (the relative complex of the pair `(X,∅)`) to the relative cochains of `(X,A)`,
shifted by `n₀`.  This file identifies its effect on cohomology in *all* degrees:

* in the interior degrees `j ≥ 1`, read through the shift isomorphism `shK_homologyIso`
  (`Work.Serre.MVShift.cupRelChainHomology`);
* in degree `0`, read through the boundary comparison `shK_homologyZero`
  (`Work.Serre.MVShift.shK_homologyZero`, whose `k = 0` case of `shK_cyclesIso` has to replace
  the isomorphism of the interior).

In both cases the answer is the mixed cup product with the class of `t`, after the forgetful map
`relToAbs ℚ ∅` from the relative cohomology of `(X,∅)` to the absolute cohomology of `X`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace Work.Serre.MVShift

noncomputable section

open Work.Cohomology

/-! ## The element formula for the boundary comparison of the shift -/

/-- The element formula for `shK_homologyZero` on the homology class of a cycle: the boundary
comparison `(shK L n).homology 0 ⟶ L.homology (0+n)` sends the class of the `0`-cycle
`cyclesMap φ 0 z` to the class of the cocycle `u = φ z`. -/
theorem shK_homologyZero_apply_cyclesMap {K L : CochainComplex (ModuleCat ℚ) ℕ} (n : ℕ)
    (φ : K ⟶ shK L n) (z : ↥(HomologicalComplex.cycles K 0))
    (u : L.X (0 + n)) (hu : u = (φ.f 0).hom ((HomologicalComplex.iCycles K 0) z))
    (hu' : (L.d (0 + n) ((0 + n) + 1)).hom u = 0) :
    (shK_homologyZero L n)
        ((shK L n).homologyπ 0 (HomologicalComplex.cyclesMap φ 0 z))
      = (L.homologyπ (0 + n)) (Work.Cohomology.cocycleOfK L u hu') := by
  have key := congrArg (fun (g : (shK L n).cycles 0 ⟶ L.homology (0 + n)) =>
      g (HomologicalComplex.cyclesMap φ 0 z))
    (shK_homologyZero_spec' L n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at key
  refine key.trans ?_
  have hcz : (shK_cyclesIso L n 0).hom (HomologicalComplex.cyclesMap φ 0 z)
      = Work.Cohomology.cocycleOfK L u hu' :=
    shK_cyclesIso_cyclesMap n 0 φ z u hu hu'
  exact congrArg (fun x => (L.homologyπ (0 + n)) x) hcz

/-! ## The main theorem, in degree zero -/

/-- **The induced map on cohomology of the honest cup, in degree `0`.** -/
theorem cupRelChainHomologyZero (X : TopCat) (A : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀)
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) :
    CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap (Work.Serre.cupRelChain X A n₀ t ht) 0)
        (shK_homologyZero (Work.Cohomology.relComplex ℚ X A) n₀)
      = CategoryTheory.CategoryStruct.comp (Work.Thom.relToAbs ℚ (∅ : Set X) 0)
          (ModuleCat.ofHom ((Work.Thom.mixedCupC ℚ A 0 n₀).flip
            (Work.Cohomology.relClassOf ℚ X A t ht))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, ha, rfl⟩ := Work.Cohomology.exists_relClassOf ℚ X (∅ : Set X) 0 x
  have hda : Work.Cohomology.cochainDiff ℚ (TopCat.toSSet.obj X) a.1 = 0 :=
    Work.Cohomology.relClassOf_cochainDiff ℚ (TopCat.of X) (∅ : Set X) a ha
  have ha' : ((Work.Cohomology.relComplex ℚ X (∅ : Set X)).d 0 (0 + 1)).hom a = 0 := by
    rw [Work.Cohomology.relComplex_d_apply]
    exact ha
  have hda' : ((Work.Cohomology.SSetCochainComplex ℚ (TopCat.toSSet.obj X)).d 0 (0 + 1)).hom
      (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj X) 0 from a.1) = 0 := by
    rw [Work.Cohomology.SSetCochainComplex_d_hom]
    exact hda
  have ht' : ((Work.Cohomology.relComplex ℚ X A).d n₀ (n₀ + 1)).hom t = 0 := by
    rw [Work.Cohomology.relComplex_d_apply]
    exact ht
  let z : (Work.Cohomology.relComplex ℚ X (∅ : Set X)).cycles 0 :=
    Work.Cohomology.cocycleOfK (Work.Cohomology.relComplex ℚ X (∅ : Set X)) a ha'
  let u : (Work.Cohomology.relComplex ℚ X A).X (0 + n₀) :=
    Work.Cohomology.mixedRelStar ℚ X A 0 n₀
      (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj X) 0 from a.1) t
  have hu' : ((Work.Cohomology.relComplex ℚ X A).d (0 + n₀) ((0 + n₀) + 1)).hom u = 0 :=
    Work.Cohomology.mstar_cocycle_cochain (Work.Cohomology.mixedLeibniz_mixedRelStar ℚ X A)
      0 n₀ (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj X) 0 from a.1) t hda' ht'
  have hu : u = ((Work.Serre.cupRelChain X A n₀ t ht).f 0).hom
      ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ X (∅ : Set X)) 0) z) := by
    rw [Work.Cohomology.iCycles_cocycleOfK]
    rw [Work.Serre.cupRelChain_f]
    rfl
  have hL : (CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap (Work.Serre.cupRelChain X A n₀ t ht) 0)
        (Work.Serre.MVShift.shK_homologyZero (Work.Cohomology.relComplex ℚ X A) n₀)).hom
      (Work.Cohomology.relClassOf ℚ X (∅ : Set X) a ha)
      = (Work.Cohomology.relComplex ℚ X A).homologyπ (0 + n₀)
          (Work.Cohomology.cocycleOfK (Work.Cohomology.relComplex ℚ X A) u hu') := by
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [Work.Cohomology.relClassOf_eq_homologyπ_cocycleOfK ℚ X (∅ : Set X) a ha ha']
    rw [homologyMap_homologyπ_apply]
    exact shK_homologyZero_apply_cyclesMap n₀
      (Work.Serre.cupRelChain X A n₀ t ht) z u hu hu'
  have hR : (CategoryTheory.CategoryStruct.comp (Work.Thom.relToAbs ℚ (∅ : Set X) 0)
          (ModuleCat.ofHom ((Work.Thom.mixedCupC ℚ A 0 n₀).flip
            (Work.Cohomology.relClassOf ℚ X A t ht)))).hom
      (Work.Cohomology.relClassOf ℚ X (∅ : Set X) a ha)
      = (Work.Cohomology.relComplex ℚ X A).homologyπ (0 + n₀)
          (Work.Cohomology.cocycleOfK (Work.Cohomology.relComplex ℚ X A) u hu') := by
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.flip_apply]
    refine (congrArg (fun y => (Work.Thom.mixedCupC ℚ A 0 n₀) y
        (Work.Cohomology.relClassOf ℚ X A t ht))
      (Work.Cohomology.relIncl_homologyMap_relClassOf ℚ (TopCat.of X) (∅ : Set X) a ha)).trans ?_
    obtain ⟨hmem, hcoc, hcup⟩ := (Classical.choose_spec
      (Work.Cohomology.mixedRelCupH ℚ (TopCat.of X) A)) 0 n₀
      (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj X) 0 from a.1) t hda ht
    refine hcup.trans ?_
    have hu'' : ((Work.Cohomology.relComplex ℚ X A).d (0 + n₀) ((0 + n₀) + 1)).hom
        (⟨Work.Cohomology.cup ℚ (TopCat.toSSet.obj X)
            (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj X) 0 from a.1) t.1,
          hmem⟩ : (Work.Cohomology.relComplex ℚ X A).X (0 + n₀)) = 0 := by
      rw [Work.Cohomology.relComplex_d_apply]
      exact hcoc
    refine (Work.Cohomology.relClassOf_eq_homologyπ_cocycleOfK ℚ X A
      (⟨Work.Cohomology.cup ℚ (TopCat.toSSet.obj X)
        (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj X) 0 from a.1) t.1, hmem⟩ :
          (Work.Cohomology.relComplex ℚ X A).X (0 + n₀)) hcoc hu'').trans ?_
    rfl
  rw [hL, hR]

/-! ## The assembled statement -/

theorem cupRelChain_homology (Y : TopCat) (B : Set Y) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ Y B n₀)
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
              (Work.Cohomology.relClassOf ℚ Y B t ht)))) :=
  ⟨fun k hk => cupRelChainHomology Y B n₀ t ht k hk,
   cupRelChainHomologyZero Y B n₀ t ht⟩

end

end Work.Serre.MVShift
