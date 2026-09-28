import Mathlib
import Submission.Work.Serre.MVShift.HonestCup
import Submission.Work.Serre.MVShift.ShQ
import Submission.Work.Serre.MVShift.relMapLM_mixedRelStar
import Submission.Work.Cohomology.mixedRelCupH
import Submission.Work.Cohomology.relIncl_relCupH
import Submission.Work.Thom.Cohomology

/-!
# The homology of the honest cup `ψ ↦ ψ ⌣ t`

`Work.Serre.cupRelChain X A n₀ t ht` is the honest chain map `ψ ↦ ψ ⌣ t` from the absolute
cochains of `X` (i.e. the relative complex of the pair `(X,∅)`) to the relative cochains of
`(X,A)`, shifted by `n₀`.  This file identifies its effect on cohomology in the interior degrees
`j ≥ 1`:

  `H(cupRelChain) j ≫ shK_homologyIso = relToAbs_∅ j ≫ (· ⌣ [t])`,

i.e. the induced map `H^j(X;ℚ) → H^{j+n₀}(X,A;ℚ)` is the mixed cup product with the class of the
cocycle `t`.  This is the first clause of `Work.Serre.CupHomStatement`.

The proof works on the class of a relative cocycle `a ∈ C^j(X,∅)`: on the one hand
`H(cupRelChain)` sends it to the class of the relative cocycle `a ⌣ t` (via the element formulae
for `homologyMap`, `cyclesMap` and the shifted homology comparison); on the other hand the
forgetful map sends it to the absolute class of `a`, and the computation rule for the mixed cup
product gives the class of `a ⌣ t` again.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace Work.Serre.MVShift

noncomputable section

open Work.Cohomology

/-! ## Element formulae for the degree shift -/

/-- The comparison `shK_homologyIso` of the degree shift, read on cycles. -/
theorem shK_homologyπ_shK_homologyIso (D : CochainComplex (ModuleCat ℚ) ℕ) (n k : ℕ)
    (hk : 1 ≤ k) :
    HomologicalComplex.homologyπ (shK D n) k ≫ (shK_homologyIso D n k hk).hom
      = (shK_cyclesIso D n k).hom ≫ HomologicalComplex.homologyπ D (k + n) := by
  simp only [shK_homologyIso, shK_cyclesIso,
    HomologicalComplex.homologyπ_restrictionHomologyIso_hom]

/-- **The element formula for the cycles comparison of the shift.**  If `z` is a cycle of `K` in
degree `k` and `u` is the image of `z` under `φ` in degree `k` (an element of `L.X (k+n)`), then the
comparison `shK_cyclesIso` sends the cycle `cyclesMap φ k z` of the shift to the cycle associated
with the cocycle `u`. -/
theorem shK_cyclesIso_cyclesMap {K L : CochainComplex (ModuleCat ℚ) ℕ} (n k : ℕ)
    (φ : K ⟶ shK L n) (z : ↥(HomologicalComplex.cycles K k))
    (u : L.X (k + n)) (hu : u = (φ.f k).hom ((HomologicalComplex.iCycles K k) z))
    (hu' : (L.d (k + n) ((k + n) + 1)).hom u = 0) :
    (shK_cyclesIso L n k).hom (HomologicalComplex.cyclesMap φ k z)
      = Work.Cohomology.cocycleOfK L u hu' := by
  apply Work.Cohomology.iCycles_injective_K L (k + n)
  have h1 : (shK_cyclesIso L n k).hom ≫ (HomologicalComplex.iCycles L (k + n))
      = (shK L n).iCycles k := by
    simp only [shK_cyclesIso, HomologicalComplex.restrictionCyclesIso_hom_iCycles]
    simp only [HomologicalComplex.restrictionXIso, eqToIso.hom, eqToHom_refl]
    simp
  have hc := congrArg (fun (g : (shK L n).cycles k ⟶ L.X (k + n)) =>
      ModuleCat.Hom.hom g (HomologicalComplex.cyclesMap φ k z)) h1
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
  have hc2 := congrArg (fun (g : K.cycles k ⟶ (shK L n).X k) =>
      ModuleCat.Hom.hom g z) (HomologicalComplex.cyclesMap_i φ k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc2
  exact (hc.trans hc2).trans
    (hu.symm.trans (Work.Cohomology.iCycles_cocycleOfK L u hu').symm)

/-- The element formula for `shK_homologyIso` on the homology class of a cycle. -/
theorem shK_homologyIso_apply_cyclesMap {K L : CochainComplex (ModuleCat ℚ) ℕ} (n k : ℕ)
    (hk : 1 ≤ k) (φ : K ⟶ shK L n) (z : ↥(HomologicalComplex.cycles K k))
    (u : L.X (k + n)) (hu : u = (φ.f k).hom ((HomologicalComplex.iCycles K k) z))
    (hu' : (L.d (k + n) ((k + n) + 1)).hom u = 0) :
    (shK_homologyIso L n k hk).hom
        ((shK L n).homologyπ k (HomologicalComplex.cyclesMap φ k z))
      = (L.homologyπ (k + n)) (Work.Cohomology.cocycleOfK L u hu') := by
  have key := congrArg (fun (g : (shK L n).cycles k ⟶ L.homology (k + n)) =>
      g (HomologicalComplex.cyclesMap φ k z))
    (shK_homologyπ_shK_homologyIso L n k hk)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at key
  rw [key, shK_cyclesIso_cyclesMap (L := L) n k φ z u hu hu']

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

/-! ## The main theorem -/

theorem cupRelChainHomology (X : TopCat) (A : Set X) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ X A n₀)
    (ht : Work.Cohomology.relDiffLM ℚ X A n₀ t = 0) (j : ℕ) (hj : 1 ≤ j) :
    CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap (Work.Serre.cupRelChain X A n₀ t ht) j)
        (Work.Serre.MVShift.shK_homologyIso (Work.Cohomology.relComplex ℚ X A) n₀ j hj).hom
      = CategoryTheory.CategoryStruct.comp (Work.Thom.relToAbs ℚ (∅ : Set X) j)
          (ModuleCat.ofHom ((Work.Thom.mixedCupC ℚ A j n₀).flip
            (Work.Cohomology.relClassOf ℚ X A t ht))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, ha, rfl⟩ := Work.Cohomology.exists_relClassOf ℚ X (∅ : Set X) j x
  have hda : Work.Cohomology.cochainDiff ℚ (TopCat.toSSet.obj X) a.1 = 0 :=
    Work.Cohomology.relClassOf_cochainDiff ℚ (TopCat.of X) (∅ : Set X) a ha
  have ha' : ((Work.Cohomology.relComplex ℚ X (∅ : Set X)).d j (j + 1)).hom a = 0 := by
    rw [Work.Cohomology.relComplex_d_apply]
    exact ha
  have hda' : ((Work.Cohomology.SSetCochainComplex ℚ (TopCat.toSSet.obj X)).d j (j + 1)).hom
      (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj X) j from a.1) = 0 := by
    rw [Work.Cohomology.SSetCochainComplex_d_hom]
    exact hda
  have ht' : ((Work.Cohomology.relComplex ℚ X A).d n₀ (n₀ + 1)).hom t = 0 := by
    rw [Work.Cohomology.relComplex_d_apply]
    exact ht
  let z : (Work.Cohomology.relComplex ℚ X (∅ : Set X)).cycles j :=
    Work.Cohomology.cocycleOfK (Work.Cohomology.relComplex ℚ X (∅ : Set X)) a ha'
  let u : (Work.Cohomology.relComplex ℚ X A).X (j + n₀) :=
    Work.Cohomology.mixedRelStar ℚ X A j n₀
      (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj X) j from a.1) t
  have hu' : ((Work.Cohomology.relComplex ℚ X A).d (j + n₀) ((j + n₀) + 1)).hom u = 0 :=
    Work.Cohomology.mstar_cocycle_cochain (Work.Cohomology.mixedLeibniz_mixedRelStar ℚ X A)
      j n₀ (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj X) j from a.1) t hda' ht'
  have hu : u = ((Work.Serre.cupRelChain X A n₀ t ht).f j).hom
      ((HomologicalComplex.iCycles (Work.Cohomology.relComplex ℚ X (∅ : Set X)) j) z) := by
    rw [Work.Cohomology.iCycles_cocycleOfK]
    rw [Work.Serre.cupRelChain_f]
    rfl
  have hL : (CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap (Work.Serre.cupRelChain X A n₀ t ht) j)
        (Work.Serre.MVShift.shK_homologyIso (Work.Cohomology.relComplex ℚ X A) n₀ j hj).hom).hom
      (Work.Cohomology.relClassOf ℚ X (∅ : Set X) a ha)
      = (Work.Cohomology.relComplex ℚ X A).homologyπ (j + n₀)
          (Work.Cohomology.cocycleOfK (Work.Cohomology.relComplex ℚ X A) u hu') := by
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [Work.Cohomology.relClassOf_eq_homologyπ_cocycleOfK ℚ X (∅ : Set X) a ha ha']
    rw [homologyMap_homologyπ_apply]
    exact shK_homologyIso_apply_cyclesMap n₀ j hj
      (Work.Serre.cupRelChain X A n₀ t ht) z u hu hu'
  have hR : (CategoryTheory.CategoryStruct.comp (Work.Thom.relToAbs ℚ (∅ : Set X) j)
          (ModuleCat.ofHom ((Work.Thom.mixedCupC ℚ A j n₀).flip
            (Work.Cohomology.relClassOf ℚ X A t ht)))).hom
      (Work.Cohomology.relClassOf ℚ X (∅ : Set X) a ha)
      = (Work.Cohomology.relComplex ℚ X A).homologyπ (j + n₀)
          (Work.Cohomology.cocycleOfK (Work.Cohomology.relComplex ℚ X A) u hu') := by
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.flip_apply]
    refine (congrArg (fun y => (Work.Thom.mixedCupC ℚ A j n₀) y
        (Work.Cohomology.relClassOf ℚ X A t ht))
      (Work.Cohomology.relIncl_homologyMap_relClassOf ℚ (TopCat.of X) (∅ : Set X) a ha)).trans ?_
    obtain ⟨hmem, hcoc, hcup⟩ := (Classical.choose_spec
      (Work.Cohomology.mixedRelCupH ℚ (TopCat.of X) A)) j n₀
      (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj X) j from a.1) t hda ht
    refine hcup.trans ?_
    have hu'' : ((Work.Cohomology.relComplex ℚ X A).d (j + n₀) ((j + n₀) + 1)).hom
        (⟨Work.Cohomology.cup ℚ (TopCat.toSSet.obj X)
            (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj X) j from a.1) t.1,
          hmem⟩ : (Work.Cohomology.relComplex ℚ X A).X (j + n₀)) = 0 := by
      rw [Work.Cohomology.relComplex_d_apply]
      exact hcoc
    refine (Work.Cohomology.relClassOf_eq_homologyπ_cocycleOfK ℚ X A
      (⟨Work.Cohomology.cup ℚ (TopCat.toSSet.obj X)
        (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj X) j from a.1) t.1, hmem⟩ :
          (Work.Cohomology.relComplex ℚ X A).X (j + n₀)) hcoc hu'').trans ?_
    rfl
  rw [hL, hR]

end

end Work.Serre.MVShift
