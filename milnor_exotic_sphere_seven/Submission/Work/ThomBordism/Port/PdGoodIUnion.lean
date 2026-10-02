-- Copied verbatim from `Submission.Work.Cohomology.pd_good_iUnion`, with imports re-routed to
-- the clash-free chain (see `Submission/Work/Thom/README.md`, ADDENDUM 16, and
-- `Submission/Work/ThomBordism/README.md`).  The workspace contains two *identical* duplicate
-- modules `Submission.Work.Cohomology.Crux.ovlRestrictionSurjective` and
-- `Submission.Work.Cohomology.Crux.vkCruxRestr`, so a module importing one of them cannot be
-- combined with a module importing the other.  The consumer here (the `Work.ThomBordism`
-- chapter, whose interface imports `ovlRestrictionSurjective`) therefore needs this copy.
-- Nothing else is changed: all declarations keep their original names and proofs.
import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_goodD_incl
-- Re-pointed to the original chain (Islands subproject, 2026): the `Thom/Relocate` copies of
-- the Poincaré-duality chain declared the same names as the `Cohomology/` originals.  The
-- originals are now re-routed (`Crux/vk_transgression_cap_weak.lean` imports the `ovl` copies),
-- so the copies are no longer needed here and the two modules can be imported together.
import Submission.Work.Cohomology.pd_glue2
-- Re-pointed to the original chain (Islands subproject, 2026): the `Thom/Relocate` copies of
-- the Poincaré-duality chain declared the same names as the `Cohomology/` originals.  The
-- originals are now re-routed (`Crux/vk_transgression_cap_weak.lean` imports the `ovl` copies),
-- so the copies are no longer needed here and the two modules can be imported together.
import Submission.Work.Cohomology.capRelAux
import Submission.Work.Cohomology.pdHom_iUnion_kill

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## Auxiliary lemmas -/

/-- A compact subset of an increasing union of open sets lies in one of the open sets. -/
theorem pdIU_compact_subset {M : TopCat} {W : ℕ → Set M} (hWopen : ∀ i, IsOpen (W i))
    (hmono : Monotone W) {K : Set M} (hIsComp : IsCompact K) (hK : K ⊆ ⋃ i, W i) :
    ∃ i, K ⊆ W i := by
  obtain ⟨t, ht⟩ := hIsComp.elim_finite_subcover W hWopen hK
  rcases t.eq_empty_or_nonempty with rfl | hne
  · refine ⟨0, fun x hx => ?_⟩
    simpa using ht hx
  · refine ⟨t.max' hne, fun x hx => ?_⟩
    have h := ht hx
    simp only [Set.mem_iUnion] at h
    obtain ⟨i, hi, hxi⟩ := h
    exact hmono (Finset.le_max' t i hi) hxi

/-- The composite of the inclusions `V ⊆ U ⊆ W` is the inclusion `V ⊆ W`. -/
theorem pdIU_pdIncl_comp {M : TopCat} {V U W : Set M} (hVU : V ⊆ U) (hUW : U ⊆ W) :
    pdIncl U V hVU ≫ pdIncl W U hUW = pdIncl W V (hVU.trans hUW) := by
  ext x
  rfl

/-- The pair map on relative cochains does not depend on the proof that the map of pairs carries
`A₁` into `A₂`. -/
theorem pdIU_relComplexMap_h_congr {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h h' : ∀ x ∈ A₁, f x ∈ A₂) :
    relComplexMap ℤ A₁ A₂ f h = relComplexMap ℤ A₁ A₂ f h' :=
  capRel_relComplexMap_congr ℤ A₁ A₂ rfl h h'

/-- **Functoriality of the restrictions `pdCohMap`**: restricting relative cohomology from `W` to
`V` directly is the same as restricting from `W` to `U` and then from `U` to `V`. -/
theorem pdIU_pdCohMap_comp {M : TopCat} {V U W : Set M} (K : Set M)
    (hVU : V ⊆ U) (hUW : U ⊆ W) (k : ℕ) :
    pdCohMap M Kᶜ W V (hVU.trans hUW) k
      = pdCohMap M Kᶜ W U hUW k ≫ pdCohMap M Kᶜ U V hVU k := by
  rw [pdCohMap, pdCohMap, pdCohMap]
  rw [← HomologicalComplex.homologyMap_comp]
  have h1 := capRel_relComplexMap_comp ℤ (pdRelSub V K) (pdRelSub U K) (pdRelSub W K)
    (pdIncl U V hVU) (pdIncl W U hUW) (fun x hx => hx) (fun x hx => hx)
  exact congrArg (fun g => HomologicalComplex.homologyMap g k) h1

/-- **The restriction commutes with the enlargement of the compact set.** -/
theorem pdIU_pdRelComplexEnlarge_restrict {M : TopCat} {U W : Set M} (hWU : W ⊆ U)
    {K K' : Set M} (hKK' : K ⊆ K') (k : ℕ) :
    pdCohExMap (TopCat.of U) (pdRelSub U K') (pdRelSub U K) (pdRelSub_mono hKK') k
      ≫ pdCohMap M K'ᶜ U W hWU k
    = pdCohMap M Kᶜ U W hWU k
      ≫ pdCohExMap (TopCat.of W) (pdRelSub W K') (pdRelSub W K) (pdRelSub_mono hKK') k := by
  rw [pdCohExMap, pdCohMap, pdCohMap, pdCohExMap]
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  have h1 := capRel_relComplexMap_comp ℤ (pdRelSub W K') (pdRelSub U K') (pdRelSub U K)
    (pdIncl U W hWU) (𝟙 (TopCat.of U)) (fun x hx => hx) (fun x hx => pdRelSub_mono hKK' hx)
  have h2 := capRel_relComplexMap_comp ℤ (pdRelSub W K') (pdRelSub W K) (pdRelSub U K)
    (𝟙 (TopCat.of W)) (pdIncl U W hWU) (fun x hx => pdRelSub_mono hKK' hx) (fun x hx => hx)
  exact (congrArg (fun g => HomologicalComplex.homologyMap g k) h1.symm).trans
    (congrArg (fun g => HomologicalComplex.homologyMap g k) h2)

/-! ## The main theorem -/

theorem pd_good_iUnion {M : TopCat} [T2Space M] {N : ℕ}
    {c : (Work.Cohomology.singularChains ℤ M).homology N}
    (W : ℕ → Set M) (hWopen : ∀ i, IsOpen (W i)) (hmono : Monotone W)
    (hGood : ∀ i, Work.Cohomology.Good N c (W i) (hWopen i)) :
    Work.Cohomology.Good N c (⋃ i, W i) (isOpen_iUnion hWopen) := by
  intro k m hkm
  constructor
  · -- surjectivity
    intro y
    obtain ⟨i, y', hy'⟩ := pdHom_iUnion_lift W hWopen hmono m y
    obtain ⟨K, hKW, hKc, x', hx'⟩ := Good.hit (hGood i) k m hkm y'
    have hKU : K ⊆ (⋃ j, W j : Set M) := hKW.trans (Set.subset_iUnion W i)
    haveI hiso : IsIso (pdCohMap M Kᶜ (⋃ j, W j) (W i) (Set.subset_iUnion W i) k) :=
      pdCohExcision (Set.subset_iUnion W i) (hWopen i) (isOpen_iUnion hWopen) hKW hKc k
    refine ⟨K, hKU, hKc,
      inv (pdCohMap M Kᶜ (⋃ j, W j) (W i) (Set.subset_iUnion W i) k) x', ?_⟩
    have hlift : (HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub (W i) K)
        (pdRelSub (⋃ j, W j) K) (pdIncl (⋃ j, W j) (W i) (Set.subset_iUnion W i))
        (fun x hx => hx)) k)
        (inv (pdCohMap M Kᶜ (⋃ j, W j) (W i) (Set.subset_iUnion W i) k) x') = x' :=
      IsIso.inv_hom_id_apply (pdCohMap M Kᶜ (⋃ j, W j) (W i) (Set.subset_iUnion W i) k) x'
    have hkey := pd_goodD_incl (W := ⋃ j, W j) (V := W i) (Set.subset_iUnion W i)
      (isOpen_iUnion hWopen) (hWopen i) hKW hKU hKc N c k m hkm
      (inv (pdCohMap M Kᶜ (⋃ j, W j) (W i) (Set.subset_iUnion W i) k) x')
    rw [hlift, hx'] at hkey
    exact hkey.symm.trans hy'
  · -- injectivity up to enlargement
    intro K hKU hKc x hx
    obtain ⟨i, hKW⟩ := pdIU_compact_subset hWopen hmono hKc hKU
    haveI hiso : IsIso (pdCohMap M Kᶜ (⋃ j, W j) (W i) (Set.subset_iUnion W i) k) :=
      pdCohExcision (Set.subset_iUnion W i) (hWopen i) (isOpen_iUnion hWopen) hKW hKc k
    have hnat := pd_goodD_incl (W := ⋃ j, W j) (V := W i) (Set.subset_iUnion W i)
      (isOpen_iUnion hWopen) (hWopen i) hKW hKU hKc N c k m hkm x
    have hzi : (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (W i))
        (TopCat.of (⋃ j, W j)) (pdIncl (⋃ j, W j) (W i) (Set.subset_iUnion W i))) m)
        (goodD N c (W i) (hWopen i) K hKW hKc k m hkm
          ((pdCohMap M Kᶜ (⋃ j, W j) (W i) (Set.subset_iUnion W i) k) x)) = 0 := by
      rw [pdCohMap]
      rw [hnat, hx]
    obtain ⟨j, hij, hkillij⟩ := pdHom_iUnion_kill W hWopen hmono m i
      (goodD N c (W i) (hWopen i) K hKW hKc k m hkm
        ((pdCohMap M Kᶜ (⋃ j, W j) (W i) (Set.subset_iUnion W i) k) x)) hzi
    have hKWj : K ⊆ W j := hKW.trans (hmono hij)
    have hcomp := pdIU_pdCohMap_comp (M := M) (V := W i) (U := W j) (W := ⋃ l, W l) K
      (hmono hij) (Set.subset_iUnion W j) k
    have hxi : (HomologicalComplex.homologyMap (relComplexMap ℤ (pdRelSub (W i) K)
        (pdRelSub (W j) K) (pdIncl (W j) (W i) (hmono hij)) (fun x hx => hx)) k)
        ((pdCohMap M Kᶜ (⋃ l, W l) (W j) (Set.subset_iUnion W j) k) x)
        = (pdCohMap M Kᶜ (⋃ l, W l) (W i) (Set.subset_iUnion W i) k) x := by
      show (pdCohMap M Kᶜ (W j) (W i) (hmono hij) k)
          ((pdCohMap M Kᶜ (⋃ l, W l) (W j) (Set.subset_iUnion W j) k) x)
        = (pdCohMap M Kᶜ (⋃ l, W l) (W i) (Set.subset_iUnion W i) k) x
      rw [hcomp, ModuleCat.comp_apply]
    have hnat2 := pd_goodD_incl (W := W j) (V := W i) (hmono hij) (hWopen j) (hWopen i)
      hKW hKWj hKc N c k m hkm
      ((pdCohMap M Kᶜ (⋃ l, W l) (W j) (Set.subset_iUnion W j) k) x)
    have hgoodj : goodD N c (W j) (hWopen j) K hKWj hKc k m hkm
        ((pdCohMap M Kᶜ (⋃ l, W l) (W j) (Set.subset_iUnion W j) k) x) = 0 := by
      rw [← hnat2, hxi]
      exact hkillij
    obtain ⟨K', hKK', hK'Wj, hK'c, hkillK'⟩ :=
      Good.kill (hGood j) k m hkm K hKWj hKc _ hgoodj
    refine ⟨K', hKK', hK'Wj.trans (Set.subset_iUnion W j), hK'c, ?_⟩
    have hsq := pdIU_pdRelComplexEnlarge_restrict (U := ⋃ l, W l) (W := W j)
      (Set.subset_iUnion W j) hKK' k
    have hunit := congrArg (fun g => g x) hsq
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hunit
    haveI hiso' : IsIso (pdCohMap M K'ᶜ (⋃ l, W l) (W j) (Set.subset_iUnion W j) k) :=
      pdCohExcision (Set.subset_iUnion W j) (hWopen j) (isOpen_iUnion hWopen) hK'Wj hK'c k
    have hfinal : (pdCohExMap (TopCat.of (⋃ l, W l)) (pdRelSub (⋃ l, W l) K')
        (pdRelSub (⋃ l, W l) K) (pdRelSub_mono hKK') k) x = 0 := by
      have hzero : (pdCohMap M K'ᶜ (⋃ l, W l) (W j) (Set.subset_iUnion W j) k)
          ((pdCohExMap (TopCat.of (⋃ l, W l)) (pdRelSub (⋃ l, W l) K')
            (pdRelSub (⋃ l, W l) K) (pdRelSub_mono hKK') k) x) = 0 := by
        rw [hunit]
        exact hkillK'
      calc (pdCohExMap (TopCat.of (⋃ l, W l)) (pdRelSub (⋃ l, W l) K')
              (pdRelSub (⋃ l, W l) K) (pdRelSub_mono hKK') k) x
          = inv (pdCohMap M K'ᶜ (⋃ l, W l) (W j) (Set.subset_iUnion W j) k)
              ((pdCohMap M K'ᶜ (⋃ l, W l) (W j) (Set.subset_iUnion W j) k)
                ((pdCohExMap (TopCat.of (⋃ l, W l)) (pdRelSub (⋃ l, W l) K')
                  (pdRelSub (⋃ l, W l) K) (pdRelSub_mono hKK') k) x)) :=
            (IsIso.hom_inv_id_apply _ _).symm
        _ = inv (pdCohMap M K'ᶜ (⋃ l, W l) (W j) (Set.subset_iUnion W j) k) 0 := by
            rw [hzero]
        _ = 0 := map_zero _
    exact hfinal

end

end Work.Cohomology
