import Mathlib
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Milnor.collar_homotopyEquiv_Mk
import Submission.Work.Milnor.mkToVkRangeHomeomorph
import Submission.Work.Milnor.cohomology_Vk
import Submission.Work.Cohomology.homotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The inclusion of the sphere bundle into the collar is a cohomology isomorphism

`Work.Milnor.collar k = {p : Vk k | 1/2 < fibreNormFun k p}` is an open neighbourhood of the unit
sphere bundle `Mk k`, and `Work.Milnor.mkToVkFun k : Mk k → Vk k` embeds `Mk k` as the subspace
`Set.range (mkToVkFun k) ⊆ collar k`.  This file shows that the resulting inclusion of subspaces

`Set.range (mkToVkFun k) ↪ collar k`

induces an isomorphism on singular cohomology with `ℤ` coefficients.

The proof factors the inclusion through the sphere bundle:

`Mk k --mkToVkRange--> Set.range (mkToVkFun k) --incl--> collar k`

where the first map is a homeomorphism (`Work.Milnor.mkToVkRangeHomeomorph`) and the composite is
the collar inclusion `collarPhi k = mkToVkFun k` (`Work.Milnor.collarPhi`).  Both `mkToVkRange`
(homeomorphism) and `collarPhi` (part of the homotopy equivalence `collar ≃ Mk k` of
`Submission.Work.Milnor.CollarHomotopy`) induce isomorphisms on cohomology, so the middle arrow
does too, by two-out-of-three for the composite
`incl ≫ mkToVkRangeHomeomorph = collarPhi`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

/-- The sphere bundle `Mk k` as an object of `TopCat`. -/
abbrev collarInclMk (k : ℤ) : TopCat := TopCat.of (Submission.Milnor.Mk k)

/-- The image of `mkToVkFun k`, as an object of `TopCat`. -/
abbrev collarInclRange (k : ℤ) : TopCat :=
  TopCat.of ↥(Set.range (Work.Milnor.mkToVkFun k))

/-- The collar of the disc bundle, as an object of `TopCat`. -/
abbrev collarInclCollar (k : ℤ) : TopCat := TopCat.of ↥(Work.Milnor.collar k)

/-- The homeomorphism `Mk k → Set.range (mkToVkFun k)` as a morphism of `TopCat`. -/
abbrev mkToVkRangeTop (k : ℤ) : collarInclMk k ⟶ collarInclRange k :=
  TopCat.ofHom (⟨Work.Milnor.mkToVkRange k, Work.Milnor.continuous_mkToVkRange k⟩ :
    C(Submission.Milnor.Mk k, ↥(Set.range (Work.Milnor.mkToVkFun k))))

/-- The inverse `Set.range (mkToVkFun k) → Mk k` as a morphism of `TopCat`. -/
abbrev vkRangeToMkTop (k : ℤ) : collarInclRange k ⟶ collarInclMk k :=
  TopCat.ofHom (⟨Work.Milnor.vkRangeToMk k, Work.Milnor.continuous_vkRangeToMk k⟩ :
    C(↥(Set.range (Work.Milnor.mkToVkFun k)), Submission.Milnor.Mk k))

/-- The collar inclusion `Mk k → collar k` as a morphism of `TopCat`. -/
abbrev collarPhiTop (k : ℤ) : collarInclMk k ⟶ collarInclCollar k :=
  TopCat.ofHom (Work.Milnor.collarPhi k)

/-- The normalisation `collar k → Mk k` as a morphism of `TopCat`. -/
abbrev collarPsiTop (k : ℤ) : collarInclCollar k ⟶ collarInclMk k :=
  TopCat.ofHom (Work.Milnor.collarPsi k)

/-- The inclusion `Set.range (mkToVkFun k) → collar k` of subspaces of `Vk k`, as a morphism of
`TopCat`. -/
abbrev collarInclTop (k : ℤ)
    (h : ∀ x ∈ Set.range (Work.Milnor.mkToVkFun k),
      (𝟙 (TopCat.of (Submission.Milnor.Vk k))) x ∈ Work.Milnor.collar k) :
    collarInclRange k ⟶ collarInclCollar k :=
  relMapSub (Set.range (Work.Milnor.mkToVkFun k)) (Work.Milnor.collar k)
    (𝟙 (TopCat.of (Submission.Milnor.Vk k))) h

theorem mkToVkRangeTop_vkRangeToMkTop (k : ℤ) :
    (mkToVkRangeTop k ≫ vkRangeToMkTop k : collarInclMk k ⟶ collarInclMk k) =
      𝟙 (collarInclMk k) := by
  apply TopCat.ext
  intro z
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply, TopCat.hom_id, ContinuousMap.id_apply]
  exact Work.Milnor.vkRangeToMk_mkToVkRange k z

theorem vkRangeToMkTop_mkToVkRangeTop (k : ℤ) :
    (vkRangeToMkTop k ≫ mkToVkRangeTop k : collarInclRange k ⟶ collarInclRange k) =
      𝟙 (collarInclRange k) := by
  apply TopCat.ext
  intro p
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply, TopCat.hom_id, ContinuousMap.id_apply]
  exact Work.Milnor.mkToVkRange_vkRangeToMk k p

theorem collarPhiTop_collarPsiTop (k : ℤ) :
    (collarPhiTop k ≫ collarPsiTop k : collarInclMk k ⟶ collarInclMk k) =
      𝟙 (collarInclMk k) := by
  apply TopCat.ext
  intro z
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply, TopCat.hom_id, ContinuousMap.id_apply]
  exact ContinuousMap.congr_fun (Work.Milnor.collarPsi_collarPhi k) z

/-- `collarPsi k` is a homotopy inverse to `collarPhi k`: the composite is homotopic to the
identity of the collar by the straight-line deformation `Work.Milnor.collarHomotopy`. -/
def collarPsiTop_collarPhiTop (k : ℤ) :
    TopCat.Homotopy (collarPsiTop k ≫ collarPhiTop k) (𝟙 (collarInclCollar k)) :=
  Work.Milnor.collarHomotopy k

/-- The inclusion of the range of `mkToVkFun k` into the collar factors the collar inclusion:
`mkToVkRange ≫ incl = collarPhi`. -/
theorem mkToVkRangeTop_collarInclTop (k : ℤ)
    (h : ∀ x ∈ Set.range (Work.Milnor.mkToVkFun k),
      (𝟙 (TopCat.of (Submission.Milnor.Vk k))) x ∈ Work.Milnor.collar k) :
    (mkToVkRangeTop k ≫ collarInclTop k h : collarInclMk k ⟶ collarInclCollar k) =
      collarPhiTop k := by
  apply TopCat.ext
  intro z
  apply Subtype.ext
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply]
  rfl

/-- **The inclusion `Set.range (mkToVkFun k) ↪ collar k` induces an isomorphism on singular
cohomology.** -/
theorem collarInclCohomologyIsIso_aux (k : ℤ)
    (h : ∀ x ∈ Set.range (Work.Milnor.mkToVkFun k),
      (𝟙 (TopCat.of (Submission.Milnor.Vk k))) x ∈ Work.Milnor.collar k)
    (n : ℕ) :
    IsIso (singularCohomologyMap ℤ (collarInclRange k) (collarInclCollar k)
      (collarInclTop k h) n) := by
  -- the two "known" isomorphisms
  haveI hiso_mk : IsIso (singularCohomologyMap ℤ (collarInclMk k) (collarInclRange k)
      (mkToVkRangeTop k) n) :=
    homotopyEquiv ℤ (collarInclMk k) (collarInclRange k) (mkToVkRangeTop k) (vkRangeToMkTop k)
      (by rw [mkToVkRangeTop_vkRangeToMkTop]; exact TopCat.Homotopy.refl _)
      (by rw [vkRangeToMkTop_mkToVkRangeTop]; exact TopCat.Homotopy.refl _) n
  haveI hiso_phi : IsIso (singularCohomologyMap ℤ (collarInclMk k) (collarInclCollar k)
      (collarPhiTop k) n) :=
    homotopyEquiv ℤ (collarInclMk k) (collarInclCollar k) (collarPhiTop k) (collarPsiTop k)
      (by rw [collarPhiTop_collarPsiTop]; exact TopCat.Homotopy.refl _)
      (collarPsiTop_collarPhiTop k) n
  -- two-out-of-three for the composite `incl ≫ mkToVkRangeTop = collarPhiTop`
  have hcomp : singularCohomologyMap ℤ (collarInclRange k) (collarInclCollar k)
        (collarInclTop k h) n ≫
      singularCohomologyMap ℤ (collarInclMk k) (collarInclRange k) (mkToVkRangeTop k) n
      = singularCohomologyMap ℤ (collarInclMk k) (collarInclCollar k) (collarPhiTop k) n := by
    rw [← singularCohomologyMap_comp ℤ (mkToVkRangeTop k) (collarInclTop k h) n,
      mkToVkRangeTop_collarInclTop]
  haveI : IsIso (singularCohomologyMap ℤ (collarInclRange k) (collarInclCollar k)
        (collarInclTop k h) n ≫
      singularCohomologyMap ℤ (collarInclMk k) (collarInclRange k) (mkToVkRangeTop k) n) := by
    rw [hcomp]; exact hiso_phi
  exact IsIso.of_isIso_comp_right
    (singularCohomologyMap ℤ (collarInclRange k) (collarInclCollar k) (collarInclTop k h) n)
    (singularCohomologyMap ℤ (collarInclMk k) (collarInclRange k) (mkToVkRangeTop k) n)

end

theorem collarInclCohomologyIsIso (h : ∀ x ∈ Set.range (Work.Milnor.mkToVkFun (-2)), (CategoryTheory.CategoryStruct.id (TopCat.of (Submission.Milnor.Vk (-2)))) x ∈ Work.Milnor.collar (-2)) (n : ℕ) : CategoryTheory.IsIso (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥(Set.range (Work.Milnor.mkToVkFun (-2)))) (TopCat.of ↥(Work.Milnor.collar (-2))) (Work.Cohomology.relMapSub (Set.range (Work.Milnor.mkToVkFun (-2))) (Work.Milnor.collar (-2)) (CategoryTheory.CategoryStruct.id (TopCat.of (Submission.Milnor.Vk (-2)))) h) n) := by
  exact collarInclCohomologyIsIso_aux (-2) h n

end Work.Cohomology
