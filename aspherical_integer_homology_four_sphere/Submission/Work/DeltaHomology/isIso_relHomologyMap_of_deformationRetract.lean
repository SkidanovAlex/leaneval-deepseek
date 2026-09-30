import Mathlib
import Submission.Work.Homology.Basic
import Submission.Work.Homology.Pairs
import Submission.Work.Homology.Corollaries
import Submission.Work.Homology.DeformationRetractHomology
import Submission.Work.DeltaHomology.GoodPairDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Work.Homology Work.DeltaHomology

noncomputable section

/-! ## The canonical homeomorphism `A ≅ {x : U | (x : X) ∈ A}`

For `A ⊆ U ⊆ X` the subspace `{x : ↥U | (x : X) ∈ A}` of the space `U` is
canonically homeomorphic to the space `A`, the two maps being the evident
inclusions/projections.  This is what lets us transport the statement "the
inclusion of `A` into `U` induces an isomorphism on homology" from the subspace
form in which `Work.Homology.DeformationRetractHomology` is phrased to the
actual map `(pairHomOfSubset hAU).sub`. -/

/-- The canonical map `A → {x : U | (x : X) ∈ A}`, `a ↦ ⟨⟨a, _⟩, _⟩`. -/
def retrSubHom {X : TopCat} (A U : Set X) (hAU : A ⊆ U) :
    TopCat.of A ⟶ TopCat.of {x : ↥U | (x : X) ∈ A} :=
  TopCat.ofHom ⟨fun a => ⟨⟨(a : X), hAU a.2⟩, a.2⟩, by continuity⟩

/-- The canonical map `{x : U | (x : X) ∈ A} → A`, the inverse of
`retrSubHom`. -/
def retrSubInv {X : TopCat} (A U : Set X) :
    TopCat.of {x : ↥U | (x : X) ∈ A} ⟶ TopCat.of A :=
  TopCat.ofHom ⟨fun s => ⟨(s.1 : X), s.2⟩, by continuity⟩

theorem retrSubHom_inv {X : TopCat} {A U : Set X} (hAU : A ⊆ U) :
    retrSubHom A U hAU ≫ retrSubInv A U = 𝟙 (TopCat.of A) := by
  apply TopCat.hom_ext
  ext a
  rfl

theorem retrSubInv_hom {X : TopCat} {A U : Set X} (hAU : A ⊆ U) :
    retrSubInv A U ≫ retrSubHom A U hAU = 𝟙 (TopCat.of {x : ↥U | (x : X) ∈ A}) := by
  apply TopCat.hom_ext
  ext s
  rfl

/-- The inclusion `A ↪ U` of `hAU` factors through the canonical
homeomorphism `A ≅ {x : U | (x : X) ∈ A}`. -/
theorem retrSubHom_comp_incl {X : TopCat} {A U : Set X} (hAU : A ⊆ U) :
    retrSubHom A U hAU ≫ incl (X := TopCat.of U) {x : ↥U | (x : X) ∈ A} =
      (pairHomOfSubset hAU).sub := by
  apply TopCat.hom_ext
  ext a
  rfl

/-- The canonical homeomorphism `A ≅ {x : U | (x : X) ∈ A}` induces an
isomorphism on singular homology. -/
theorem isIso_singHomologyMap_retrSubHom {X : TopCat} {A U : Set X} (hAU : A ⊆ U)
    (R : ModuleCat ℤ) (n : ℕ) : IsIso (singHomologyMap R n (retrSubHom A U hAU)) := by
  refine ⟨singHomologyMap R n (retrSubInv A U), ?_, ?_⟩
  · rw [← singHomologyMap_comp, retrSubHom_inv, singHomologyMap_id]
  · rw [← singHomologyMap_comp, retrSubInv_hom, singHomologyMap_id]

/-- If `B` is a deformation retract of `Y`, the inclusion `B ↪ Y` induces an
isomorphism on singular homology. -/
theorem isIso_singHomologyMap_incl_of_deformationRetract {Y : TopCat} {B : Set Y}
    (h : DeformationRetract Y B) (R : ModuleCat ℤ) (n : ℕ) :
    IsIso (singHomologyMap R n (incl B)) := by
  obtain ⟨H⟩ := h.homotopy
  have hhom : singHomologyMap R n (h.retract ≫ incl B) = singHomologyMap R n (𝟙 Y) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (C := ModuleCat ℤ) H R n
  refine ⟨singHomologyMap R n h.retract, ?_, ?_⟩
  · rw [← singHomologyMap_comp, h.retract_incl, singHomologyMap_id]
  · rw [← singHomologyMap_comp, hhom, singHomologyMap_id]

/-- If `A ∩ U` is a deformation retract of `U`, then the inclusion
`A ↪ U` induces an isomorphism on singular homology in every degree. -/
theorem isIso_singHomologyMap_sub_of_deformationRetract {X : TopCat} {A U : Set X} (hAU : A ⊆ U)
    (h : DeformationRetract (TopCat.of U) {x : ↥U | (x : X) ∈ A}) (R : ModuleCat ℤ) (n : ℕ) :
    IsIso (singHomologyMap R n (pairHomOfSubset hAU).sub) := by
  have hcomp : singHomologyMap R n (pairHomOfSubset hAU).sub
      = singHomologyMap R n (retrSubHom A U hAU)
        ≫ singHomologyMap R n (incl (X := TopCat.of U) {x : ↥U | (x : X) ∈ A}) := by
    rw [← singHomologyMap_comp, retrSubHom_comp_incl]
  rw [hcomp]
  have h1 : IsIso (singHomologyMap R n (retrSubHom A U hAU)) :=
    isIso_singHomologyMap_retrSubHom hAU R n
  have h2 : IsIso (singHomologyMap R n
      (incl (X := TopCat.of U) {x : ↥U | (x : X) ∈ A})) :=
    isIso_singHomologyMap_incl_of_deformationRetract h R n
  infer_instance

/-- **Good pairs induce isomorphisms on relative homology.**  If `A ⊆ U ⊆ X` and
`A` (more precisely `A ∩ U`) is a deformation retract of `U`, then the map of pairs
`(X,A) → (X,U)` induced by the identity of `X` (namely
`pairHomOfSubset hAU`) induces an isomorphism on relative homology in every degree.

Route: compare the two short exact sequences of chain complexes `pairSeq ℤ X A` and
`pairSeq ℤ X U` through the morphism induced by `pairHomOfSubset hAU` (its two
relevant squares are `inclChain_naturality` and `relChainMap_comp_relProj`), and
apply Mathlib's five-lemma `isIso_homologyMap_τ₃`
(`Algebra/Homology/HomologySequenceLemmas.lean`): the vertical maps on the `A`- and
`U`-terms are isomorphisms because the inclusion `A ↪ U` and the retraction exhibit
`A` and `U` as homotopy equivalent (use
`Work.Homology.DeformationRetractHomology`, whose isomorphism has
`singHomologyMap (incl _)` as its inverse component; one must transport its
conclusion from the subspace `{x : ↥U | (x : X) ∈ A}` of `U` to `TopCat.of A`,
which are canonically homeomorphic since `A ⊆ U`). -/
theorem isIso_relHomologyMap_of_deformationRetract {X : TopCat} {A U : Set X} (hAU : A ⊆ U)
    (h : DeformationRetract (TopCat.of U) {x : ↥U | (x : X) ∈ A}) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (relChainMap ZMod (pairHomOfSubset hAU)) n) := by
  have h₁ : ∀ j, IsIso (HomologicalComplex.homologyMap
      (singChainMap ZMod (pairHomOfSubset hAU).sub) j) :=
    fun j => isIso_singHomologyMap_sub_of_deformationRetract hAU h ZMod j
  have h₂ : ∀ j, IsIso (HomologicalComplex.homologyMap (singChainMap ZMod (𝟙 X)) j) := by
    intro j
    rw [singChainMap_id, HomologicalComplex.homologyMap_id]
    infer_instance
  have h1epi : Epi (HomologicalComplex.homologyMap
      (pairSeqMap ZMod (pairHomOfSubset hAU)).τ₁ n) := by
    have h1i : IsIso (HomologicalComplex.homologyMap
        (pairSeqMap ZMod (pairHomOfSubset hAU)).τ₁ n) := h₁ n
    exact IsIso.epi_of_iso _
  have h2iso : IsIso (HomologicalComplex.homologyMap
      (pairSeqMap ZMod (pairHomOfSubset hAU)).τ₂ n) := h₂ n
  have h2mono : ∀ j, Mono (HomologicalComplex.homologyMap
      (pairSeqMap ZMod (pairHomOfSubset hAU)).τ₂ j) := fun j => by
    have h2j : IsIso (HomologicalComplex.homologyMap
        (pairSeqMap ZMod (pairHomOfSubset hAU)).τ₂ j) := h₂ j
    exact IsIso.mono_of_iso _
  exact HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (pairSeqMap ZMod (pairHomOfSubset hAU)) (pairSeq_shortExact ZMod X A)
    (pairSeq_shortExact ZMod X U) n h1epi h2iso (fun j _ => h₁ j) (fun j _ => h2mono j)

end

end Work.DeltaHomology
