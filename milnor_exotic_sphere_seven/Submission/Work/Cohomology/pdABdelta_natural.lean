import Mathlib
import Submission.Work.Cohomology.pd_ab_enlarge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Naturality of the connecting map `pdABδ` under enlarging the pair

For subsets `A' ⊆ A` and `B' ⊆ B` of a topological space `X`, the identity on underlying cochains
gives a morphism of short exact sequences

`pdABShort X A B ⟶ pdABShort X A' B'`

with components `pdABEnlarge X hA hB` (on `C^*(X,A+B)`), the degreewise restriction on the middle
term `C^*(X,A) ⊞ C^*(X,B)` (`pdABMid`), and `pdRelComplexEnlargeInter X hA hB` (on
`C^*(X, A∩B)`).

The naturality of the connecting homomorphism of the long exact sequence associated to a morphism
of short exact sequences of complexes (`HomologicalComplex.HomologySequence.δ_naturality`) then
gives the commutativity of

`H^k(X,A∩B) --δ--> H^{k+1}(X,A+B)`
`     |                        |`
`H^k(X,A'∩B') --δ--> H^{k+1}(X,A'+B')`
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- The restriction `C^*(X,A) ⟶ C^*(X,A')` induced by `A' ⊆ A`. -/
abbrev pdRelEnlargeA (X : TopCat) {A A' : Set X} (hA : A' ⊆ A) :
    relComplex ℤ X A ⟶ relComplex ℤ X A' :=
  relComplexMap ℤ A' A (𝟙 X) (fun _ hx => hA hx)

/-- The restriction `C^*(X,B) ⟶ C^*(X,B')` induced by `B' ⊆ B`. -/
abbrev pdRelEnlargeB (X : TopCat) {B B' : Set X} (hB : B' ⊆ B) :
    relComplex ℤ X B ⟶ relComplex ℤ X B' :=
  relComplexMap ℤ B' B (𝟙 X) (fun _ hx => hB hx)

/-- **The map on the middle terms of the `A+B` short exact sequence** induced by enlarging the
pair: the degreewise restriction `C^*(X,A) ⊞ C^*(X,B) ⟶ C^*(X,A') ⊞ C^*(X,B')`. -/
def pdABMid (X : TopCat) {A A' B B' : Set X} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    relComplex ℤ X A ⊞ relComplex ℤ X B ⟶ relComplex ℤ X A' ⊞ relComplex ℤ X B' :=
  biprod.map (pdRelEnlargeA X hA) (pdRelEnlargeB X hB)

/-! ## The four cochain-level identifications -/

/-- The `A`-component: enlarging then including in `C^*(X,A)` is including in `C^*(X,A')`. -/
lemma pdABInclA_comp_pdRelEnlargeA (X : TopCat) {A A' B B' : Set X} (hA : A' ⊆ A)
    (hB : B' ⊆ B) :
    pdABInclA X A B ≫ pdRelEnlargeA X hA = pdABEnlarge X hA hB ≫ pdABInclA X A' B' := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [show (show ↥(relKern ℤ X A' n) from
      (ModuleCat.Hom.hom ((pdRelEnlargeA X hA).f n))
        ((ModuleCat.Hom.hom ((pdABInclA X A B).f n)) x)).1
      = (show ↥(relKern ℤ X A n) from (ModuleCat.Hom.hom ((pdABInclA X A B).f n)) x).1
      from PDABClean.relMapLM_id_coe X (fun _ hx => hA hx) n _]
  rfl

/-- The `B`-component: enlarging then including in `C^*(X,B)` is including in `C^*(X,B')`. -/
lemma pdABInclB_comp_pdRelEnlargeB (X : TopCat) {A A' B B' : Set X} (hA : A' ⊆ A)
    (hB : B' ⊆ B) :
    pdABInclB X A B ≫ pdRelEnlargeB X hB = pdABEnlarge X hA hB ≫ pdABInclB X A' B' := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [show (show ↥(relKern ℤ X B' n) from
      (ModuleCat.Hom.hom ((pdRelEnlargeB X hB).f n))
        ((ModuleCat.Hom.hom ((pdABInclB X A B).f n)) x)).1
      = (show ↥(relKern ℤ X B n) from (ModuleCat.Hom.hom ((pdABInclB X A B).f n)) x).1
      from PDABClean.relMapLM_id_coe X (fun _ hx => hB hx) n _]
  rfl

/-- Restricting `C^*(X,A)` to `C^*(X,A'∩B')` via `A'` is the same as first going to `C^*(X,A∩B)`
and then enlarging the pair. -/
lemma pdRelEnlargeA_comp_pdToInterA (X : TopCat) {A A' B B' : Set X} (hA : A' ⊆ A)
    (hB : B' ⊆ B) :
    pdRelEnlargeA X hA ≫ pdToInterA X A' B'
      = pdToInterA X A B ≫ pdRelComplexEnlargeInter X hA hB := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  rfl

/-- Restricting `C^*(X,B)` to `C^*(X,A'∩B')` via `B'` is the same as first going to `C^*(X,A∩B)`
and then enlarging the pair. -/
lemma pdRelEnlargeB_comp_pdToInterB (X : TopCat) {A A' B B' : Set X} (hA : A' ⊆ A)
    (hB : B' ⊆ B) :
    pdRelEnlargeB X hB ≫ pdToInterB X A' B'
      = pdToInterB X A B ≫ pdRelComplexEnlargeInter X hA hB := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  rfl

/-! ## The two squares of the morphism of short exact sequences -/

/-- The first square: `pdABEnlarge` is compatible with the diagonals. -/
lemma pdABEnlarge_comp_pdABDiag (X : TopCat) {A A' B B' : Set X} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    pdABEnlarge X hA hB ≫ pdABDiag X A' B' = pdABDiag X A B ≫ pdABMid X hA hB := by
  apply biprod.hom_ext
  · dsimp only [pdABDiag, pdABMid]
    simp only [Category.assoc, biprod.lift_fst, biprod.lift_fst_assoc, biprod.map_fst]
    rw [show pdABInclA X A B ≫ pdRelEnlargeA X hA
          = pdABEnlarge X hA hB ≫ pdABInclA X A' B'
        from pdABInclA_comp_pdRelEnlargeA X hA hB]
  · dsimp only [pdABDiag, pdABMid]
    simp only [Category.assoc, biprod.lift_snd, biprod.lift_snd_assoc, biprod.map_snd]
    rw [show pdABInclB X A B ≫ pdRelEnlargeB X hB
          = pdABEnlarge X hA hB ≫ pdABInclB X A' B'
        from pdABInclB_comp_pdRelEnlargeB X hA hB]

/-- The second square: `pdABMid` is compatible with the difference maps. -/
lemma pdABMid_comp_pdBiprodToInter (X : TopCat) {A A' B B' : Set X} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    pdABMid X hA hB ≫ pdBiprodToInter X A' B'
      = pdBiprodToInter X A B ≫ pdRelComplexEnlargeInter X hA hB := by
  apply biprod.hom_ext'
  · dsimp only [pdABMid, pdBiprodToInter]
    simp only [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc]
    rw [show pdRelEnlargeA X hA ≫ pdToInterA X A' B'
          = pdToInterA X A B ≫ pdRelComplexEnlargeInter X hA hB
        from pdRelEnlargeA_comp_pdToInterA X hA hB]
  · dsimp only [pdABMid, pdBiprodToInter]
    simp only [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc]
    rw [Preadditive.comp_neg, Preadditive.neg_comp,
      pdRelEnlargeB_comp_pdToInterB X hA hB]

/-! ## Naturality of `pdABδ` -/

/-- **Naturality of the `A+B` connecting map under enlarging the pair.** -/
theorem pdABdelta_natural (X : TopCat) {A A' B B' : Set X} (hA : A' ⊆ A) (hB : B' ⊆ B) (k : ℕ) :
    CategoryTheory.CategoryStruct.comp (Work.Cohomology.PDABClean.pdABδ X A B k)
        (HomologicalComplex.homologyMap (Work.Cohomology.pdABEnlarge X hA hB) (k + 1))
      = CategoryTheory.CategoryStruct.comp
          (HomologicalComplex.homologyMap (Work.Cohomology.pdRelComplexEnlargeInter X hA hB) k)
          (Work.Cohomology.PDABClean.pdABδ X A' B' k) := by
  let φ : pdABShort X A B ⟶ pdABShort X A' B' :=
    { τ₁ := pdABEnlarge X hA hB
      τ₂ := pdABMid X hA hB
      τ₃ := pdRelComplexEnlargeInter X hA hB
      comm₁₂ := pdABEnlarge_comp_pdABDiag X hA hB
      comm₂₃ := pdABMid_comp_pdBiprodToInter X hA hB }
  have h := HomologicalComplex.HomologySequence.δ_naturality φ
    (PDABClean.pdAB_shortExact X A B) (PDABClean.pdAB_shortExact X A' B') k (k + 1)
    (by simp [ComplexShape.up_Rel])
  simp only [PDABClean.pdABδ]
  exact h

end

end Work.Cohomology
