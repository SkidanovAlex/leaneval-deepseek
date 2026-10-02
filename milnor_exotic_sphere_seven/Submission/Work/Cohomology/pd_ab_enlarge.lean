import Mathlib
import Submission.Work.Cohomology.relKernMono
import Submission.Work.Cohomology.pd_ab_incl_rel
import Submission.Work.Cohomology.pd_ab_clean
import Submission.Work.Cohomology.exists_relComplexMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Enlarging the pair in the `A+B` cochain complex

Let `A' ⊆ A` and `B' ⊆ B` be subsets of `X` (in the application `A = W∖K`, `A' = W∖K'` with
`K ⊆ K'`).  A cochain vanishing on chains in `A` and in `B` also vanishes on chains in the smaller
sets `A'`, `B'`, so there is a canonical map of complexes

  `pdABEnlarge X hA hB : pdABCoh X A B ⟶ pdABCoh X A' B'`,

the identity on the underlying cochains.  It is the "enlargement of the compact set" for Hatcher's
`A+B` complex.  We record its functoriality and its compatibility with `pdABInclRel` and with the
connecting map `pdABδ` of the `A+B` short exact sequence.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **The enlargement map of the `A+B` complex**: for `A' ⊆ A` and `B' ⊆ B` the identity on the
underlying cochains, from the complex truncated at `A, B` to the one truncated at `A', B'`. -/
def pdABEnlarge (X : TopCat) {A A' B B' : Set X} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    pdABCoh X A B ⟶ pdABCoh X A' B' :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (Submodule.inclusion
      (le_inf (inf_le_left.trans (relKern_mono (R := ℤ) hA))
        (inf_le_right.trans (relKern_mono (R := ℤ) hB)))))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [pdABCoh_d, pdABCoh_d]
      rfl)


/-- The map of relative complexes induced by enlarging the pair, on the "`A ∪ B`" slots. -/
def pdRelComplexEnlargeUnion (X : TopCat) {A A' B B' : Set X} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    relComplex ℤ X (A ∪ B) ⟶ relComplex ℤ X (A' ∪ B') :=
  relComplexMap ℤ (A' ∪ B') (A ∪ B) (𝟙 X) (Set.union_subset_union hA hB)


/-- The map of relative complexes induced by enlarging the pair, on the "`A ∩ B`" slots. -/
def pdRelComplexEnlargeInter (X : TopCat) {A A' B B' : Set X} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    relComplex ℤ X (A ∩ B) ⟶ relComplex ℤ X (A' ∩ B') :=
  relComplexMap ℤ (A' ∩ B') (A ∩ B) (𝟙 X) (Set.inter_subset_inter hA hB)

end

end Work.Cohomology
