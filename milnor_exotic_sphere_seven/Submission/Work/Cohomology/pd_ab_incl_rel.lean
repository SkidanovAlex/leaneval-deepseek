import Mathlib
import Submission.Work.Cohomology.relKernMono
import Submission.Work.Cohomology.pd_ab_defs
import Submission.Work.Cohomology.pd_plumbing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The inclusion of the relative complex of a union into the `A+B` complex

For subsets `A, B ⊆ X` the `A+B` cochain complex `pdABCoh X A B` is the intersection of the two
relative complexes `C^*(X,A)` and `C^*(X,B)` (`Submission/Work/Cohomology/pd_ab_defs.lean`).  Since
`A ⊆ A ∪ B` and `B ⊆ A ∪ B`, every cochain vanishing on the chains of `A ∪ B` vanishes on the
chains of `A` and on the chains of `B`, so there is a canonical inclusion of cochain complexes

  `pdABInclRel X A B : C^*(X, A∪B) ⟶ C^*(X, A+B)`.

Its cokernel is the dual of the quotient `C_*(A∪B)/(C_*(A) + C_*(B))`, which is acyclic when `A`
and `B` are open (the small-chains theorem); hence the inclusion is a quasi-isomorphism — the
statement delegated as `Work.Cohomology.pdABCoh_quasiIso`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **The inclusion `C^*(X, A∪B) ⟶ C^*(X, A+B)`.** -/
def pdABInclRel (X : TopCat) (A B : Set X) : relComplex ℤ X (A ∪ B) ⟶ pdABCoh X A B :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (Submodule.inclusion
      (le_inf (relKern_mono (R := ℤ) (Set.subset_union_left : A ⊆ A ∪ B)) (relKern_mono (R := ℤ) (Set.subset_union_right : B ⊆ A ∪ B)))))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [relComplex_d, pdABCoh_d]
      rfl)

/-- The underlying cochain of `pdABInclRel` is the same cochain. -/
@[simp] theorem pdABInclRel_coe (X : TopCat) (A B : Set X) (n : ℕ)
    (x : (relComplex ℤ X (A ∪ B)).X n) :
    ((ModuleCat.Hom.hom ((pdABInclRel X A B).f n)) x).1 = x.1 := rfl

end

end Work.Cohomology
