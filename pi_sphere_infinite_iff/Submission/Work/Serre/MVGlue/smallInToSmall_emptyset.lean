import Mathlib
import Submission.Work.Cohomology.RelMVDefs
import Submission.Work.Cohomology.isZero_dualComplex_empty
import Submission.Work.Cohomology.relComplex_empty_homology_iso
import Submission.Work.Cohomology.relChains_empty_homology_iso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The relative small chains of `(X, ∅)`

For any space `X`, subsets `U, V ⊆ X` and `A = ∅`, the small chains lying in `∅` are zero: a
singular simplex can never have its (nonempty) image contained in the empty set.  Hence the
subcomplex `smallInSubcomplex U V ∅` has no simplices at all, its chain complex
`smallInChains U V ∅` is a zero object, and the canonical map

`smallInToSmall U V ∅ : smallInChains U V ∅ ⟶ smallChains U V`

is the zero morphism.  The cokernel projection of a zero morphism is an isomorphism, which is the
statement `Work.Serre.MVGlue.smallInToSmall_emptyset`.
-/

set_option linter.style.haveILetI false

open CategoryTheory Limits
open scoped Simplicial

namespace Work.Serre.MVGlue

noncomputable section

/-- No singular simplex of `X` is small for the pair `(U,V)` and lies in the empty set: its image
(the range of the corresponding map on the standard simplex) is nonempty. -/
theorem isEmpty_smallInSSet_emptyset (X : TopCat) (U V : Set X) (n : ℕ) :
    IsEmpty ((Work.Cohomology.smallInSSet U V (∅ : Set X)).obj (Opposite.op ⦋n⦌)) := by
  refine ⟨fun σ => False.elim ?_⟩
  obtain ⟨-, h2⟩ := σ.2
  haveI : Nonempty (stdSimplex ℝ (Fin (n + 1))) := inferInstance
  exact h2 ⟨Classical.arbitrary _, rfl⟩

/-- Every component of the small chains lying in the empty set is a zero object: it is a coproduct
indexed by the (empty) type of small simplices lying in `∅`. -/
theorem isZero_smallInChains_emptyset_X (X : TopCat) (U V : Set X) (n : ℕ) :
    IsZero ((Work.Cohomology.smallInChains U V (∅ : Set X)).X n) := by
  haveI : IsEmpty ((Work.Cohomology.smallInSSet U V (∅ : Set X)).obj (Opposite.op ⦋n⦌)) :=
    isEmpty_smallInSSet_emptyset X U V n
  exact Work.Cohomology.isZero_coproduct_of_isEmpty
    (fun _ : ((Work.Cohomology.smallInSSet U V (∅ : Set X)).obj (Opposite.op ⦋n⦌)) =>
      ModuleCat.of ℤ ℤ)

/-- The canonical map `smallInChains U V ∅ ⟶ smallChains U V` is the zero morphism, because its
source is a chain complex all of whose components are zero objects. -/
theorem smallInToSmall_emptyset_eq_zero (X : TopCat) (U V : Set X) :
    Work.Cohomology.smallInToSmall U V (∅ : Set X) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.zero_f]
  exact (isZero_smallInChains_emptyset_X X U V n).eq_zero_of_src _

theorem smallInToSmall_emptyset (X : TopCat) (U V : Set X) :
    CategoryTheory.IsIso
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.smallInToSmall U V (∅ : Set X))) :=
  CategoryTheory.Limits.cokernel.π_of_zero (smallInToSmall_emptyset_eq_zero X U V)

end

end Work.Serre.MVGlue
