import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.isZero_dualComplex_empty

/-!
# The relative chains of the empty set

For any topological space `X`, the empty set has no singular simplices, so the chain complex
`C_*(∅)` of the empty subspace is a zero object of `ChainComplex (ModuleCat ℤ) ℕ`.  Hence the
inclusion of chains `C_*(∅) ⟶ C_*(X)` is the zero morphism, and the cokernel projection

`C_*(X) ⟶ C_*(X,∅) = cokernel (C_*(∅) ⟶ C_*(X))`

is an isomorphism (the cokernel projection of a zero morphism is always an isomorphism).  Passing
to homology, `Hₙ(X,∅) ≅ Hₙ(X)` for every `n`.

This is the lemma `Work.Cohomology.relChains_empty_homology_iso`, the base case of the degree-wise
comparison of the relative chain complex of a pair with the absolute chains of the ambient space.
-/

set_option linter.style.haveILetI false

open CategoryTheory Limits Work.Cohomology
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- Every component of the singular chain complex of the empty space is a zero object: it is a
coproduct indexed by the (empty) type of singular `n`-simplices of `∅`. -/
theorem isZero_singularChains_empty_X (X : TopCat) (n : ℕ) :
    IsZero ((singularChains ℤ (TopCat.of (∅ : Set X))).X n) := by
  haveI : IsEmpty ((TopCat.toSSet.obj (TopCat.of (∅ : Set X))).obj (Opposite.op ⦋n⦌)) :=
    isEmpty_singularSimplex_empty X n
  exact isZero_coproduct_of_isEmpty
    (fun _ : ((TopCat.toSSet.obj (TopCat.of (∅ : Set X))).obj (Opposite.op ⦋n⦌)) =>
      ModuleCat.of ℤ ℤ)

/-- The inclusion of singular chains `C_*(∅) ⟶ C_*(X)` of the empty set is the zero morphism, since
its source is a complex all of whose components are zero objects. -/
theorem inclChains_empty_eq_zero (X : TopCat) : inclChains X (∅ : Set X) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.zero_f]
  exact (isZero_singularChains_empty_X X n).eq_zero_of_src _

/-- **The relative chains of the empty set agree with the absolute chains in homology.**

The cokernel projection `C_*(X) ⟶ C_*(X,∅)` is the cokernel projection of the zero morphism
`C_*(∅) ⟶ C_*(X)`, hence an isomorphism of chain complexes; applying the `n`-th homology functor
gives the stated isomorphism `Hₙ(X,∅) ≅ Hₙ(X)`. -/
theorem relChains_empty_homology_iso (X : TopCat) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X ∅)) n) := by
  haveI : IsIso (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X ∅)) :=
    CategoryTheory.Limits.cokernel.π_of_zero (inclChains_empty_eq_zero X)
  exact Functor.map_isIso
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n)
    (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X ∅))

end

end Work.Cohomology
