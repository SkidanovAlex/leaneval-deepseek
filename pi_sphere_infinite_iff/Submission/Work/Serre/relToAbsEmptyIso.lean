import Mathlib
import Submission.Work.Serre.relCohMV_les_rat
import Submission.Work.Serre.MVCohRatDefs
import Submission.Work.Cohomology.relComplex_empty_homology_iso
import Submission.Work.Cohomology.isZero_dualComplex_empty

/-!
# The identification `H^n(X,∅) ≅ H^n(X)` over `ℚ`

`Work.Cohomology.relComplex_empty_homology_iso` proves, over `ℤ`, that the inclusion
`relIncl ℤ X ∅ : C^*(X,∅) ⟶ C^*(X)` is an isomorphism of cochain complexes, hence that the
forgetful map `H^n(X,∅) ≅ H^n(X)` is bijective.  This file repeats the argument over `ℚ` (the
constructions are coefficient-generic, only the two auxiliary statements about the cochains of the
empty space are stated for `ℤ` in the workspace), and records the result in the vocabulary of
`Work.Thom.relToAbs`, which is what the Mayer–Vietoris ladder of the
`bijective_mixedCup_of_openCover` argument needs.
-/

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Work.Cohomology
open scoped Simplicial

namespace Work.Serre

noncomputable section

/-- Every component of the singular chain complex over `ℚ` of the empty space is a zero object: it
is a coproduct indexed by the (empty) type of singular `n`-simplices of `∅`. -/
theorem isZero_singularChains_empty_set_rat (X : TopCat) (n : ℕ) :
    IsZero ((Work.Cohomology.singularChains ℚ (TopCat.of (∅ : Set X))).X n) := by
  haveI : IsEmpty ((TopCat.toSSet.obj (TopCat.of (∅ : Set X))).obj (Opposite.op ⦋n⦌)) :=
    Work.Cohomology.isEmpty_singularSimplex_empty X n
  exact Work.Cohomology.isZero_coproduct_of_isEmpty
    (fun _ : ((TopCat.toSSet.obj (TopCat.of (∅ : Set X))).obj (Opposite.op ⦋n⦌)) =>
      ModuleCat.of ℚ ℚ)

/-- Every component of the rational singular cochain complex of the empty space is a zero object. -/
theorem isZero_singularCochainComplex_empty_set_rat (X : TopCat) (n : ℕ) :
    IsZero ((Work.Cohomology.singularCochainComplex ℚ (TopCat.of (∅ : Set X))).X n) :=
  Work.Cohomology.isZero_dualObj_of_isZero ℚ (Work.Cohomology.singularChains ℚ
    (TopCat.of (∅ : Set X))) (fun m => isZero_singularChains_empty_set_rat X m) n

/-- The restriction of rational singular cochains to the empty set is zero. -/
theorem restr_empty_eq_zero_rat (X : TopCat) (n : ℕ) :
    (Work.Cohomology.restr ℚ X (∅ : Set X)).f n = 0 :=
  (isZero_singularCochainComplex_empty_set_rat X n).eq_zero_of_tgt _

/-- The relative rational `n`-cochains of the pair `(X,∅)` are all of `C^n(X)`. -/
theorem relKern_empty_eq_top_rat (X : TopCat) (n : ℕ) :
    Work.Cohomology.relKern ℚ X (∅ : Set X) n = ⊤ := by
  rw [Work.Cohomology.relKern, restr_empty_eq_zero_rat X n, ModuleCat.hom_zero,
    LinearMap.ker_zero]

/-- **The inclusion `C^*(X,∅) ⟶ C^*(X)` is an isomorphism over `ℚ`.** -/
theorem isIso_relIncl_empty_rat (X : TopCat) :
    IsIso (Work.Cohomology.relIncl ℚ X (∅ : Set X)) :=
  Work.Cohomology.isIso_relIncl_of_relKern_eq_top ℚ X ∅ (fun n => relKern_empty_eq_top_rat X n)

/-- **The forgetful map `H^n(X,∅;ℚ) ⟶ H^n(X;ℚ)` is an isomorphism**: the relative cohomology of
the pair `(X,∅)` is the absolute cohomology of `X`. -/
theorem isIso_relToAbs_empty_rat {B : Type} [TopologicalSpace B] (n : ℕ) :
    IsIso (Work.Thom.relToAbs ℚ (∅ : Set B) n) := by
  haveI : IsIso (Work.Cohomology.relIncl ℚ (TopCat.of B) (∅ : Set B)) :=
    isIso_relIncl_empty_rat (TopCat.of B)
  exact Functor.map_isIso
    (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n)
    (Work.Cohomology.relIncl ℚ (TopCat.of B) (∅ : Set B))

end

end Work.Serre
