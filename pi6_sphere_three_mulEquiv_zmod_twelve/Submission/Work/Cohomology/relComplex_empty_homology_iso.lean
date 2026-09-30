import Mathlib
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.isZero_dualComplex_empty
import Submission.Work.Cohomology.Singular

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The relative cochain complex of the empty set

For any topological space `X`, the empty set has no singular simplices, so every component of the
singular cochain complex `C^*(∅)` of the empty subspace is a zero object.  Consequently the
restriction map `C^*(X) ⟶ C^*(∅)` is the zero morphism, and the relative cochain complex
`C^*(X,∅)` — the degreewise kernel of the restriction, i.e. all of `C^n(X)` — agrees with `C^*(X)`:
the inclusion `relIncl ℤ X ∅ : C^*(X,∅) ⟶ C^*(X)` is an isomorphism of cochain complexes.

Passing to cohomology this gives `Hⁿ(X,∅) ≅ Hⁿ(X)` for every `n`, which is the lemma
`Work.Cohomology.relComplex_empty_homology_iso`; it is the base case of the degreewise comparison
of the relative cochain complex of a pair with the absolute cochains of the ambient space.
-/

set_option linter.style.haveILetI false

open CategoryTheory Limits Work.Cohomology
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- Every component of the singular chain complex of the empty space is a zero object: it is a
coproduct indexed by the (empty) type of singular `n`-simplices of `∅`. -/
theorem isZero_singularChains_empty_set (X : TopCat) (n : ℕ) :
    IsZero ((singularChains ℤ (TopCat.of (∅ : Set X))).X n) := by
  haveI : IsEmpty ((TopCat.toSSet.obj (TopCat.of (∅ : Set X))).obj (Opposite.op ⦋n⦌)) :=
    isEmpty_singularSimplex_empty X n
  exact isZero_coproduct_of_isEmpty
    (fun _ : ((TopCat.toSSet.obj (TopCat.of (∅ : Set X))).obj (Opposite.op ⦋n⦌)) =>
      ModuleCat.of ℤ ℤ)

/-- Every component of the singular cochain complex of the empty space is a zero object, being the
`ℤ`-dual of a zero module. -/
theorem isZero_singularCochainComplex_empty_set (X : TopCat) (n : ℕ) :
    IsZero ((singularCochainComplex ℤ (TopCat.of (∅ : Set X))).X n) :=
  isZero_dualObj_of_isZero ℤ (singularChains ℤ (TopCat.of (∅ : Set X)))
    (fun m => isZero_singularChains_empty_set X m) n

/-- The restriction of singular cochains to the empty set is zero, its target being a zero
object. -/
theorem restr_empty_eq_zero (X : TopCat) (n : ℕ) :
    (restr ℤ X (∅ : Set X)).f n = 0 :=
  (isZero_singularCochainComplex_empty_set X n).eq_zero_of_tgt _

/-- The relative `n`-cochains of the pair `(X,∅)` are all of `C^n(X)`: the kernel of the (zero)
restriction to the empty set. -/
theorem relKern_empty_eq_top (X : TopCat) (n : ℕ) :
    relKern ℤ X (∅ : Set X) n = ⊤ := by
  rw [relKern, restr_empty_eq_zero X n, ModuleCat.hom_zero, LinearMap.ker_zero]

/-- **The inclusion `C^*(X,A) ⟶ C^*(X)` is an isomorphism** as soon as every relative cochain
module is all of `C^n(X)`, i.e. `relKern R X A n = ⊤` for all `n`.  Indeed the `n`-th component of
`relIncl` is then the inclusion of the top submodule, a bijective `R`-linear map.

(The statement is made over a general commutative ring so that all submodule module structures are
the canonical `Submodule.module` ones; specialising to `R = ℤ` then causes no instance
mismatches.) -/
theorem isIso_relIncl_of_relKern_eq_top (R : Type) [CommRing R] (X : TopCat) (A : Set X)
    (h : ∀ n, relKern R X A n = ⊤) : IsIso (relIncl R X A) := by
  haveI : ∀ n, IsIso ((relIncl R X A).f n) := by
    intro n
    haveI : Mono ((relIncl R X A).f n) := by
      rw [ModuleCat.mono_iff_injective]
      exact Subtype.val_injective
    haveI : Epi ((relIncl R X A).f n) := by
      rw [ModuleCat.epi_iff_surjective]
      intro y
      refine ⟨⟨y, ?_⟩, rfl⟩
      rw [h n]
      exact Submodule.mem_top
    exact isIso_of_mono_of_epi _
  exact HomologicalComplex.Hom.isIso_of_components (relIncl R X A)

/-- **The inclusion `relIncl ℤ X ∅ : C^*(X,∅) ⟶ C^*(X)` is an isomorphism of cochain
complexes.** -/
theorem isIso_relIncl_empty (X : TopCat) : IsIso (relIncl ℤ X (∅ : Set X)) :=
  isIso_relIncl_of_relKern_eq_top ℤ X ∅ (fun n => relKern_empty_eq_top X n)

/-- **The relative cohomology of the pair `(X,∅)` agrees with the absolute cohomology of `X`.**

The inclusion of the relative cochain complex `relIncl ℤ X ∅` is an isomorphism of cochain
complexes, hence induces an isomorphism `Hⁿ(X,∅) ≅ Hⁿ(X)` on homology. -/
theorem relComplex_empty_homology_iso (X : TopCat) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ X ∅) n) := by
  haveI : IsIso (relIncl ℤ X (∅ : Set X)) := isIso_relIncl_empty X
  exact Functor.map_isIso
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n)
    (relIncl ℤ X (∅ : Set X))

end

end Work.Cohomology
