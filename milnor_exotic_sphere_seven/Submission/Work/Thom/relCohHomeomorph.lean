import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.cappedPairDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Relative cohomology is invariant under a homeomorphism of pairs

The goal of this file is `Work.Thom.relCohHomeomorph`: for a homeomorphism `e : X ≃ₜ Y` carrying a
subset `A ⊆ X` onto a subset `B ⊆ Y`, the pullback `relCohMap e : H^n(Y,B;R) ≅ H^n(X,A;R)` is an
isomorphism of `R`-modules, with inverse `relCohMap e.symm`.  This is the tool the base case of the
Thom isomorphism needs: the Thom pair of the trivial bundle over a point,
`(Σ _ : PUnit, ℝⁿ, {p | p.2 ≠ 0})`, is homeomorphic *as a pair* to `(ℝⁿ, ℝⁿ∖0)`
(`Bundle.TotalSpace.homeomorphProd` together with `PUnit × ℝⁿ ≅ ℝⁿ`), whose relative cohomology is
computed in `Work.Thom.relCohomology_euclidean_punctured`.

## A note on the imports

The natural route is to use `Work.Thom.relCohMap_id` and `Work.Thom.relCohMap_comp` and to assemble
the `Iso` from them.  Their import closures, however, cannot be loaded in a single environment: the
closure of `Submission.Work.Thom.relCohMap_id` contains `Submission.Work.Cohomology.localCohomology`
(through `capRelAux`) while the closure of `Submission.Work.Thom.relCohomology_euclidean_punctured`'s
sibling `Submission.Work.Thom.relCohMap_comp` contains `Submission.Work.Cohomology.dualZ` (through
`cappedPairDefs`), and those two modules *both declare* the constant `Work.Cohomology.dualZ`.

So the two functoriality statements are re-derived here at the chain level, exactly as
`Submission/Work/Thom/relCohMap_comp.lean` does: the chain-level input is
`Work.Cohomology.relComplexMap_comp`, `relComplexMap_id` and `relComplexMap_congr`
(`Submission/Work/Cohomology/cappedPairDefs.lean`), together with
`Work.Cohomology.dualChainMap_id` (`Submission/Work/Cohomology/Pullback.lean`).  The results
`relCohMap_id'`, `relCohMap_comp'` and `relCohMap_congr'` below are the primed copies of
`Work.Thom.relCohMap_id`, `Work.Thom.relCohMap_comp` and the natural congruence statement; they can
be imported freely together with the originals.
-/

set_option maxHeartbeats 1000000

namespace Work.Thom

open CategoryTheory

noncomputable section

/-- **The pullback of relative cohomology only depends on the underlying continuous map.**  Two
continuous maps which are equal induce the same map `H^n(Y,B;R) ⟶ H^n(X,A;R)`. -/
theorem relCohMap_congr' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {f f' : C(X, Y)}
    (A : Set X) (B : Set Y) (h : f = f') (hf : ∀ x ∈ A, f x ∈ B) (hf' : ∀ x ∈ A, f' x ∈ B)
    (R : Type) [CommRing R] (n : ℕ) :
    relCohMap f A B hf R n = relCohMap f' A B hf' R n := by
  -- Unfold the two pullbacks as homology maps of pair maps (an abbreviation unfolding only).
  show HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of X)
      (X₂ := TopCat.of Y) R A B (TopCat.ofHom f) hf) n
    = HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of X)
      (X₂ := TopCat.of Y) R A B (TopCat.ofHom f') hf') n
  rw [Work.Cohomology.relComplexMap_congr R A B
    (congrArg (fun f : C(X, Y) => (TopCat.ofHom f : TopCat.of X ⟶ TopCat.of Y)) h) hf hf']

/-- **Functoriality of the pullback of relative cohomology.**  For maps of pairs
`f : (A ⊆ X) → (B ⊆ Y)` and `g : (B ⊆ Y) → (C ⊆ Z)` the pullbacks compose contravariantly:

`relCohMap g ≫ relCohMap f = relCohMap (g ∘ f)`.

This is a copy of `Work.Thom.relCohMap_comp` (which cannot be imported here, see the module
docstring), proved directly at the chain level. -/
theorem relCohMap_comp' {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (A : Set X) (B : Set Y) (C : Set Z) (f : C(X, Y)) (g : C(Y, Z))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ y ∈ B, g y ∈ C) (hgf : ∀ x ∈ A, g (f x) ∈ C)
    (R : Type) [CommRing R] (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (relCohMap g B C hg R n) (relCohMap f A B hf R n)
      = relCohMap (g.comp f) A C hgf R n := by
  -- The chain-level identity: the two pair maps compose to the pair map of the composite.
  have key : CategoryTheory.CategoryStruct.comp
      (Work.Cohomology.relComplexMap (X₁ := TopCat.of Y) (X₂ := TopCat.of Z) R B C
        (TopCat.ofHom g) hg)
      (Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of Y) R A B
        (TopCat.ofHom f) hf)
    = Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of Z) R A C
        (TopCat.ofHom (g.comp f)) hgf := by
    rw [← Work.Cohomology.relComplexMap_comp (X₀ := TopCat.of X) (X₁ := TopCat.of Y)
      (X₂ := TopCat.of Z) R A B C (TopCat.ofHom f) (TopCat.ofHom g) hf hg]
    exact Work.Cohomology.relComplexMap_congr R A C (TopCat.ofHom_comp f g).symm
      (fun x hx => hg (f x) (hf x hx)) hgf
  -- Unfold the three pullbacks as the homology maps of the corresponding pair maps.
  have hg' : relCohMap g B C hg R n = HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of Y) (X₂ := TopCat.of Z) R B C (TopCat.ofHom g) hg) n := rfl
  have hf' : relCohMap f A B hf R n = HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of Y) R A B (TopCat.ofHom f) hf) n := rfl
  have hgf' : relCohMap (g.comp f) A C hgf R n = HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of Z) R A C (TopCat.ofHom (g.comp f)) hgf) n := rfl
  rw [hg', hf', hgf', ← HomologicalComplex.homologyMap_comp, key]

/-- **The pullback of relative cohomology along the identity of pairs is the identity.**  This is a
copy of `Work.Thom.relCohMap_id` (which cannot be imported here, see the module docstring). -/
theorem relCohMap_id' {X : Type} [TopologicalSpace X] (A : Set X) (R : Type) [CommRing R] (n : ℕ) :
    relCohMap (ContinuousMap.id X) A A (fun _ h => h) R n
      = CategoryTheory.CategoryStruct.id (RelCoh R n X A) := by
  -- The pullback of cochains along the identity of `TopCat.of X` is the identity.
  have hdual : Work.Cohomology.dualChainMap R (TopCat.of X) (TopCat.of X)
      (TopCat.ofHom (ContinuousMap.id X))
      = 𝟙 (Work.Cohomology.singularCochainComplex R (TopCat.of X)) := by
    rw [TopCat.ofHom_id, Work.Cohomology.dualChainMap_id]
  -- The pair map of the identity morphism is the identity of the relative cochain complex.
  -- The membership hypothesis is kept as a bound variable: `relComplexMap` does not depend on the
  -- proof that the map of pairs carries `A` into itself, and this formulation lets `key` be applied
  -- to the (elaborated) proof term occurring in the goal without any dependent rewriting.
  have key : ∀ (h : ∀ x ∈ A,
        (TopCat.ofHom (ContinuousMap.id X) : TopCat.of X ⟶ TopCat.of X) x ∈ A),
      Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of X) R A A
        (TopCat.ofHom (ContinuousMap.id X)) h
        = 𝟙 (Work.Cohomology.relComplex R (TopCat.of X) A) := by
    intro h
    apply HomologicalComplex.hom_ext
    intro k
    rw [Work.Cohomology.relComplexMap_f]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [ModuleCat.hom_ofHom, Work.Cohomology.relMapLM_coe, hdual,
      HomologicalComplex.id_f, ModuleCat.hom_id]
    exact congrArg Subtype.val rfl
  show HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of X)
      (X₂ := TopCat.of X) R A A (TopCat.ofHom (ContinuousMap.id X)) (fun _ h => h)) n
    = CategoryTheory.CategoryStruct.id (Work.Cohomology.relCohomology R (TopCat.of X) A n)
  exact (congrArg (fun φ => HomologicalComplex.homologyMap φ n) (key _)).trans
    (HomologicalComplex.homologyMap_id (Work.Cohomology.relComplex R (TopCat.of X) A) n)

/-- **Relative cohomology is invariant under a homeomorphism of pairs.**  For a homeomorphism
`e : X ≃ₜ Y` carrying `A ⊆ X` onto `B ⊆ Y` (the hypothesis `he : ∀ x, x ∈ A ↔ e x ∈ B`), the
pullback `relCohMap e` is an isomorphism of `R`-modules `H^n(Y,B;R) ≅ H^n(X,A;R)`, with inverse
`relCohMap e.symm`.

This is the tool the base case of the Thom isomorphism needs: the Thom pair of the trivial bundle
over a point, `(Σ _ : PUnit, ℝⁿ, {p | p.2 ≠ 0})`, is homeomorphic *as a pair* to `(ℝⁿ, ℝⁿ∖0)`
(`Bundle.TotalSpace.homeomorphProd`, together with the homeomorphism `PUnit × ℝⁿ ≅ ℝⁿ`), whose
relative cohomology is computed in `Work.Thom.relCohomology_euclidean_punctured`.

The `Iso` is built with `hom := relCohMap e A B hf`, `inv := relCohMap e.symm B A hg` and
`hom_inv_id` / `inv_hom_id` from `relCohMap_comp'` (with `e.comp e.symm = id` and
`e.symm.comp e = id`), `relCohMap_congr'` and `relCohMap_id'`. -/
theorem relCohHomeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (e : X ≃ₜ Y) (he : ∀ x, x ∈ A ↔ e x ∈ B)
    (R : Type) [CommRing R] (n : ℕ) :
    Nonempty (Work.Thom.RelCoh R n Y B ≅ Work.Thom.RelCoh R n X A) := by
  -- `e` carries `A` into `B`, and `e.symm` carries `B` back into `A`.
  have hf : ∀ x ∈ A, (e : C(X, Y)) x ∈ B := fun x hx => (he x).mp hx
  have hg : ∀ y ∈ B, (e.symm : C(Y, X)) y ∈ A :=
    fun y hy => (he (e.symm y)).mpr (by simpa using hy)
  -- The two composites of the map of pairs with its inverse are the identities.
  have hcompY : (e : C(X, Y)).comp (e.symm : C(Y, X)) = ContinuousMap.id Y := by
    ext y
    change e (e.symm y) = y
    exact e.apply_symm_apply y
  have hcompX : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X := by
    ext x
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  refine ⟨{ hom := relCohMap (e : C(X, Y)) A B hf R n
            inv := relCohMap (e.symm : C(Y, X)) B A hg R n
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · -- `relCohMap e ≫ relCohMap e.symm = 𝟙`, on `H^n(Y,B;R)`.
    exact (relCohMap_comp' (X := Y) (Y := X) (Z := Y) (A := B) (B := A) (C := B)
        (f := (e.symm : C(Y, X))) (g := (e : C(X, Y))) (hf := hg) (hg := hf)
        (R := R) (n := n) (fun y hy => hf ((e.symm : C(Y, X)) y) (hg y hy))).trans
      ((relCohMap_congr' (f := (e : C(X, Y)).comp (e.symm : C(Y, X)))
          (f' := ContinuousMap.id Y) B B hcompY
          (fun y hy => hf ((e.symm : C(Y, X)) y) (hg y hy)) (fun _ hy => hy) R n).trans
        (relCohMap_id' B R n))
  · -- `relCohMap e.symm ≫ relCohMap e = 𝟙`, on `H^n(X,A;R)`.
    exact (relCohMap_comp' (X := X) (Y := Y) (Z := X) (A := A) (B := B) (C := A)
        (f := (e : C(X, Y))) (g := (e.symm : C(Y, X))) (hf := hf) (hg := hg)
        (R := R) (n := n) (fun x hx => hg ((e : C(X, Y)) x) (hf x hx))).trans
      ((relCohMap_congr' (f := (e.symm : C(Y, X)).comp (e : C(X, Y)))
          (f' := ContinuousMap.id X) A A hcompX
          (fun x hx => hg ((e : C(X, Y)) x) (hf x hx)) (fun _ hx => hx) R n).trans
        (relCohMap_id' A R n))

end

end Work.Thom
