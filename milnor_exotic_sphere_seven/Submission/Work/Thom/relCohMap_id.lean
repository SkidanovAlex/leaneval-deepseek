import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.capRelAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

open CategoryTheory

/-- The **pullback of relative cohomology along the identity map of pairs is the identity**.
Together with `Work.Thom.relCohMap_comp` this makes `H^n(-,-;R)` a contravariant functor on pairs,
hence invariant under homeomorphisms of pairs — the tool the base case of the Thom isomorphism needs
(`Bundle.TotalSpace.homeomorphProd` identifies the Thom pair of the trivial bundle over a point with
the pair `(ℝⁿ, ℝⁿ∖0)` whose cohomology is `Work.Thom.relCohomology_euclidean_punctured`).

Suggested route: the chain-level statement is already in the workspace as
`Work.Cohomology.capRel_relComplexMap_id` (`Submission/Work/Cohomology/capRelAux.lean`);
conclude with `HomologicalComplex.homologyMap_id` and `TopCat.ofHom_id`.  (Beware: elaborating
`HomologicalComplex.homologyMap` with an unspecified morphism times out; give the implicit arguments
`X₁`/`X₂` of `relComplexMap` explicitly and state the intermediate equality with an explicit type.
`𝟙` is written out as `CategoryTheory.CategoryStruct.id` so that the statement is
self-contained.) -/
theorem relCohMap_id {X : Type} [TopologicalSpace X] (A : Set X) (R : Type) [CommRing R] (n : ℕ) :
    Work.Thom.relCohMap (ContinuousMap.id X) A A (fun _ h => h) R n
      = CategoryTheory.CategoryStruct.id (Work.Thom.RelCoh R n X A) := by
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

end Work.Thom
