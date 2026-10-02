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

namespace Work.Thom

/-- **Functoriality of the pullback of relative cohomology.**  For maps of pairs
`f : (A ⊆ X) → (B ⊆ Y)` and `g : (B ⊆ Y) → (C ⊆ Z)` the pullbacks compose contravariantly:

`relCohMap g ≫ relCohMap f = relCohMap (g ∘ f)`.

This is what makes `H^n(-,-;R)` a contravariant functor on pairs, and together with
`Work.Thom.relCohMap_id` it yields invariance under *homeomorphisms of pairs* — the tool the base
case of the Thom isomorphism needs: the Thom pair of the trivial bundle over a point is
`(Σ _ : PUnit, ℝⁿ, {p | p.2 ≠ 0})`, related to `(ℝⁿ, ℝⁿ∖0)` by the homeomorphism
`Bundle.TotalSpace.homeomorphProd`.

Suggested route: the chain-level identity is already in the workspace as
`Work.Cohomology.relComplexMap_comp` (`Submission/Work/Cohomology/cappedPairDefs.lean`) and
`Work.Cohomology.relComplexMap_comp'` (`AuxFactor.lean`); conclude with
`HomologicalComplex.homologyMap_comp` and the definitions `Work.Thom.relCohMap` /
`Work.Thom.relToAbs` / `Work.Thom.CohMap`.  (Beware: elaborating `HomologicalComplex.homologyMap`
with an unspecified morphism times out; give the implicit arguments `X₁`/`X₂` of `relComplexMap`
explicitly and state the intermediate equalities with an explicit type.  `≫` is written out as
`CategoryTheory.CategoryStruct.comp` so that the statement is self-contained.) -/
theorem relCohMap_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (A : Set X) (B : Set Y) (C : Set Z) (f : C(X, Y)) (g : C(Y, Z))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ y ∈ B, g y ∈ C)
    (hgf : ∀ x ∈ A, g (f x) ∈ C) (R : Type) [CommRing R] (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (Work.Thom.relCohMap g B C hg R n)
        (Work.Thom.relCohMap f A B hf R n)
      = Work.Thom.relCohMap (g.comp f) A C hgf R n := by
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
  have hg' : Work.Thom.relCohMap g B C hg R n = HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of Y) (X₂ := TopCat.of Z) R B C (TopCat.ofHom g) hg) n := rfl
  have hf' : Work.Thom.relCohMap f A B hf R n = HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of Y) R A B (TopCat.ofHom f) hf) n := rfl
  have hgf' : Work.Thom.relCohMap (g.comp f) A C hgf R n = HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of Z) R A C (TopCat.ofHom (g.comp f)) hgf) n := rfl
  rw [hg', hf', hgf', ← HomologicalComplex.homologyMap_comp, key]

end Work.Thom
