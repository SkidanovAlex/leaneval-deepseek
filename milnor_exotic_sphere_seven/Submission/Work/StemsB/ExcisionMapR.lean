import Mathlib
import Submission.Work.Cohomology.Endgame.relComplexMapExcision

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Excision realised by the inclusion of pairs, over an arbitrary coefficient ring

`Submission/Work/Cohomology/Endgame/relComplexMapExcision.lean` proves, over `ℤ`, that the map of
relative cochain complexes induced by the inclusion of pairs `(X ∖ Z, A ∖ Z) ↪ (X, A)` (for
`closure Z ⊆ interior A`) is an isomorphism on homology in every degree.  Every ingredient of that
proof is coefficient-generic: the `ℤ`-dual of the inclusion of relative chain complexes is a
quasi-isomorphism `Work.Cohomology.Endgame.dualZMapRelChainsMapIsIso_of_interior` (already stated
over an arbitrary `CommRing R`), the identification of the relative cochains with the `ℤ`-dual of
the relative chains is `Work.Cohomology.relComplexMapDualZ` (also stated over `R`), and the outer
factors `Work.Cohomology.relZIsoComplex R` are isomorphisms of complexes.

This file records the coefficient-generic form; the `ℤ` original is untouched.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.StemsB

noncomputable section

/-- **Excision is realised by the map of pairs, over an arbitrary commutative ring.**

For `X : TopCat`, `A Z : Set X` with `closure Z ⊆ interior A`, and `V = X ∖ Z`, the map of relative
cochain complexes induced by the inclusion of pairs `(V, A ∩ V) ↪ (X, A)`,

`C^*(X, A; R) ⟶ C^*(V, A ∩ V; R)`,

is an isomorphism on homology in every degree. -/
theorem relComplexMapExcision_R (R : Type) [CommRing R] (X : TopCat) (A Z : Set X)
    (hZ : closure Z ⊆ interior A) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap R ((Subtype.val : {x : X | x ∉ Z} → X) ⁻¹' A) A
        (Work.Cohomology.subtypeIncl X {x : X | x ∉ Z})
        (fun x hx => by simp only [Work.Cohomology.subtypeIncl]; exact hx)) n) := by
  set V : Set X := {x : X | x ∉ Z} with hV
  -- the two interiors cover `X`, so that the small chains of the cover compute the relative chains
  have hcov : interior V ∪ interior A = Set.univ := by
    rw [hV, Set.union_comm]
    exact Work.Cohomology.univ_eq_interior_union_compl A Z hZ
  -- the `ℤ`-dual of the inclusion of relative chain complexes is a quasi-isomorphism
  have hmid : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.dualZMap R (Work.Cohomology.relChains (TopCat.of V) {y : V | (y : X) ∈ A})
        (Work.Cohomology.relChains X A) (Work.Cohomology.relChainsMap X V A)) n) :=
    Work.Cohomology.Endgame.dualZMapRelChainsMapIsIso_of_interior R X V A hcov n
  -- the duality identifications turn the pair map into the conjugate of the dualised chain map
  rw [Work.Cohomology.relComplexMapDualZ]
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  show CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Iso.inv (Work.Cohomology.relZIsoComplex R X A)) n ≫
    HomologicalComplex.homologyMap (Work.Cohomology.dualZMap R
      (Work.Cohomology.relChains (TopCat.of V) {y : V | (y : X) ∈ A})
      (Work.Cohomology.relChains X A) (Work.Cohomology.relChainsMap X V A)) n ≫
    HomologicalComplex.homologyMap
      (Iso.hom (Work.Cohomology.relZIsoComplex R (TopCat.of V) {y : V | (y : X) ∈ A})) n)
  -- the two outer factors are isomorphisms of complexes, hence isomorphisms on homology
  haveI h1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Iso.inv (Work.Cohomology.relZIsoComplex R X A)) n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n)
      (Iso.inv (Work.Cohomology.relZIsoComplex R X A))
  haveI h3 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Iso.hom (Work.Cohomology.relZIsoComplex R (TopCat.of V) {y : V | (y : X) ∈ A})) n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n)
      (Iso.hom (Work.Cohomology.relZIsoComplex R (TopCat.of V) {y : V | (y : X) ∈ A}))
  haveI := hmid
  infer_instance

end

end Work.StemsB
