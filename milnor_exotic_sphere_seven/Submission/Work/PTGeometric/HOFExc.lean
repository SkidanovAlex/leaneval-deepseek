import Mathlib
import Submission.Work.PTGeometric.HOFDefs
import Submission.Work.Cohomology.excision
import Submission.Work.PTGeometric.HOFEuclid

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Excision as a linear equivalence, in the `RelH` vocabulary

For an open subset `U` of a topological space and a closed subset `K ⊆ U`, the inclusion of pairs
`(U, U∖K) → (X, X∖K)` induces an isomorphism on relative homology.  This file packages that
isomorphism as a `LinearEquiv` (`Work.PTGeometric.HOF.excEquiv`), in the excluded-set convention
`Work.Orient.RelH X N K = H_N(X, X∖K)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.PTGeometric.HOF

noncomputable section

variable {X : TopCat} {N : ℕ}

/-- The trace of `K` on `U`, as a subset of `↥U`. -/
abbrev trace (U : Set X) (K : Set X) : Set ↥U := {y : ↥U | (y : X) ∈ K}

/-- The pair map `(U, U∖K) → (X, X∖K)` induced by the inclusion, on relative homology. -/
def excMap (X : TopCat) (N : ℕ) (U : Set X) (K : Set X) :
    Work.Orient.RelH (TopCat.of ↥U) N (trace U K) →ₗ[ℤ] Work.Orient.RelH X N K :=
  (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U Kᶜ) N).hom

/-- `excMap` is the map induced by the inclusion of pairs, in the `RelHmapOf` normal form. -/
theorem excMap_eq_relHmapOf (X : TopCat) (N : ℕ) (U : Set X) (K : Set X) :
    excMap X N U K
      = RelHmapOf N (Work.Cohomology.subtypeIncl X U) (trace U K) K (fun y hy => hy) := by
  rw [excMap, RelHmapOf, Work.Cohomology.relChainsMap]
  exact congrArg (fun (φ : Work.Cohomology.relChains (TopCat.of ↥U) (trace U K)ᶜ ⟶
      Work.Cohomology.relChains X Kᶜ) => (HomologicalComplex.homologyMap φ N).hom)
    (Work.ThomBordism.doubleFC.relChainsMapOf_congr rfl rfl _ _)

/-- The complement of a point, as a subset of `↥U`. -/
abbrev punctU (U : Set X) (a : X) : Set ↥U := {z : ↥U | (z : X) ≠ a}

/-- `punctU` is the complement of the trace of `{a}`. -/
theorem punctU_eq_compl_trace (U : Set X) (a : X) :
    punctU U a = (trace U ({a} : Set X))ᶜ := rfl

/-- A point of `↥U` outside the trace of `{a}` is not `a`. -/
theorem ne_of_notMem_trace_singleton {U : Set X} {a : X} {z : ↥U}
    (h : z ∉ trace U ({a} : Set X)) : (z : X) ≠ a := by
  intro hz
  exact h (show (z : X) ∈ ({a} : Set X) from hz)

/-- **Excision**: for `U` open and `K ⊆ U` closed, `excMap` is an isomorphism. -/
theorem isIso_excMap (X : TopCat) (N : ℕ) (U : Set X) (hU : IsOpen U) (K : Set X)
    (hKU : K ⊆ U) (hKc : IsClosed K) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U Kᶜ) N) := by
  have hcov : U ∪ Kᶜ = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
    by_cases h : z ∈ U
    · exact Or.inl h
    · exact Or.inr (fun hz => h (hKU hz))
  exact Work.Cohomology.excision_relChainsMap_isIso X U Kᶜ hU hKc.isOpen_compl hcov N

/-- **Excision as a linear equivalence.** -/
noncomputable def excEquiv (X : TopCat) (N : ℕ) (U : Set X) (hU : IsOpen U) (K : Set X)
    (hKU : K ⊆ U) (hKc : IsClosed K) :
    Work.Orient.RelH (TopCat.of ↥U) N (trace U K) ≃ₗ[ℤ] Work.Orient.RelH X N K :=
  LinearEquiv.ofBijective (excMap X N U K) (by
    haveI hiso := isIso_excMap X N U hU K hKU hKc
    exact ConcreteCategory.bijective_of_isIso
      (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U Kᶜ) N))

/-- The defining property of `excEquiv`. -/
theorem excEquiv_apply (X : TopCat) (N : ℕ) (U : Set X) (hU : IsOpen U) (K : Set X)
    (hKU : K ⊆ U) (hKc : IsClosed K) (x : Work.Orient.RelH (TopCat.of ↥U) N (trace U K)) :
    excEquiv X N U hU K hKU hKc x = excMap X N U K x := rfl

/-- The inverse of `excEquiv` is the restriction: `excEquiv.symm` followed by the inclusion is the
restriction map `RelH X N K → RelH (TopCat.of ↥U) N (trace U K)`. -/
theorem excMap_comp_symm (X : TopCat) (N : ℕ) (U : Set X) (hU : IsOpen U) (K : Set X)
    (hKU : K ⊆ U) (hKc : IsClosed K) (x : Work.Orient.RelH X N K) :
    excMap X N U K ((excEquiv X N U hU K hKU hKc).symm x) = x := by
  have h : excEquiv X N U hU K hKU hKc ((excEquiv X N U hU K hKU hKc).symm x) = x :=
    LinearEquiv.apply_symm_apply _ x
  rwa [excEquiv_apply] at h

end

end Work.PTGeometric.HOF
