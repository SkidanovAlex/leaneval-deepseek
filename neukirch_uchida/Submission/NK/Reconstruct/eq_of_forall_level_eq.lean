import Mathlib
import Submission.NK.Reconstruct.PlaceCorrespondence

/-!
# Places of a separable closure are determined by their restrictions to the finite levels

Let `K` be a number field with separable closure `K'`.  A *place* of `K'` (a `ValuationSubring`
of `K'`) is determined by the collection of its restrictions to the finite Galois intermediate
fields `L ⊆ K'`: if two valuation subrings of `K'` agree after `comap`-ing to every such `L`,
then they are equal.

The mathematical content is the cofinality of the finite Galois levels in `K'`: by infinite Galois
theory every element `x : K'` lies in a finite Galois intermediate field, namely the normal closure
of `K(x)` inside `K'` (`FiniteGaloisIntermediateField.adjoin K {x}`).  Since `K'` is a separable
closure of `K`, the extension `K'/K` is Galois (`IsSepClosure.isGalois`), so that closure is
available; being a finite extension of the number field `K` the level is itself a number field
(`NumberField.of_module_finite`), which is what lets it be used in the hypothesis.

This is the analogue for places of `NK.Reconstruct.eq_of_restrictNormalHom_eq` for automorphisms,
and it is used to descend a condition on all finite levels to the whole separable closure.
-/

namespace NK.Reconstruct

set_option linter.unusedVariables false

theorem eq_of_forall_level_eq {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsSepClosure K K'] {B₁ B₂ : ValuationSubring K'}
    (h₁ : B₁.comap (algebraMap K K') ≠ ⊤) (h₂ : B₂.comap (algebraMap K K') ≠ ⊤)
    (h : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L],
      B₁.comap (algebraMap ↥L K') = B₂.comap (algebraMap ↥L K')) :
    B₁ = B₂ := by
  -- it suffices to compare the membership of every `x : K'` in the two valuation subrings
  ext x
  -- the finite Galois level containing `x`: the normal closure of `K(x)` in `K'`
  let M : FiniteGaloisIntermediateField K K' := FiniteGaloisIntermediateField.adjoin K ({x} : Set K')
  let L : IntermediateField K K' := M.toIntermediateField
  have hx : x ∈ L :=
    FiniteGaloisIntermediateField.subset_adjoin K ({x} : Set K') (Set.mem_singleton x)
  have hfin : FiniteDimensional K L := M.finiteDimensional
  have hgal : IsGalois K L := M.isGalois
  have hnum : NumberField ↥L := NumberField.of_module_finite K ↥L
  have hnorm : Normal K L := hgal.to_normal
  -- the hypothesis at this level, read on the element `x`
  have heq := h L
  have hm : (⟨x, hx⟩ : ↥L) ∈ B₁.comap (algebraMap ↥L K') ↔
      (⟨x, hx⟩ : ↥L) ∈ B₂.comap (algebraMap ↥L K') := by rw [heq]
  simpa using hm

end NK.Reconstruct
