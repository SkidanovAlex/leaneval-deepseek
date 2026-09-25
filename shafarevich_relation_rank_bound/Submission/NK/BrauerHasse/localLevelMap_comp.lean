import Mathlib
import Submission.NK.BrauerHasse.Profinite

namespace NK.BrauerHasse

set_option autoImplicit false

universe u

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The quotient maps defining the local levels are compatible with composition, i.e. the maps
`(U ∩ D_A)/((U ∩ D_A) ∩ Gal(K'/L')) →* (U ∩ D_A)/((U ∩ D_A) ∩ Gal(K'/L))` form a functor on the
lattice of finite Galois intermediate fields. -/
lemma localLevelQuotHom_comp (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'} (h₁ : L₁ ≤ L₂) (h₂ : L₂ ≤ L₃) :
    (localLevelQuotHom U A h₁).comp (localLevelQuotHom U A h₂) =
      localLevelQuotHom U A (h₁.trans h₂) := by
  simp only [localLevelQuotHom]
  rw [QuotientGroup.map_comp_map (N := L₃.fixingSubgroup.subgroupOf (U ⊓ stabSubgroup A))
      (M := L₂.fixingSubgroup.subgroupOf (U ⊓ stabSubgroup A))
      (O := L₁.fixingSubgroup.subgroupOf (U ⊓ stabSubgroup A))
      (f := MonoidHom.id ↥(U ⊓ stabSubgroup A)) (g := MonoidHom.id ↥(U ⊓ stabSubgroup A))]
  simp

/-- The local inflation maps between the local cohomology levels are compatible with composition:
the local level system is a functor on the finite Galois intermediate fields. -/
theorem localLevelMap_comp {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : ValuationSubring K') {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'}
    (h₁ : L₁ ≤ L₂) (h₂ : L₂ ≤ L₃) :
    CategoryTheory.CategoryStruct.comp (NK.BrauerHasse.localLevelMap p U A h₁)
        (NK.BrauerHasse.localLevelMap p U A h₂) =
      NK.BrauerHasse.localLevelMap p U A (h₁.trans h₂) := by
  simp only [localLevelMap]
  rw [← H2.map_comp, localLevelQuotHom_comp]

end NK.BrauerHasse
