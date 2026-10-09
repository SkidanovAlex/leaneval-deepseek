import Mathlib
import Submission.NK.HassePrinciple.MuColimit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.ABHN

/-- An element of a finite Galois intermediate field `L'` which is fixed by every
`K`-automorphism of `K'` that fixes `L` already lies in `L`, hence its unit comes from
`(↥L)ˣ` along the inclusion `L ≤ L'`. -/
theorem exists_units_map_eq_of_mem_fixedField {K K' : Type} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] {L L' : FiniteGaloisIntermediateField K K'}
    (hh : (L : IntermediateField K K') ≤ (L' : IntermediateField K K')) (x : (↥L')ˣ)
    (hx : ∀ σ : K' ≃ₐ[K] K', σ ∈ (L : IntermediateField K K').fixingSubgroup →
      σ ((x : ↥L') : K') = ((x : ↥L') : K')) :
    ∃ v : (↥L)ˣ, Units.map (IntermediateField.inclusion hh).toMonoidHom v = x := by
  have hmem : ((x : ↥L') : K') ∈ (L : IntermediateField K K') := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (L : IntermediateField K K')]
    rw [IntermediateField.mem_fixedField_iff]
    exact fun σ hσ => hx σ hσ
  refine ⟨Units.mk0 (⟨((x : ↥L') : K'), hmem⟩ : ↥L) ?_, ?_⟩
  · intro h
    have h1 : ((x : ↥L') : K') = 0 := by
      simpa using congrArg (fun z : ↥L => (z : K')) h
    exact Units.ne_zero x (Subtype.ext h1)
  · apply Units.ext
    apply Subtype.ext
    rfl

end NK.NUV2.ABHN
