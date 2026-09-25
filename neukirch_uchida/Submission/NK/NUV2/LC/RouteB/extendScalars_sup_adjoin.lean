import Mathlib

namespace NK.NUV2.LC.RouteB

/-- For an intermediate field `L` of `K'/F` and a subset `s ⊆ K'`, the compositum
`L ⊔ F(s)` (viewed as an intermediate field of `K'/L` via `extendScalars`) equals the
intermediate field `L(s)` generated over `L` by `s`.

This is the standard "adjoin is associative in the base" statement, recorded in Mathlib as
`IntermediateField.restrictScalars_adjoin_eq_sup`; taking `restrictScalars F` of both sides is
injective. -/
theorem extendScalars_sup_adjoin {F K' : Type} [Field F] [Field K'] [Algebra F K']
    (L : IntermediateField F K') (s : Set K') :
    IntermediateField.extendScalars (F := L) (E := L ⊔ IntermediateField.adjoin F s) le_sup_left =
      IntermediateField.adjoin ↥L s := by
  apply IntermediateField.restrictScalars_injective F
  rw [IntermediateField.extendScalars_restrictScalars,
    IntermediateField.restrictScalars_adjoin_eq_sup]

end NK.NUV2.LC.RouteB
