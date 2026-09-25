import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Order.CompletePartialOrder

set_option linter.style.haveILetI false

namespace Commons.FieldTheory.Galois

/-- In characteristic zero, a compositum (supremum) of Galois intermediate fields
is Galois: the sup is algebraic (a compositum of algebraic extensions) hence
separable over the characteristic-zero base, and normal by
`IntermediateField.normal_iSup`. -/
theorem isGalois_iSup_of_charZero {F K : Type*} [Field F] [CharZero F] [Field K] [Algebra F K]
    {ι : Type*} (E : ι → IntermediateField F K) [∀ i, IsGalois F ↥(E i)] :
    IsGalois F ↥(⨆ i, E i) := by
  rw [isGalois_iff]
  constructor
  · -- separability: each `E i` is algebraic over `F` (normality implies algebraicity),
    -- so the compositum is algebraic, hence (in characteristic zero) separable.
    haveI hAlg : ∀ i, Algebra.IsAlgebraic F ↥(E i) :=
      fun i => (inferInstance : Normal F ↥(E i)).toIsAlgebraic
    haveI : Algebra.IsAlgebraic F ↥(⨆ i, E i) := IntermediateField.isAlgebraic_iSup hAlg
    infer_instance
  · -- normality of a compositum of normal extensions
    exact IntermediateField.normal_iSup F K E

end Commons.FieldTheory.Galois