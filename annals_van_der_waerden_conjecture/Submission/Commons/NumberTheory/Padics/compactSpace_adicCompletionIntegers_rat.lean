import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.ProperSpace

open IsDedekindDomain

/-!
# Compactness of the ring of integers of the adic completion of `ℚ`

For every height-one prime ideal `v` of `ℤ` (i.e. every rational prime `p`), the ring
`v.adicCompletionIntegers ℚ` of integers of the `v`-adic completion of `ℚ` is compact.

Indeed, Mathlib's `Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv` provides a
continuous `ℤ`-algebra isomorphism `v.adicCompletionIntegers ℚ ≃A[ℤ] ℤ_[p]`, and `ℤ_[p]`
is compact by `PadicInt.compactSpace`; compactness is transported back along the homeomorphism
`e.symm.toHomeomorph`.

The local priority boost of `Ring.toIntAlgebra` ensures that the typeclass synthesizer picks,
for the subtype `v.adicCompletionIntegers ℚ`, the same `Algebra ℤ` instance as the one fixed in
the statement of `padicIntEquiv`.
-/

attribute [local instance 2000] Ring.toIntAlgebra

namespace Commons.NumberTheory.Padics

noncomputable section

/-- The ring of integers of the `v`-adic completion of `ℚ` is compact. -/
theorem compactSpace_adicCompletionIntegers_rat (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    CompactSpace (v.adicCompletionIntegers ℚ) := by
  let e := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv (R := ℤ) v
  exact (e.symm.toHomeomorph.compactSpace)

end

end Commons.NumberTheory.Padics