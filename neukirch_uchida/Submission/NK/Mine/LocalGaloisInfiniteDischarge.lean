import Submission.NK.Mine.infinite_gal_adicCompletion
import Submission.NK.LocalDecomposition.All

/-!
# The input `NK.LocalDecomposition.LocalGaloisInfinite` is a theorem

`NK.LocalDecomposition.localDecompositionCriterion_of_localKorollar1` (Route III of Neukirch's
criterion) takes five inputs, one of which is `NK.LocalDecomposition.LocalGaloisInfinite κ κ'`, the
statement that the absolute Galois group of a `p`-adic field `κ` is infinite.  Since a `p`-adic
field has extensions of every degree (`NK.Mine.infinite_gal_adicCompletion`, proved by a colleague
from the Eisenstein polynomial `T ^ n - π`), this input is discharged here.
-/

namespace NK.Mine

universe u

/-- **`LocalGaloisInfinite` for a completion.**  Immediate from
`NK.Mine.infinite_gal_adicCompletion`. -/
theorem localGaloisInfinite_adicCompletion {K : Type u} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L : Type u) [Field L] [Algebra (𝔭.adicCompletion K) L]
    [IsSepClosure (𝔭.adicCompletion K) L] :
    NK.LocalDecomposition.LocalGaloisInfinite (𝔭.adicCompletion K) L :=
  infinite_gal_adicCompletion 𝔭 L

end NK.Mine
