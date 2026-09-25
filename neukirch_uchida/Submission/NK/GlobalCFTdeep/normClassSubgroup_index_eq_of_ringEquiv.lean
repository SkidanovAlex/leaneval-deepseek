import Mathlib
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.GlobalCFTdeep.Transport.NormGroupTransport

namespace NK.GlobalCFTdeep

/-- **The norm index is invariant under ring equivalences of number fields** (universe
polymorphic, as advised by the review).  If `eK : K ≃+* K'` and `eL : L ≃+* L'` are ring
equivalences of number fields compatible with the algebra maps
(`eL ∘ algebraMap K L = algebraMap K' L' ∘ eK`), then

  `[C_K : N_{L/K}C_L] = [C_{K'} : N_{L'/K'}C_{L'}]`.

Every object in the construction (`Place`, completions, local unit groups, `𝕀`, `normIdeleFun`,
`normImage`, `normClassSubgroup`) is functorial under such an equivalence, so there is an
isomorphism of the quotients `C_K ⧸ N_{L/K}C_L ≃* C_{K'} ⧸ N_{L'/K'}C_{L'}`, and the index is
`Nat.card` of that quotient.  This is the *bridge* that lets the `Type 0` arithmetic results of this
chapter be transported to number fields in any universe `Type u`: a number field `K : Type u` is
countable, hence equivalent to a `Type 0` model (`Shrink.{u,0} K`), and the field/number-field
structure is transported along that equivalence (Mathlib's `Function.Injective.field` and friends).
The analogous transport along `ULift` is carried out in
`NK.UniverseUnify/ringOfIntegersULiftEquiv.lean`, `heightOneSpectrumULift.lean`. -/
theorem normClassSubgroup_index_eq_of_ringEquiv {K L K' L' : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [Field K'] [NumberField K']
    [Field L'] [NumberField L'] [Algebra K' L'] [FiniteDimensional K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x)) :
    (NK.GlobalCFT.Idele.normClassSubgroup K L).index =
      (NK.GlobalCFT.Idele.normClassSubgroup K' L').index :=
  NK.GlobalCFTdeep.Transport.normClassSubgroup_index_eq eK eL hcomp

end NK.GlobalCFTdeep
