import Mathlib
import Submission.NK.LocalInputs.Inputs
import Submission.NK.LocalInputs.Defs
import Submission.NK.LocalStructure.Defs
import Submission.NK.LocalInputs.PowerQuotient.Setup
import Submission.NK.LocalInputs.PowerQuotient.natCard_pu_quot_pow

open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField WithZero

namespace NK.LocalInputs.PowerQuotient

/-- **The local arithmetic input, unconditionally.**

For a number field `K`, a finite prime `𝔭` and the prime `p` of the residue characteristic of the
completion `K_𝔭`, the arithmetic input `LocalFieldInputs K 𝔭 p` holds: the residue characteristic
is `p`, and the `p`-power quotient of the principal units `U¹ = 1 + 𝔪` has order
`p ^ ([K_𝔭 : ℚ_p] + δ)` with `δ = 1` iff `ζ_p ∈ K_𝔭`. -/
theorem localFieldInputs_of_prime {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    NK.LocalInputs.LocalFieldInputs K 𝔭 p := by
  obtain ⟨M, hM, hD⟩ := exists_logData (K := K) 𝔭
  obtain ⟨D⟩ := hD
  refine ⟨hp, hres, ?_⟩
  rw [← pu_one (K := K) 𝔭]
  exact natCard_pu_quot_pow (K := K) 𝔭 hp hres D

end NK.LocalInputs.PowerQuotient
