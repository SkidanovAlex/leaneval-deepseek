import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.LocalInputs.CommGroupRank.hasFrattiniRank_of_natCard_quot_powSubgroup
import Submission.NK.LocalInputs.Instantiation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalInputs

noncomputable section

/-- **The `p`-Frattini rank of the unit group of `K_𝔭`** is `[K_𝔭 : ℚ_p] + 1 + δ`, where
`δ = 1` iff `ζ_p ∈ K_𝔭`.  From the power-class count of part (1) alone. -/
theorem hasFrattiniRank_units_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hF : LocalFieldInputs K 𝔭 p) :
    NK.LocalAnabelian.HasFrattiniRank p
      (localDegree K 𝔭 + 1 + zetaIndicator p (𝔭.adicCompletion K))
      (𝔭.adicCompletion K)ˣ :=
  NK.LocalInputs.CommGroupRank.hasFrattiniRank_of_natCard_quot_powSubgroup hF.hp
    (natCard_KummerGroup_adicCompletion_eq_pow 𝔭 hF)

end

end NK.LocalInputs
