/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `p`-Frattini rank of the unit group of a `p`-adic field

Part (1) of the deliverable computes the power-class group: `|κˣ/(κˣ)^p| = p^{d+1+δ}`.  For a
*commutative* group, the number of index-`p` subgroups is determined by `C/C^p`
(`NK.LocalInputs.CommGroupRank.hasFrattiniRank_of_natCard_quot_powSubgroup`), so the same
computation gives the `p`-Frattini rank of the unit group itself:

  `HasFrattiniRank p (d+1+δ) κˣ`.

Together with the compatibility of the index-`p` count with profinite completion
(`NK.LocalInputs.CommGroupRank.numIndexSubgroups_profiniteCompletion`:
`numIndexSubgroups p A^{∧} = numIndexSubgroups p A` for commutative `A`), this wires part (1) into
the abelian rank of part (3): see `NK.LocalInputs.InputsOfUnits`, where
`HasFrattiniRank p (d+1+δ) (NK.LocalReciprocity.completionUnits κ)` — the last input needed for
`NK.LocalInputs.hasAbelianFrattiniRank_of_lubinTate` — is *derived* from `LocalFieldInputs`.
-/
import Submission.NK.LocalInputs.Instantiation
import Submission.NK.LocalInputs.CommGroupRank.hasFrattiniRank_of_natCard_quot_powSubgroup
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
