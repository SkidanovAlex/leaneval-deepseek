import Mathlib
import Submission.NK.LocalStructure.Defs
import Submission.NK.LocalStructure.Power.natCard_pRootsOfUnity_eq_pow_zetaIndicator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalStructure.Power

open scoped Classical Pointwise
open IsDedekindDomain.HeightOneSpectrum

/-- **The `p`-power class count of the principal units, in the form consumed by the local
structure theory.**  From the reduced input `PrincipalUnitsCore` — which records
`U¹/(U¹)^p ≅ (ℤ/p)^{[κ:ℚ_p]} × μ_p(κ)`, the `p`-adic logarithm structure of `U¹ = 1 + 𝔪` — and
the order `#μ_p(κ) = p^δ` of the `p`-torsion (`δ = zetaIndicator p κ` the indicator of
`ζ_p ∈ κ`), the order of the `p`-th power quotient of the principal units of `κ = K_𝔭` is
`p ^ ([κ : ℚ_p] + δ)`. -/
theorem principalUnits_card_of_core {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (h : NK.LocalStructure.PrincipalUnitsCore K 𝔭 p) :
    Nat.card (↥(NK.LocalInputs.principalUnits K 𝔭) ⧸ (powMonoidHom p).range) =
      p ^ (NK.LocalInputs.localDegree K 𝔭 +
        NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K)) := by
  rw [h.quot_torsion,
    natCard_pRootsOfUnity_eq_pow_zetaIndicator p (𝔭.adicCompletion K) h.hp,
    ← pow_add]

end NK.LocalStructure.Power
