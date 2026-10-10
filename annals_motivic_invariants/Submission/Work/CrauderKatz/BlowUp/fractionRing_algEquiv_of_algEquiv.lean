import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CrauderKatz.BlowUp

/-- A `𝕜`-algebra isomorphism of commutative rings induces a `𝕜`-algebra isomorphism of their
fraction fields (fraction rings `FractionRing = Localization (nonZeroDivisors _)`), with the standard
`𝕜`-algebra structures.

Route: `IsLocalization.algEquivOfAlgEquiv` (Mathlib, `RingTheory/Localization/Basic.lean`) applied to
`R = Q`, `P = Q'`, `M = nonZeroDivisors Q`, `T = nonZeroDivisors Q'`; the side condition
`Submonoid.map φ (nonZeroDivisors Q) = nonZeroDivisors Q'` follows from `Submonoid.ext` since a ring
equivalence carries nonzerodivisors to nonzerodivisors. -/
theorem fractionRing_algEquiv_of_algEquiv {𝕜 Q Q' : Type} [Field 𝕜] [CommRing Q] [CommRing Q']
    [Algebra 𝕜 Q] [Algebra 𝕜 Q'] (φ : Q ≃ₐ[𝕜] Q') :
    Nonempty (FractionRing Q ≃ₐ[𝕜] FractionRing Q') :=
  ⟨IsFractionRing.algEquivOfAlgEquiv φ⟩

end Work.CrauderKatz.BlowUp
