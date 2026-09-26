import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.KdevA4
import Submission.Work.Asymptotics.KhatE1Defs

/-!
# The `K₋` block of the `E(z)^4` read-off

The `K₋` half of `3456π·KdevA4` is `Xc·R8_q3 + R8_p3 + [Tref8]_{e^4} + [Dev8Sum]_{e^4}`; below,
`Kminus4` is that bracket in the `KdevA4` spelling, and the RHS is its normal form under the two
substitutions `ψ₄ → Φ + P` and `j(τ)·Φ → E1combo8 - 1152E₄(τ) + 576ψ₄` (engine-generated,
`.kdevdir/a4leanB.txt`).  There is no `tailC` here, so no `zpow`/`Complex.I` side conditions. -/
namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

open Work.Kernels

/-- **The `K₋` block in the `KdevA4` spelling equals its normal form.** -/
theorem Kminus4_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane)
    (hΔ : DeltaFun τ ≠ 0) (hE4 : E4Fun τ ≠ 0) :
    ((10948608 * E4Fun τ + 19906560 * psi4 ℓ τ
                + 61056 * (jInvariantFun τ * psi4 ℓ τ)
                - 61056 * (psi2 ℓ τ * E14Fun τ / DeltaFun τ)
              + (jInvariantFun τ - 720)
                * (-41472 * E4Fun τ + 912384 * Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ
                  + 870912 * psi4 ℓ τ
                  + 1152 * (psi2 ℓ τ * E14Fun τ / DeltaFun τ)
                  - 1152 * (jInvariantFun τ * psi4 ℓ τ)))
            + (((jInvariantFun τ - 720) ^ 2 - 179280 - 24 * jInvariantFun τ)
                * (-3456 * Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ + 1728 * psi4 ℓ τ))
            + Work.Asymptotics.KhatE1Core.Dev4 ℓ τ z)
      =
    - (1360862208 : ℂ) * (Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ)
    + (1017536256 : ℂ) * (E4Fun τ)
    - (847872 : ℂ) * (Work.Asymptotics.E1combo8 ℓ τ)
    - (488374272 : ℂ) * (psi4 ℓ τ)
    + (85888512 : ℂ) * ((psi2 ℓ τ * E6Fun τ / E4Fun τ))
    + (85888512 : ℂ) * ((psi4 ℓ τ - psi2 ℓ τ * E6Fun τ / E4Fun τ))
    + (5971968 : ℂ) * (Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ * jInvariantFun τ)
    - (705024 : ℂ) * (E4Fun τ * jInvariantFun τ)
    + (576 : ℂ) * (jInvariantFun τ * Work.Asymptotics.E1combo8 ℓ τ)
    + (331776 : ℂ) * (jInvariantFun τ * psi4 ℓ τ)
    - (1658880 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E6Fun τ / E4Fun τ))
    - (3456 : ℂ) * (Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ * jInvariantFun τ * jInvariantFun τ)
    + (1728 : ℂ) * (jInvariantFun τ * jInvariantFun τ * (psi2 ℓ τ * E6Fun τ / E4Fun τ)) := by
  rw [Work.Asymptotics.E1combo8, Work.Asymptotics.KhatE1Core.Dev4]
  field_simp
  ring

end

end Work.Asymptotics.KhatE1Core
