import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Sm1RefCoeffs

/-!
# The `Sm2Ref` `q`-expansion

`Sm2Ref τ z = j(τ)·Φ_ref·(24q - 252q²)` is already a polynomial in `q` of degree `2` — the
`Sm2` reference is the one place where the truncation of `Δ(z)` enters at a *fixed* small order
(`1 - Δ(z)/q ≈ 24q - 252q²`), so nothing has to be recomputed:

  `Sm2Ref = 24·j(τ)Φ_ref·q - 252·j(τ)Φ_ref·q²`,

and its coefficient list is therefore exactly `(0, 24·j(τ)Φ_ref, -252·j(τ)Φ_ref)`.  In
particular the `E²`-coefficient of the `Sm2` reference is `24·j(τ)·Φ_ref` (`(24 : ℂ)` times
`Sm2Ref`'s own data — the `q`-degree-1 slot is the `E²` slot because `KPlus24Ref` is even).

**Next.**  `Sm3Ref = 3456 R₀ (E4Ref³·S0 - E6Ref·E2SRef·I4zRef)` and
`Sm4Ref = 1728 r₀E2SRef² + 1728 r₂E4Ref - Uref·E4Ref³` are polynomials in `q` of degree `6` and
are the two that need an explicit coefficient list (computed from the reference definitions:
`E4Ref³ = 1 + 720q + 179280q² + 16934400q³ + 387244800q⁴ + 3359232000q⁵ + 10077696000q⁶`,
`E2SRef² = S0² - 48S0q + (576-144S0)q² + 3456q³ + 5184q⁴`).  Their `q¹` coefficients are
`Sm3Ref`: `3456 R₀(720·S0 + 24 + 744·S0) = 82944 R₀ + 5059584 R₀S0`, and
`Sm4Ref`: `-82944 r₀S0 + 414720 r₂ - 720·Uref`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- **The `Sm2Ref` `q`-expansion** (degree `2`, so this is its full coefficient list). -/
lemma Sm2Ref_qexp (τ z : ℍ) :
    Sm2Ref τ z
      = Work.Kernels.qParamFun z
          * (24 * Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Phiref τ z)
        + (Work.Kernels.qParamFun z) ^ 2
            * (-252 * Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Phiref τ z) := by
  simp only [Sm2Ref]
  ring

/-- The `E²`-coefficient of the `Sm2` reference, read off from `Sm2Ref_qexp`. -/
lemma Sm2Ref_E2 (τ z : ℍ) :
    Sm2Ref τ z - Work.Kernels.qParamFun z
        * (24 * Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Phiref τ z)
      = (Work.Kernels.qParamFun z) ^ 2
          * (-252 * Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Phiref τ z) := by
  rw [Sm2Ref_qexp τ z]; ring

end

end Work.Asymptotics.KhatE1Core
