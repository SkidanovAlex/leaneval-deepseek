import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Sm3RefCoeffs

/-!
# The `Sm4Ref` `q`-expansion

`Sm4Ref = UfunRef - Uref·E4Ref³` (the `-Uref + Uref` cancels), and
`UfunRef = 1728 r₀·E2SRef² + 1728 r₂·E4Ref`, so `Sm4Ref` is a polynomial in `q` of degree `6`
with `Uref` (an explicit expression in `r₀, r₂, S0`) and `r₀, r₂, S0` as coefficient atoms.
The list below is cross-checked coefficient by coefficient against the reference definitions.

Its `q¹` (= `E²`) coefficient is `-82944 r₀S0 + 414720 r₂ - 720·Uref`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- **The `Sm4Ref` `q`-expansion** (degree `6`, the full coefficient list). -/
lemma Sm4Ref_qexp (τ z : ℍ) :
    Sm4Ref τ z
      = (1728 * Work.Asymptotics.K24F.r0 τ * (Work.Asymptotics.K24F.S0 z) ^ 2
          + 1728 * Work.Asymptotics.K24F.r2 τ - Work.Asymptotics.K24F.Uref τ z)
        + Work.Kernels.qParamFun z
            * (-82944 * Work.Asymptotics.K24F.r0 τ * Work.Asymptotics.K24F.S0 z
                + 414720 * Work.Asymptotics.K24F.r2 τ
                - 720 * Work.Asymptotics.K24F.Uref τ z)
        + (Work.Kernels.qParamFun z) ^ 2
            * (995328 * Work.Asymptotics.K24F.r0 τ
                - 248832 * Work.Asymptotics.K24F.r0 τ * Work.Asymptotics.K24F.S0 z
                + 3732480 * Work.Asymptotics.K24F.r2 τ
                - 179280 * Work.Asymptotics.K24F.Uref τ z)
        + (Work.Kernels.qParamFun z) ^ 3
            * (5971968 * Work.Asymptotics.K24F.r0 τ
                - 16934400 * Work.Asymptotics.K24F.Uref τ z)
        + (Work.Kernels.qParamFun z) ^ 4
            * (8957952 * Work.Asymptotics.K24F.r0 τ
                - 387244800 * Work.Asymptotics.K24F.Uref τ z)
        + (Work.Kernels.qParamFun z) ^ 5
            * (-3359232000 * Work.Asymptotics.K24F.Uref τ z)
        + (Work.Kernels.qParamFun z) ^ 6
            * (-10077696000 * Work.Asymptotics.K24F.Uref τ z) := by
  have hS0 : Work.Asymptotics.KhatE1.S0z z = Work.Asymptotics.K24F.S0 z := rfl
  simp only [Sm4Ref, UfunRef, E4Ref, E2SRef]
  rw [hS0]
  ring

end

end Work.Asymptotics.KhatE1Core
