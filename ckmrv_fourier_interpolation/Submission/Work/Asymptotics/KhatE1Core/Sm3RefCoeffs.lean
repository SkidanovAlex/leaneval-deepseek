import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Sm2RefCoeffs

/-!
# The `Sm3Ref` `q`-expansion

`Sm3Ref = 3456 R₀(E4Ref³·S0 - E6Ref·E2SRef·I4zRef)` is a polynomial in `q` of degree `6`, and
this module fixes its full coefficient list.  Cross-checked coefficient by coefficient against
the reference definitions (`E4Ref³ = 1 + 720q + 179280q² + 16934400q³ + 387244800q⁴ +
3359232000q⁵ + 10077696000q⁶`, `E2SRef = S0 - 24q - 72q²`, `E6Ref = 1 - 504q - 16632q²`,
`I4zRef = 1 - 240q + 55440q²`): the `q⁰` part vanishes *exactly* (`S0 - S0` — the leading
`S0` of `E4Ref³·S0` against that of `E6Ref·E2SRef·I4zRef`), so `Sm3Ref` starts at `q¹`, i.e. at
`E²`, as the cusp expansion of `E₆E₂ˢ/E₄` requires.

The `q¹` (= `E²`) coefficient is `3456 R₀(24 + 1464·S0) = 82944 R₀ + 5059584 R₀·S0`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- **The `Sm3Ref` `q`-expansion** (degree `6`, the full coefficient list). -/
lemma Sm3Ref_qexp (τ z : ℍ) :
    Sm3Ref τ z
      = Work.Kernels.qParamFun z
          * (3456 * Work.Asymptotics.K24F.R0 τ
              * (24 + 1464 * Work.Asymptotics.K24F.S0 z))
        + (Work.Kernels.qParamFun z) ^ 2
            * (3456 * Work.Asymptotics.K24F.R0 τ
                * (-17784 + 19512 * Work.Asymptotics.K24F.S0 z))
        + (Work.Kernels.qParamFun z) ^ 3
            * (3456 * Work.Asymptotics.K24F.R0 τ
                * (3780864 + 40884480 * Work.Asymptotics.K24F.S0 z))
        + (Work.Kernels.qParamFun z) ^ 4
            * (3456 * Work.Asymptotics.K24F.R0 τ
                * (-563298624 + 1309322880 * Work.Asymptotics.K24F.S0 z))
        + (Work.Kernels.qParamFun z) ^ 5
            * (3456 * Work.Asymptotics.K24F.R0 τ
                * (-23854279680 + 3359232000 * Work.Asymptotics.K24F.S0 z))
        + (Work.Kernels.qParamFun z) ^ 6
            * (3456 * Work.Asymptotics.K24F.R0 τ
                * (-66389621760 + 10077696000 * Work.Asymptotics.K24F.S0 z)) := by
  have hS0 : Work.Asymptotics.KhatE1.S0z z = Work.Asymptotics.K24F.S0 z := rfl
  simp only [Sm3Ref, E4Ref, E6Ref, E2SRef, I4zRef]
  rw [hS0]
  ring

end

end Work.Asymptotics.KhatE1Core
