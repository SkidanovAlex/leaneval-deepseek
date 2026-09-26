import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.KPlus24Split
import Submission.Work.Residues.ThetaEpt

/-!
# The coefficient half, first piece: the `K₊` references as polynomials in `q`

`KPlus24Ref ℓ τ z = -(c·z²·(Sm1Ref + … + Sm5Ref))`, and every `*Ref` atom appearing in the
`Sm_iRef` is an *explicit polynomial in `q = qParamFun z`*:

  `E4Ref = 1 + 240q + 2160q²`,  `E6Ref = 1 - 504q - 16632q²`,  `E14Ref = 1 - 24q - 196632q²`,
  `I4Ref = 1 - 720q + 339120q²`,  `I4zRef = 1 - 240q + 55440q²`,
  `DqRef = 1 - 24q + 252q²`,  `DeltaRef = q·DqRef = q - 24q² + 252q³`,
  `E2SRef = S0z z - 24q - 72q²`.

The only obstruction to `KPlus24Ref` being a polynomial in `q` is the reference of `1/Δ` used in
`Sm1Ref`: `DeltaInvRef = q⁻¹ + 24` carries a `q⁻¹`, which cancels against the explicit factor
`q` in `q·DeltaInvRef - 1`.  That cancellation is `DeltaInvRef_mul_q` below.

**Parity.**  `S0z z`, `Q1`, `Phiref`, `Uref`, `Th0`, `R0`, `r0`, `r1`, `r2`, `j(τ)`, `(z:ℂ)` are
all `E`-free, and every `*Ref` atom above is even in `E = Ept z` (`q^j = E^{2j}`).  Hence
`KPlus24Ref` is **even in `E`**: its `E`-coefficients vanish at the odd orders, the `E^{2j}`
coefficient being the coefficient of `q^j`.  In particular the `E²` coefficient of the `K₊`
reference is the coefficient of `q¹` in its `q`-expansion, and `KPlus24Ref` is a polynomial in
`q` of degree at most `6` (the largest degree arising from products such as
`E4Ref³·S0`, `E6Ref·E2SRef·I4zRef`, `VfunRef·I4Ref`, `E4Ref³·Q1·(q·DeltaInvRef - 1)`).

**Next step.**  Expand each `Sm_iRef` in `q` (a finite `ring` computation against the definitions
above, done one `Sm_i` at a time in the same staged way as `Sm1Split`), collect the `q¹`
coefficients, and compare their sum against the corresponding part of `Bracket24E2'`.  The
`Sm5Ref` expansion below is the first instance of that move.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- `q · q⁻¹ = 1` for `q = qParamFun z`. -/
lemma q_mul_qinv (z : ℍ) :
    Work.Kernels.qParamFun z * (Work.Kernels.qParamFun z)⁻¹ = 1 :=
  mul_inv_cancel₀ (Work.Asymptotics.qParamFun_ne_zero' z)

/-- **The `1/Δ`-reference `q`-cancellation**: `q·DeltaInvRef - 1 = 24q`.  This is what makes
`q·DeltaInvRef - 1` (and hence `Sm1Ref`) a polynomial in `q`. -/
lemma DeltaInvRef_mul_q (z : ℍ) :
    Work.Kernels.qParamFun z * DeltaInvRef z - 1 = 24 * Work.Kernels.qParamFun z := by
  simp only [DeltaInvRef]
  rw [mul_add, q_mul_qinv z]
  ring

/-- `DeltaRef = q·(1 - 24q + 252q²)` (definitional), recorded in expanded `q`-form. -/
lemma DeltaRef_qexp (z : ℍ) :
    DeltaRef z = Work.Kernels.qParamFun z - 24 * (Work.Kernels.qParamFun z) ^ 2
      + 252 * (Work.Kernels.qParamFun z) ^ 3 := by
  simp only [DeltaRef, DqRef]; ring

/-- **The `Sm5Ref` `q`-expansion.**  `Sm5Ref = -(Δ_ref·j(τ))·Θ₀` with
`Δ_ref = q - 24q² + 252q³`; its `E²`-coefficient is the coefficient of `q¹`, namely
`-(j(τ)·Θ₀)` (and its `E⁴`-, `E⁶`-coefficients are `24·j(τ)Θ₀` and `-252·j(τ)Θ₀`). -/
lemma Sm5Ref_qexp (τ z : ℍ) :
    Sm5Ref τ z
      = Work.Kernels.qParamFun z
          * (-(Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Th0 τ z))
        + (Work.Kernels.qParamFun z) ^ 2
            * (24 * Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Th0 τ z)
        + (Work.Kernels.qParamFun z) ^ 3
            * (-252 * Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Th0 τ z) := by
  simp only [Sm5Ref, DeltaRef, DqRef]
  ring

end

end Work.Asymptotics.KhatE1Core
