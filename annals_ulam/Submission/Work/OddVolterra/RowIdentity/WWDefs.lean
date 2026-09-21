import Mathlib
import Submission.Work.OddVolterra.RowIdentity.Basic

/-!
# The smooth factor `B` of the swept integrand

The swept integrand of the odd row identity is

`Wint n h x y u σ = (σ - u)^{n+1/2} · B n h x y u σ`,

where the *smooth* factor `B` collects the two frozen endpoint contributions

`B u σ = (Qy h y u σ)^{n+1/2}·(-(deriv y σ)) + (Qx h x u σ)^{n+1/2}·(-(deriv x σ))`.

This file only introduces `Bfun` (and the substitution form `WintSub`), so that later files
-- including parallel work on the smoothness of `WW` -- can refer to them.
-/

namespace Work.OddVolterra.RowIdentity

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- The smooth factor `B u σ` of the swept integrand `Wint`. -/
def Bfun (n : ℕ) (h x y : ℝ → ℝ) (u σ : ℝ) : ℝ :=
  (Qy h y u σ) ^ ((n : ℝ) + 1 / 2) * (-(deriv y σ))
    + (Qx h x u σ) ^ ((n : ℝ) + 1 / 2) * (-(deriv x σ))

/-- The swept integrand factors as `(σ-u)^{n+1/2} · Bfun u σ`. -/
lemma Wint_eq_mul_Bfun (n : ℕ) (h x y : ℝ → ℝ) (u σ : ℝ) :
    Wint n h x y u σ = (σ - u) ^ ((n : ℝ) + 1 / 2) * Bfun n h x y u σ := rfl

/-- The integrand of the substituted swept integral, in the variable `θ` with
`σ = u + θ² (1 - u)`. -/
def WintSub (n : ℕ) (h x y : ℝ → ℝ) (u θ : ℝ) : ℝ :=
  2 * θ ^ (2 * n + 2) * Bfun n h x y u (u + θ ^ 2 * (1 - u))

/-- The substituted integrand is `Bfun` evaluated at `σ = u + θ² (1-u)`, times `2θ^{2n+2}`. -/
lemma WintSub_eq (n : ℕ) (h x y : ℝ → ℝ) (u θ : ℝ) :
    WintSub n h x y u θ
      = 2 * θ ^ (2 * n + 2) * Bfun n h x y u (u + θ ^ 2 * (1 - u)) := rfl

end

end Work.OddVolterra.RowIdentity
