/-
# `Work.EllipticEst.ModalSolution.RadGreenWeak.Defs`

Notation for the weak (self-adjointness) identity of the radial Green's function
`Work.FTS.PhiStar.Radial.radGreen α m c`:

```
∫_{z>0} radGreen α m c z · (L ψ)(z) · z^q + lamR m · ∫_{z>0} radGreen α m c z · ψ z · z^q
  = ∫_{z>0} c z · ψ z · z^q
```

where `q = (5-α)/α`, `L u = -(α²z²u'' + α(5+α)zu')`, and `radGreen` is the explicit decaying
solution of `L a + lamR m · a = c`,

```
radGreen α m c z = 1/(α(4m+5)) · ( z^{s⁻} ∫_0^z c t t^{-1-s⁻} dt
                                  + z^{s⁺} ∫_z^∞ c t t^{-1-s⁺} dt )
```

with `s⁺ = 2m/α`, `s⁻ = -(2m+5)/α`.

The weight `z^q` is exactly the one for which `L` is formally self-adjoint:
`(α² z² z^q)' = α(5+α) z z^q`, i.e. `α²(q+2) = α(5+α)`.  This file only collects the
notation shared by the pieces of the proof of `radGreen_weak_ode_le1`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution.RadGreenWeak

set_option autoImplicit false

/-- The growing indicial exponent `s⁺ = 2m/α` of the mode-`m` radial operator. -/
def sP (α : ℝ) (m : ℕ) : ℝ := 2 * (m : ℝ) / α

/-- The decaying indicial exponent `s⁻ = -(2m+5)/α` of the mode-`m` radial operator. -/
def sM (α : ℝ) (m : ℕ) : ℝ := -(2 * (m : ℝ) + 5) / α

/-- The weight exponent `q = (5-α)/α`. -/
def qW (α : ℝ) : ℝ := (5 - α) / α

/-- The weight `w(z) = z^q`, `q = (5-α)/α`. -/
def wgt (α : ℝ) (z : ℝ) : ℝ := z ^ qW α

/-- The radial part of `bslOp`: `(L u)(z) = -(α²z²u''(z) + α(5+α)z u'(z))`. -/
def Lneg (α : ℝ) (u : ℝ → ℝ) (z : ℝ) : ℝ :=
  -(α ^ 2 * z ^ 2 * deriv (deriv u) z + α * (5 + α) * z * deriv u z)

/-- The Lagrange coefficient `p(z) = α² z² w(z) = α² z^{q+2}`. -/
def pwt (α : ℝ) (z : ℝ) : ℝ := α ^ 2 * (z ^ 2 * wgt α z)

/-- The lower source kernel of `radGreen`: `t ↦ c t · t^{-1-s⁻} = c t · t^{(2m+5)/α-1}`. -/
def srcM (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (t : ℝ) : ℝ :=
  c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)

/-- The upper source kernel of `radGreen`: `t ↦ c t · t^{-1-s⁺} = c t · t^{-2m/α-1}`. -/
def srcP (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (t : ℝ) : ℝ :=
  c t * t ^ (-(2 * (m : ℝ) / α) - 1)

/-- `Φ = L ψ + lamR m · ψ`: the "test function" of the weak identity. -/
def PhiF (α : ℝ) (m : ℕ) (ψ : ℝ → ℝ) (z : ℝ) : ℝ :=
  Lneg α ψ z + Work.FTS.PhiStar.Radial.lamR m * ψ z

/-- `radGreen` in the notation of this development (definitional). -/
lemma radGreen_eq (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m c z
      = 1 / (α * (4 * (m : ℝ) + 5)) *
          (z ^ sM α m * (∫ t in (0 : ℝ)..z, srcM α m c t)
            + z ^ sP α m * (∫ t in Set.Ioi z, srcP α m c t)) := rfl

end Work.EllipticEst.ModalSolution.RadGreenWeak
