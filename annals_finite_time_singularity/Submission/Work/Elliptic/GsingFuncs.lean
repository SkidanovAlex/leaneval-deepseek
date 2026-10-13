/-
The homogeneous factor of the singular term `G`, its first two derivatives, and the
explicit first/second derivative data of `Gstar` and `Gbar`.

`Gbar α F z = -(3/(4α)) z^{-5/α} J(z)` with `J(z) = ∫_0^z s^{(5-α)/α} F_*(s) ds`.  Since
`z^{-5/α}` is a homogeneous solution of the Euler equation `α²z²y'' + α(5+α)zy' = 0`
(the indicial roots are `0` and `-5/α`), the derivative bookkeeping is cleanest if this
factor is named.  All the functions below are the explicit values produced by the
differentiation rules: `DGstar`/`DGbar` are the first derivatives of `Gstar`/`Gbar`,
`DDGstar`/`DDGbar` the second ones.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

/-- The homogeneous factor `-(3/(4α)) z^{-5/α}` of `Gbar`. -/
def Abar (α : ℝ) (z : ℝ) : ℝ := -(3 / (4 * α)) * z ^ (-(5 / α))

/-- The derivative of `Abar`, with respect to `z`. -/
def DAbar (α : ℝ) (z : ℝ) : ℝ := (-(3 / (4 * α)) * (-(5 / α))) * z ^ (-(5 / α) - 1)

/-- The second derivative of `Abar`, with respect to `z`. -/
def DDAbar (α : ℝ) (z : ℝ) : ℝ :=
  (-(3 / (4 * α)) * (-(5 / α))) * ((-(5 / α) - 1) * z ^ (-(5 / α) - 1 - 1))

/-- The inner integral `J(z) = ∫_0^z s^{(5-α)/α} F_*(s) ds` of `Gbar`. -/
def Jfun (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..z, s ^ ((5 - α) / α) * Fstar F s

/-- The value of `(Gstar α F)'` at `z`, as a function of `z`. -/
def DGstar (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (-(1 / (4 * α))) * (-(3 * Fstar F z / z))

/-- The value of `(Gbar α F)'` at `z`, as a function of `z`. -/
def DGbar (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  DAbar α z * Jfun α F z + Abar α z * (z ^ ((5 - α) / α) * Fstar F z)

/-- The value of `(Gstar α F)''` at `z`, as a function of `z`. -/
def DDGstar (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (-(1 / (4 * α))) * (-(((3 * deriv (Fstar F) z) * z - 3 * Fstar F z) / z ^ 2))

/-- The value of `(Gbar α F)''` at `z`, as a function of `z`. -/
def DDGbar (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  DDAbar α z * Jfun α F z
    + DAbar α z * (z ^ ((5 - α) / α) * Fstar F z)
    + DAbar α z * (z ^ ((5 - α) / α) * Fstar F z)
    + Abar α z * (((5 - α) / α) * z ^ ((5 - α) / α - 1) * Fstar F z
        + z ^ ((5 - α) / α) * deriv (Fstar F) z)

end Work.Elliptic
