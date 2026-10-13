/-
# `Work.SolutionDelivery.HolderInputs` — the two time-Hölder constants `H`, `H₁`

`Work.StabilityFar.AssemblyInputs` asks for the time-`α`-Hölder constants of `ω` and `∂ₜω` on the
support ball — the two inputs of the far-field `α`-Hölder estimate `St4`.  Both are derived here
from the *single* hypothesis `ConstructedSolution.hωcore` (the core `C^{1,α}` regularity of `ω` on
`coreRegion (R+1) × extWindow T`):

* `H` from the mean value inequality in `t` (a Lipschitz bound, which for `α ≤ 1` is `α`-Hölder);
* `H₁` from the `α`-Hölder bound on the derivative, evaluated on the time block `(0,1)`.
-/
import Mathlib.Basic.ENNReal.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Order.Filter.Defs
import Submission.Work.SolutionDelivery.Slices
import Submission.Work.SolutionDelivery.Holder.timeHolderOnBall_of_isContDiffHolderOn
import Submission.Work.SolutionDelivery.Holder.timeHolderOnBall_timeDeriv_of_isContDiffHolderOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

variable {α : NNReal}

namespace ConstructedSolution

variable (C : ConstructedSolution α)

/-- **The time-Hölder constant `H` of `AssemblyInputs`.** -/
theorem exists_timeHolder (hα1 : (α : ℝ) ≤ 1) :
    ∃ H : ℝ, 0 ≤ H ∧ Work.StabilityFar.TimeHolderOnBall (α : ℝ) C.ω C.R C.T H :=
  Holder.timeHolderOnBall_of_isContDiffHolderOn (ρ := C.R + 1) (R := C.R) (T := C.T)
    (lt_add_one C.R) hα1 C.hωcore

/-- **The time-Hölder constant `H₁` of `AssemblyInputs`.** -/
theorem exists_timeHolder_timeDeriv :
    ∃ H₁ : ℝ, 0 ≤ H₁ ∧
      Work.StabilityFar.TimeHolderOnBall (α : ℝ) (timeDeriv C.ω) C.R C.T H₁ :=
  Holder.timeHolderOnBall_timeDeriv_of_isContDiffHolderOn (ρ := C.R + 1) (R := C.R) (T := C.T)
    (lt_add_one C.R) C.hωcore

end ConstructedSolution

end Work.SolutionDelivery
