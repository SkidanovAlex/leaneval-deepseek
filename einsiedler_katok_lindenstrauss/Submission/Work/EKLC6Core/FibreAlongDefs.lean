import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLComp.LeafDefs

/-!
# `Work.EKLC6Core.FibreAlongDefs`

The objects used by `Work.EKLC6Core.fiber_leafwise_along` and by the lemmas it is proved from:
the diagonal map `x ↦ aDiag t • x`, its invariant σ-algebra, the fibre measures
`condExpKernel μ (invariants (aDiag t ·)) x`, and the `ν`-average over the plaque of an
`m`-atom that occurs on the right-hand side of the `condexp` field of `IsLeafwise`.
-/

open MeasureTheory ProbabilityTheory

set_option linter.unusedVariables false
set_option warn.classDefReducibility false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The diagonal map `x ↦ aDiag t • x`. -/
def diagMap (t : Fin 3 → ℝ) : X3 → X3 := fun x => aDiag t • x

/-- The invariant σ-algebra of `diagMap t`. -/
def invSig (t : Fin 3 → ℝ) : MeasurableSpace X3 := MeasurableSpace.invariants (diagMap t)

/-- The fibre measures of `μ` over `invSig t`: the conditional kernel of `μ` on the σ-algebra of
`diagMap t`-invariant sets. -/
def fibre (μ : Measure X3) [IsFiniteMeasure μ] (t : Fin 3 → ℝ) : X3 → Measure X3 :=
  fun x => condExpKernel μ (invSig t) x

/-- The `ν`-average over the plaque of the `m`-atom of a point, which is the right-hand side of
the `condexp` field of `IsLeafwise`. -/
def nuAvg (U : Subgroup SL3) (ν : X3 → Measure SL3) (m : MeasurableSpace X3) (f : X3 → ℝ) :
    X3 → ℝ :=
  fun y => (∫ u in shape m U y, f (u • y) ∂(ν y)) / ((ν y) (shape m U y)).toReal

/-- Borel measurability of a real-valued function on `X₃`, with the σ-algebra pinned: writing the
hypothesis as `Measurable f` inside a context in which a local variable `m : MeasurableSpace X₃`
is in scope silently elaborates to `Measurable[m] f`, so the pinned form is used instead. -/
def BorelMeas (f : X3 → ℝ) : Prop := Measurable[instMeasurableSpaceX3] f

@[simp] theorem diagMap_def (t : Fin 3 → ℝ) : diagMap t = fun x : X3 => aDiag t • x := rfl

@[simp] theorem invSig_def (t : Fin 3 → ℝ) :
    invSig t = MeasurableSpace.invariants (fun x : X3 => aDiag t • x) := rfl

@[simp] theorem fibre_def (μ : Measure X3) [IsFiniteMeasure μ] (t : Fin 3 → ℝ) (x : X3) :
    fibre μ t x = condExpKernel μ (MeasurableSpace.invariants
      (fun x : X3 => aDiag t • x)) x := rfl

@[simp] theorem nuAvg_def (U : Subgroup SL3) (ν : X3 → Measure SL3) (m : MeasurableSpace X3)
    (f : X3 → ℝ) (y : X3) :
    nuAvg U ν m f y = (∫ u in shape m U y, f (u • y) ∂(ν y))
      / ((ν y) (shape m U y)).toReal := rfl

end Work.EKLC6Core
