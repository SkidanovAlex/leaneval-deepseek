/-
# `Work.ConstructionInstance.Meas` — the measurability of the self-similar vorticity

`Work.Cyl.eTheta` is *not* continuous at the axis (the factor `1/radial` has no limit), but it is
measurable: it is the product of the measurable scalar `1/radial` with the polynomial
`Work.Cyl.angularVec`.  Consequently the self-similar vorticity `omegaS p g = P • e_θ` is
`AEStronglyMeasurable` as soon as the *scalar* profile `P(x) = profile p g (ρ(x)^p, θ(x))` is.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

theorem measurable_radial : Measurable (fun x : R3 => Work.Cyl.radial x) := by
  have h : Measurable (fun x : R3 => Work.Cyl.radSq x) := by
    show Measurable (fun x : R3 => x 0 ^ 2 + x 1 ^ 2)
    fun_prop
  exact h.sqrt

theorem measurable_angularVec : Measurable (fun x : R3 => Work.Cyl.angularVec x) := by
  have h : Continuous fun x : R3 => Work.Cyl.angularVec x := by
    show Continuous fun x : R3 => WithLp.toLp 2 (![-x 1, x 0, 0] : Fin 3 → ℝ)
    fun_prop
  exact h.measurable

/-- `Work.Cyl.eTheta` is measurable (though not continuous). -/
theorem measurable_eTheta : Measurable (fun x : R3 => Work.Cyl.eTheta x) := by
  have hscal : Measurable (fun x : R3 => (1 : ℝ) / Work.Cyl.radial x) :=
    measurable_const.div measurable_radial
  have hfun : (fun x : R3 => Work.Cyl.eTheta x)
      = fun x : R3 => (1 / Work.Cyl.radial x) • Work.Cyl.angularVec x := rfl
  rw [hfun]
  exact hscal.smul measurable_angularVec

/-- **The self-similar vorticity is measurable** as soon as its scalar profile is. -/
theorem aestronglyMeasurable_omegaS {p : ℝ} {g : ℝ → ℝ → ℝ}
    (hP : AEStronglyMeasurable
      (fun x : R3 => profile p g (Work.Cyl.Rc p x) (Work.Cyl.theta x)) volume) :
    AEStronglyMeasurable (omegaS p g) volume := by
  have h := hP.smul (measurable_eTheta.aestronglyMeasurable (μ := volume))
  exact h

end Work.ConstructionInstance
