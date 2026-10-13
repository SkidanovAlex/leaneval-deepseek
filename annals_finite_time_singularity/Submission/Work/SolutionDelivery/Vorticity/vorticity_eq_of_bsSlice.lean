import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SolutionDelivery.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Vorticity

/-- **The vorticity of the constructed solution is the given field.**  On the window the
Biot–Savart dictionary `hbs` identifies each velocity slice `u(·,t)` with `BS(ω(·,t))`; for an
integrable, bounded, divergence-free vorticity slice the Biot–Savart law `hLaw` then says that
the curl of that field is the slice itself. -/
theorem vorticity_eq_of_bsSlice {u ω : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3} {T : ℝ}
    (hLaw : Work.LWP.BiotSavartLaw)
    (hbs : Work.StabilityFar.IsBiotSavartSlice u ω T)
    (hint : ∀ t ∈ Work.StabilityFar.window T, MeasureTheory.Integrable (fun y : Work.SolutionDelivery.R3 => ω y t))
    (hbdd : ∀ t ∈ Work.StabilityFar.window T, IsBoundedFun (fun y : Work.SolutionDelivery.R3 => ω y t))
    (hdiv : ∀ t ∈ Work.StabilityFar.window T, FiniteTimeSingularity.div (fun y : Work.SolutionDelivery.R3 => ω y t) = 0) :
    ∀ t ∈ Work.StabilityFar.window T, ∀ x : Work.SolutionDelivery.R3,
      FiniteTimeSingularity.vorticity (fun y => u y t) x = ω x t := by
  intro t ht x
  have hslice : (fun y => u y t) = Work.LWP.biotSavart (fun y => ω y t) :=
    funext (fun y => hbs t ht y)
  rw [hslice]
  exact Work.LWP.vorticity_biotSavart hLaw (hint t ht) (hbdd t ht)
    (fun y => congrFun (hdiv t ht) y) x

end Work.SolutionDelivery.Vorticity
