import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.Aux2

open MeasureTheory Set
open scoped Topology

theorem gcJHasDeriv (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => ∫ y in s..(2 * N),
          Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ)
        (-(Real.exp (-(b * t)) * deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ)) t := by
  intro θ hθ t
  -- the `θ`-slice of `u` is continuous
  have hslice : Continuous fun y : ℝ => u y θ := by
    rw [continuous_iff_continuousAt]
    intro y
    have hpt : ContinuousAt (Function.uncurry u) (y, θ) :=
      hu.continuousOn.continuousAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨trivial, hθ⟩)
    have hmap : ContinuousAt (fun y' : ℝ => (y', θ)) y :=
      (Continuous.prodMk_left θ).continuousAt
    exact hpt.comp (f := fun y' : ℝ => (y', θ)) hmap
  have hchi : Continuous (deriv (Work.FTS.EllSol.Trunc.chi N)) :=
    (Work.FTS.EllSol.Trunc.chi_contDiff 1 N).continuous_deriv_one
  have hexp : Continuous fun y : ℝ => Real.exp (-(b * y)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id).neg
  have hcont : Continuous fun y : ℝ =>
      Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ :=
    (hexp.mul hchi).mul hslice
  exact intervalIntegral.integral_hasDerivAt_left
    (f := fun y : ℝ => Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ)
    (a := t) (b := 2 * N)
    (hcont.intervalIntegrable _ _) (hcont.stronglyMeasurableAtFilter volume (𝓝 t))
    hcont.continuousAt

end Work.FTS.EllSol.ShiftFT.Aux2
