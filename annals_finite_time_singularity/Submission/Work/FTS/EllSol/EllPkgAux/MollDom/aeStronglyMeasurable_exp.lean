import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

/-- The half-strip `ℝ × (0, π/2)` is of full measure for the product measure
`volume.prod (volume.restrict Iθ)`: inside `Iθ = [0, π/2]` the complement of `(0, π/2)` consists
of the two endpoints `0`, `π/2`, which are null. -/
theorem ae_mem_halfStrip :
    ∀ᵐ (p : ℝ × ℝ) ∂(MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      p ∈ ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
  have hIθ : (MeasureTheory.volume.restrict Work.Spaces.Iθ : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    show (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (π / 2)) : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2))
    exact (MeasureTheory.restrict_Ioo_eq_restrict_Icc (μ := MeasureTheory.volume)
      (a := (0 : ℝ)) (b := π / 2)).symm
  rw [MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
    (MeasurableSet.univ.prod (measurableSet_Ioo (a := (0 : ℝ)) (b := π / 2)))]
  filter_upwards with x
  rw [hIθ]
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioo (a := (0 : ℝ)) (b := π / 2))]
    with y hy
  exact ⟨trivial, hy⟩

theorem aeStronglyMeasurable_exp {X : ℝ → ℝ → ℝ}
    (hX : ContinuousOn (Function.uncurry X) Work.FTS.EllipticEst.Q0) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- the (measurable, co-null) half-strip on which the datum is continuous
  have hmeasS : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    MeasurableSet.univ.prod (measurableSet_Ioo (a := (0 : ℝ)) (b := π / 2))
  -- on that half-strip the datum is continuous: the map `p ↦ (exp p.1, p.2)` is continuous and
  -- sends the half-strip into the open quadrant `Q0` on which `X` is continuous
  have hcont : ContinuousOn (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
    have hφ : Continuous (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) :=
      (Real.continuous_exp.comp continuous_fst).prodMk continuous_snd
    have h : ContinuousOn ((Function.uncurry X) ∘ (fun p : ℝ × ℝ => (Real.exp p.1, p.2)))
        ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
      hX.comp hφ.continuousOn (fun p hp => ⟨Real.exp_pos p.1, (Set.mem_prod.mp hp).2⟩)
    exact h
  rw [← MeasureTheory.Measure.restrict_eq_self_of_ae_mem ae_mem_halfStrip]
  exact hcont.aestronglyMeasurable hmeasS

end Work.FTS.EllSol.EllPkgAux.MollDom
