import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A globally smooth chart map with prescribed value and derivative at a point

For a smooth manifold `M` modelled on `(E, H, I)` and a point `x : M`, there is a globally
smooth `g : M → E` with `g x = 0` and `mvfderiv I g x = mvfderiv I (extChartAt I x) x`.

The construction is the standard one: take the chart `extChartAt I x` (translated so that it
vanishes at `x`) and multiply it by a `SmoothBumpFunction` at `x`, which is `1` near `x` and
supported inside the chart source.  The bump is invisible to the value and to the derivative at
`x`, and it makes the product globally smooth.
-/

open scoped Manifold ContDiff Bundle
open Bundle Set Filter

namespace Work.Diff.Evol

theorem chartMap_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [T2Space M]
    (x : M) :
    ∃ g : M → E,
      ContMDiff I (modelWithCornersSelf ℝ E) (((⊤ : ℕ∞) : WithTop ℕ∞)) g ∧
      g x = 0 ∧ mvfderiv I g x = mvfderiv I (extChartAt I x) x := by
  classical
  -- A smooth bump function at `x` (it is `1` near `x` and supported in the chart source).
  let f : SmoothBumpFunction I x := Classical.choice inferInstance
  -- The chart map, translated so that it vanishes at `x`; this is smooth on the chart source.
  let c : E := extChartAt I x x
  let h : M → E := fun y => extChartAt I x y - c
  have hh_smooth : ContMDiffOn I (modelWithCornersSelf ℝ E) ∞ h (chartAt H x).source :=
    (contMDiffOn_extChartAt (x := x)).sub contMDiffOn_const
  refine ⟨fun y => f y • h y, ?_, ?_, ?_⟩
  · exact f.contMDiff_smul hh_smooth
  · simp only [f.eq_one, one_smul]
    simp [h, c]
  · have hx_src : x ∈ (chartAt H x).source := mem_chart_source H x
    have hext_mdiff : MDiffAt (extChartAt I x) x := mdifferentiableAt_extChartAt hx_src
    have hc_mdiff : MDiffAt (fun _ : M => c) x := mdifferentiableAt_const
    have h_mdiff : MDiffAt h x := hext_mdiff.sub hc_mdiff
    have hf_mdiff : MDiffAt (fun y : M => f y) x :=
      (SmoothBumpFunction.contMDiffAt f).mdifferentiableAt (by decide)
    have hx0 : h x = 0 := by simp [h, c]
    -- The bump is `1` at `x` and `h x = 0`, so it does not affect the derivative at `x`.
    have hg_eq : mvfderiv I (fun y => f y • h y) x = mvfderiv I h x := by
      change mvfderiv I ((fun y : M => f y) • h) x = mvfderiv I h x
      rw [mvfderiv_smul hf_mdiff h_mdiff, f.eq_one, one_smul, hx0,
        ContinuousLinearMap.smulRight_zero, add_zero]
    -- Translating by a constant does not change the derivative.
    have hh_eq : mvfderiv I h x = mvfderiv I (extChartAt I x) x := by
      rw [show h = (extChartAt I x) - (fun _ : M => c) from rfl,
        mvfderiv_sub hext_mdiff hc_mdiff, mvfderiv_const, sub_zero]
    rw [hg_eq, hh_eq]

end Work.Diff.Evol
