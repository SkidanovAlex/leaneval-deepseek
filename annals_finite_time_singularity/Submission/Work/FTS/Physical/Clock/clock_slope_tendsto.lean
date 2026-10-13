import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slope of the clock at the blow-up time

The clock of the dynamic rescaling is `t(τ) = ∫₀^τ A`, where the amplitude `A` is positive and
continuous on `[0,∞)` (`PhysClock.hApos`, `PhysClock.hAcont`).  This file computes the *right*
slope of the clock at `τ = 0`:

`t(y)/y ⟶ A(0)`  and  `y/t(y) ⟶ A(0)⁻¹`  as `y → 0⁺`.

The first limit is the fundamental theorem of calculus: `A` has right limit `A(0)` at `0`, so the
average of `A` over `(0,y)` tends to `A(0)`; equivalently `t` has right derivative `A 0` at `0`,
and the Newton quotient `(t(y) - t(0))/(y - 0) = t(y)/y` converges to it
(`hasDerivWithinAt_iff_tendsto_slope`).  The second limit follows from the first by continuity of
`x ↦ x⁻¹` at the *nonzero* value `A(0) > 0` and the field identity `(t(y)/y)⁻¹ = y/t(y)`
(`inv_div`, which in a `DivisionMonoid` is unconditional — no side condition on `t(y)` is needed).

Both limits are one-sided: `t` is only known to be a primitive of `A` with `A` continuous on
`[0,∞)`, so nothing is claimed about the slope from the left (`A` is not even assumed continuous
on `(-∞,0)`).
-/

namespace Work.FTS.Physical.Clock

open Filter MeasureTheory
open scoped Topology

/-- **`t` has right derivative `A 0` at `0`.**  This is the fundamental theorem of calculus at the
left endpoint `0` of the fake-time half-line: `A` is integrable on the degenerate interval `0..0`,
strongly measurable at `𝓝[>] 0` (being continuous on `[0,∞)`), and continuous at `0` within
`(0,∞)` (`PhysClock.hAcont`), so `u ↦ ∫₀^u A` has derivative `A 0` at `0` within `Ici 0`.

Note that no two-sided derivative is claimed (nor true in general): `A` is only assumed continuous
on `[0,∞)`. -/
theorem hasDerivWithinAt_t_zero (C : Work.FTS.Physical.PhysClock) :
    HasDerivWithinAt C.t (C.A 0) (Set.Ici (0 : ℝ)) 0 := by
  -- `A` is continuous at `0` along `(0,∞)`
  have hA : ContinuousWithinAt C.A (Set.Ioi (0 : ℝ)) 0 :=
    (C.hAcont 0 (Set.mem_Ici.mpr le_rfl)).mono Set.Ioi_subset_Ici_self
  -- and strongly measurable at `𝓝[>] 0`
  have hmeas : StronglyMeasurableAtFilter C.A (𝓝[Set.Ioi (0 : ℝ)] 0) volume :=
    ⟨Set.Ioi 0, self_mem_nhdsWithin,
      (C.hAcont.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi⟩
  -- and integrable on the degenerate interval `0..0`
  have hf : IntervalIntegrable C.A volume (0 : ℝ) 0 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le le_rfl]
    exact C.hAcont.mono Set.Icc_subset_Ici_self
  have hderiv : HasDerivWithinAt (fun u : ℝ => ∫ x in (0 : ℝ)..u, C.A x) (C.A 0) (Set.Ici 0) 0 :=
    intervalIntegral.integral_hasDerivWithinAt_right hf hmeas hA
  exact hderiv

/-- **The right slope of the clock at `0` is `A 0`**: `t(y)/y → A(0)` as `y → 0⁺`. -/
theorem tendsto_t_div_self (C : Work.FTS.Physical.PhysClock) :
    Filter.Tendsto (fun y : ℝ => C.t y / y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (C.A 0)) := by
  -- the Newton quotient is the slope, which converges to the right derivative
  have hslope : Filter.Tendsto (slope C.t 0) (nhdsWithin (0 : ℝ) (Set.Ici 0 \ {0}))
      (nhds (C.A 0)) :=
    hasDerivWithinAt_iff_tendsto_slope.mp (hasDerivWithinAt_t_zero C)
  -- `Ioi 0` is (up to the irrelevant point `0`) the domain of the slope
  have hsub : Set.Ioi (0 : ℝ) ⊆ Set.Ici (0 : ℝ) \ {0} := by
    intro y hy
    have hy0 : 0 < y := Set.mem_Ioi.mp hy
    exact ⟨le_of_lt hy0, by simp [ne_of_gt hy0]⟩
  have hmono := hslope.mono_left (nhdsWithin_mono 0 hsub)
  refine hmono.congr' ?_
  filter_upwards with y
  simp [slope_def_field]

/-- **The reciprocal right slope of the clock at `0`**: `y/t(y) → A(0)⁻¹` as `y → 0⁺`.  This is
`t(y)/y → A(0)` (`tendsto_t_div_self`) composed with inversion at the nonzero value `A(0) > 0`,
using the identity `(t(y)/y)⁻¹ = y/t(y)` of a `DivisionMonoid`. -/
theorem tendsto_self_div_t (C : Work.FTS.Physical.PhysClock) :
    Filter.Tendsto (fun y : ℝ => y / C.t y) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((C.A 0)⁻¹)) := by
  have hne : C.A 0 ≠ 0 := ne_of_gt (C.hApos 0 le_rfl)
  have h2 : Filter.Tendsto (fun y : ℝ => (C.t y / y)⁻¹) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((C.A 0)⁻¹)) :=
    (tendsto_t_div_self C).inv₀ hne
  refine h2.congr' ?_
  filter_upwards with y
  exact inv_div (C.t y) y

/-- **The slope of the clock at the blow-up time.**  The clock `t(τ) = ∫₀^τ A` of a `PhysClock`
has slope `A(0)` at `τ = 0` from the right, in both orientations: `t(y)/y → A(0)` and
`y/t(y) → A(0)⁻¹` as `y → 0⁺`. -/
theorem clock_slope_tendsto (C : Work.FTS.Physical.PhysClock) :
    Filter.Tendsto (fun y : ℝ => C.t y / y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (C.A 0)) ∧
    Filter.Tendsto (fun y : ℝ => y / C.t y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((C.A 0)⁻¹)) :=
  ⟨tendsto_t_div_self C, tendsto_self_div_t C⟩

end Work.FTS.Physical.Clock
