import Mathlib

/-!
# KL-R5: the mean value of `log‖h‖` on the circle via Jensen + r→1⁻

(R5 of Plan.md DESIGN NOTE 5.)  In Fedja's proof of the Konyagin–Lev
inequality one needs: if `h := 2 − f_a` is zero-free on the closed unit
disk and bounded away from zero there, then the *boundary* circle average of
`log‖h‖` equals `log‖h(0)‖`:

    Real.circleAverage (fun z => Real.log ‖h z‖) 0 1 = Real.log ‖h 0‖.

Proof: for each radius `0 < r < 1`, Jensen's formula
(`AnalyticOnNhd.circleAverage_log_norm_of_ne_zero`, in
Mathlib/Analysis/Complex/JensenFormula.lean) applied on the closed ball of
radius `r` gives the equality at radius `r` (the divisor/finsum vanishes
because `h` is zero-free on the closed unit disk); then pass to the limit
`r → 1⁻` in the circle average.  This passage of the limit is handled by
`Real.ContinuousOn.circleAverage` (continuity of `r ↦ circleAverage f 0 r`
for `f` continuous on the union of the circles, i.e. on the closed unit
disk — `log‖h‖` is continuous there since `h` is continuous and bounded
away from zero) together with `Real.ContinuousOn.eq_of_eqOn_Ioo` (a
function continuous on `Ioc 0 1` and constant on `Ioo 0 1` takes that
constant at `1`).

The second theorem `boundary_log_nonneg_of_inner_log_neg` is the
contradiction step used in the KL proof (here `h(0) = 2 − a ∈ (0,1)`):
from `0 ≤ Real.circleAverage ... 0 1` and `Real.log ‖h 0‖ < 0` get False.
-/

noncomputable section

open scoped Real Complex
open Complex
open Metric
open MeasureTheory
open Interval

namespace Submission.Core

/-- **Mean value on the circle.**  If `h` is analytic on the open unit disk,
continuous and bounded away from zero on the closed unit disk, then the
boundary circle average of `log‖h‖` equals `log‖h(0)‖`. -/
theorem log_norm_boundary_circleAverage (h : ℂ → ℂ)
    (hh : AnalyticOn ℂ h (Metric.ball (0 : ℂ) 1))
    (hcont : ContinuousOn h (Metric.closedBall (0 : ℂ) 1))
    (hm : ∃ m : ℝ, 0 < m ∧ ∀ z ∈ Metric.closedBall (0 : ℂ) 1, m ≤ ‖h z‖) :
    Real.log ‖h 0‖ =
      Real.circleAverage (fun z : ℂ => Real.log ‖h z‖) (0 : ℂ) 1 := by
  let g : ℂ → ℝ := fun z => Real.log ‖h z‖
  obtain ⟨m, hmpos, hmle⟩ := hm
  have hmgt : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 < ‖h z‖ := by
    intro z hz
    exact lt_of_lt_of_le hmpos (hmle z hz)
  -- `g = Real.log ∘ ‖h ·‖` is continuous on the closed unit disk.
  have hgcont : ContinuousOn g (Metric.closedBall (0 : ℂ) 1) := by
    refine ContinuousOn.log ?_ ?_
    · simpa [g] using hcont.norm
    · intro z hz
      exact ne_of_gt (hmgt z hz)
  -- Jensen's formula at every intermediate radius `r ∈ Ioo 0 1`.
  have hIoo : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      Real.circleAverage g 0 r = Real.log ‖h 0‖ := by
    intro r hr
    have hran : AnalyticOnNhd ℂ h (Metric.closedBall (0 : ℂ) |r|) := by
      intro z hz
      refine AnalyticOn.analyticAt ?_ hh
      have hz1 : dist z (0 : ℂ) < 1 :=
        lt_of_le_of_lt (mem_closedBall.mp hz) (by simpa [abs_of_pos hr.1] using hr.2)
      exact (isOpen_ball.mem_nhds (mem_ball.mpr hz1))
    have hnez : ∀ u ∈ Metric.closedBall (0 : ℂ) |r|, h u ≠ 0 := by
      intro u hu
      have hu1 : u ∈ Metric.closedBall (0 : ℂ) 1 := by
        apply mem_closedBall.mpr
        calc
          dist u (0 : ℂ) ≤ |r| := mem_closedBall.mp hu
          _ ≤ 1 := by simpa [abs_of_pos hr.1] using le_of_lt hr.2
      exact norm_ne_zero_iff.mp (ne_of_gt (hmgt u hu1))
    simpa [g, abs_of_pos hr.1] using
      (AnalyticOnNhd.circleAverage_log_norm_of_ne_zero (R := r) (c := (0 : ℂ)) (g := h)
        hran hnez)
  -- The circle average is continuous in the radius on `Ioc 0 1`.
  have hcontR : ContinuousOn (fun r : ℝ => Real.circleAverage g 0 r) (Set.Ioc 0 1) := by
    refine Real.ContinuousOn.circleAverage (f := g) (c := (0 : ℂ)) (s := Set.Ioc 0 1) ?_ ?_
    · refine hgcont.mono ?_
      intro z hz
      simpa [mem_closedBall, dist_eq_norm] using hz.2
    · intro r hr
      exact le_of_lt hr.1
  -- Constant on `Ioo 0 1` and continuous up to `1`, hence the value at `1`.
  simpa [g] using (Real.ContinuousOn.eq_of_eqOn_Ioo
    (f := fun r : ℝ => Real.circleAverage g 0 r)
    (c := Real.log ‖h 0‖) (r := 0) (R := 1) hcontR zero_lt_one hIoo).symm

/-- **Contradiction from a nonnegative boundary average.**  If additionally
the boundary circle average is nonnegative but `log‖h 0‖ < 0` (i.e.
`‖h 0‖ < 1`), then `False`. -/
theorem boundary_log_nonneg_of_inner_log_neg (h : ℂ → ℂ)
    (hh : AnalyticOn ℂ h (Metric.ball (0 : ℂ) 1))
    (hcont : ContinuousOn h (Metric.closedBall (0 : ℂ) 1))
    (hm : ∃ m : ℝ, 0 < m ∧ ∀ z ∈ Metric.closedBall (0 : ℂ) 1, m ≤ ‖h z‖)
    (hmean : 0 ≤ Real.circleAverage (fun z : ℂ => Real.log ‖h z‖) (0 : ℂ) 1)
    (hlt : Real.log ‖h 0‖ < 0) : False := by
  have heq : Real.log ‖h 0‖ =
      Real.circleAverage (fun z : ℂ => Real.log ‖h z‖) (0 : ℂ) 1 :=
    log_norm_boundary_circleAverage h hh hcont hm
  have hge : 0 ≤ Real.log ‖h 0‖ := by
    rw [heq]
    exact hmean
  linarith

end Submission.Core

end
