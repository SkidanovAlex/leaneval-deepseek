import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.rgG1_lintegral_bound
import Submission.Work.FTS.PhiStar.Honesty.rgG1_cont_Ioi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

/-- **Far-field square bound for the singular Green branch.**

With `q = rgQ α m ≥ 28` and `rgG1 α m c z = z^{-q} * ∫_0^z c t * t^{q-1} dt`, the function
`z ↦ (rgG1 α m c z)²` is integrable on `(1,∞)`.

HINT (verified by two reviewers).  For `z > 1`, `∫ t in (0)..z, rgF1 α m c t = A₀ + ∫ t in 1..z, rgF1 α m c t`
with `A₀ = ∫ t in (0)..1, rgF1 α m c t` an honest finite constant:
`∫_0^1 |c t| t^{q-1} ≤ (∫_0^1 c²/t⁴)^{1/2} (1/(2q+3))^{1/2} < ∞` by Cauchy–Schwarz with weights
`|c t|/t²` and `t^{q+1}` (use `hnear`).  For this split use
`intervalIntegral.integral_add_adjacent_intervals` with `IntervalIntegrable rgF1 0 1` (from
`hnear`: `|c t| t^{q-1} ≤ (1/2)(c t)²/t⁴ + (1/2) t^{2q+2}` and `2q+2 > -1`) and
`IntervalIntegrable rgF1 1 z` (from `hfar`: `|c t| t^{q-1} ≤ (1/2)(c t)² + (1/2) t^{2q-2}`).
Then `rgG1 z = z^{-q}A₀ + z^{-q}∫ t in 1..z, rgF1 α m c t`, and:
* `∫_1^∞ (z^{-q}A₀)² dz = A₀²/(2q-1) < ∞` (`2q > 1`);
* Cauchy–Schwarz `(∫ t in 1..z, c t t^{q-1})² ≤ (∫ t in 1..z, (c t)² t^{q-1})(∫ t in 1..z, t^{q-1})`
  and `∫ t in 1..z, t^{q-1} = (z^q - 1)/q ≤ z^q/q` give
  `(z^{-q}∫ t in 1..z, c t t^{q-1})² ≤ z^{-q}/q * ∫ t in 1..z, (c t)² t^{q-1}`;
* Tonelli on the region `1 < t < z < ∞` (`Work.FTS.PhiStar.Honesty.lintegral_tail_swap_Ioi_one`)
  gives `∫_1^∞ z^{-q} ∫_1^z (c t)² t^{q-1} dt dz = ∫_1^∞ (c t)² t^{q-1} t^{1-q}/(q-1) dt
   = (1/(q-1)) ∫_1^∞ (c t)² dt < ∞` (use `integral_Ioi_rpow_of_lt` for `∫_t^∞ z^{-q} dz = t^{1-q}/(q-1)`).
Assemble with `(x+y)² ≤ 2x² + 2y²` and `IntegrableOn.union`/`IntegrableOn.congr_fun_ae`.
Measurability of `rgA` on `(1,∞)` (for `AEStronglyMeasurable`): `rgA` is continuous on any
`uIcc 0 y` with `y > 1` by `intervalIntegral.continuousOn_primitive_interval`
(`IntegrableOn rgF1 (uIcc 0 y)` from the two majorants above), so a reduction to each
`Ioc 1 (n+1)` via `Work.FTS.PhiStar.Honesty.integrableOn_Ioi_one_of_interval_bounds` is also
available. -/
theorem rgG1_sq_Ioi {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.EllExist.rgG1 α m c z) ^ 2) (Set.Ioi 1) := by
  have hbound := rgG1_lintegral_bound hα hα4 hm hc hnear hfar
  have hfin : (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((Work.FTS.EllExist.rgG1 α m c z) ^ 2))
      ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hmeas : AEStronglyMeasurable (fun z : ℝ => (Work.FTS.EllExist.rgG1 α m c z) ^ 2)
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    have hcont1 : ContinuousOn (fun z : ℝ => Work.FTS.EllExist.rgG1 α m c z) (Set.Ioi (1 : ℝ)) :=
      (rgG1_cont_Ioi hα hα4 hm hc hnear hfar).mono
        (fun z hz => Set.mem_Ioi.mpr (lt_trans zero_lt_one (Set.mem_Ioi.mp hz)))
    exact (hcont1.pow 2).aestronglyMeasurable (s := Set.Ioi (1 : ℝ)) measurableSet_Ioi
  have hfin' : HasFiniteIntegral (fun z : ℝ => (Work.FTS.EllExist.rgG1 α m c z) ^ 2)
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    rw [hasFiniteIntegral_iff_norm]
    have this : (∫⁻ z, ENNReal.ofReal ‖(Work.FTS.EllExist.rgG1 α m c z) ^ 2‖
          ∂(volume.restrict (Set.Ioi (1 : ℝ))))
        = ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((Work.FTS.EllExist.rgG1 α m c z) ^ 2) := by
      refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
    rw [this]
    exact lt_top_iff_ne_top.mpr hfin
  exact ⟨hmeas, hfin'⟩

end Work.FTS.PhiStar.Honesty
