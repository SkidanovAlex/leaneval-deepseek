/-
# `rgiA_abs_le`

The value bound for the `0..z` Green integral `Work.FTS.PhiStar.Series.rgiA`:

  `|rgiA α m c y| ≤ M * y ^ ((2m+5)/α) / ((2m+5)/α)`  for `y > 0`,

whenever `|c t| ≤ M` for all `t : ℝ`.

Since `rgiA α m c y = ∫ t in (0)..y, c t * t ^ ((2m+5)/α - 1)` and `p := (2m+5)/α > 0`, this is
the elementary estimate

  `|∫_0^y c t t^{p-1} dt| ≤ ∫_0^y |c t| t^{p-1} dt ≤ M ∫_0^y t^{p-1} dt = M y^p / p`.

The only integration fact needed beyond the standard library is the closed form
`∫_0^y t^{p-1} dt = y^p / p`, which is `integral_rpow` together with `0 ^ p = 0`
(`p ≠ 0`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

noncomputable section
open MeasureTheory

namespace Work.FTS.PhiStar.Honesty

/-- If `f` is dominated by `M * t ^ (p - 1)` on `[0, y]` (`p > 0`, `y > 0`) then the interval
integral of `f` is bounded by `M * y ^ p / p`.

The hypothesis `0 ≤ M` is not needed separately: the domination hypothesis forces it (for
`t ≥ 0` large enough that `t ^ (p-1) > 0`). -/
theorem rgiA_interval_bound {f : ℝ → ℝ} {M p y : ℝ} (hM : 0 ≤ M) (hp : 0 < p)
    (hb : ∀ t : ℝ, 0 ≤ t → |f t| ≤ M * t ^ (p - 1)) (hy : 0 < y) :
    |∫ t in (0 : ℝ)..y, f t| ≤ M * y ^ p / p := by
  have hq : -1 < p - 1 := by linarith
  -- write the interval integral as an integral against `volume.restrict (Ioc 0 y)`
  have hEq : ∫ t in (0 : ℝ)..y, f t = ∫ t in Set.Ioc (0 : ℝ) y, f t :=
    intervalIntegral.integral_of_le hy.le
  rw [hEq]
  -- integrability of the majorant `M * t ^ (p - 1)` on `Ioc 0 y`
  have hInt1 : MeasureTheory.Integrable (fun t : ℝ => t ^ (p - 1))
      (volume.restrict (Set.Ioc (0 : ℝ) y)) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := y) hq).1
  have hInt2 : MeasureTheory.Integrable (fun t : ℝ => M * t ^ (p - 1))
      (volume.restrict (Set.Ioc (0 : ℝ) y)) := hInt1.const_mul M
  -- the monotone step, a.e. in `Ioc 0 y`
  have hmono : ∫ t in Set.Ioc (0 : ℝ) y, |f t| ≤ ∫ t in Set.Ioc (0 : ℝ) y, M * t ^ (p - 1) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => abs_nonneg _) hInt2 ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    exact hb t ht.1.le
  calc |∫ t in Set.Ioc (0 : ℝ) y, f t|
      ≤ ∫ t in Set.Ioc (0 : ℝ) y, |f t| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) y, M * t ^ (p - 1) := hmono
    _ = M * y ^ p / p := by
        rw [← intervalIntegral.integral_of_le hy.le, intervalIntegral.integral_const_mul]
        have hrpow : ∫ t in (0 : ℝ)..y, t ^ (p - 1) = y ^ p / p := by
          rw [integral_rpow (Or.inl hq)]
          rw [show (p - 1) + 1 = p from by ring, Real.zero_rpow (ne_of_gt hp)]
          simp
        rw [hrpow]
        ring

theorem rgiA_abs_le {α : ℝ} (hα : 0 < α) {m : ℕ} {c : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t : ℝ, |c t| ≤ M) :
    ∀ y : ℝ, 0 < y →
      |Work.FTS.PhiStar.Series.rgiA α m c y|
        ≤ M * y ^ ((2 * (m : ℝ) + 5) / α) / ((2 * (m : ℝ) + 5) / α) := by
  intro y hy
  have hp : 0 < (2 * (m : ℝ) + 5) / α := by
    apply div_pos _ hα
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hpt : ∀ t : ℝ, 0 ≤ t →
      |Work.FTS.PhiStar.Series.rgiF1 α m c t| ≤ M * t ^ ((2 * (m : ℝ) + 5) / α - 1) := by
    intro t ht
    rw [Work.FTS.PhiStar.Series.rgiF1, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht _)]
    exact mul_le_mul_of_nonneg_right (hb t) (Real.rpow_nonneg ht _)
  exact rgiA_interval_bound hM hp hpt hy

end Work.FTS.PhiStar.Honesty
