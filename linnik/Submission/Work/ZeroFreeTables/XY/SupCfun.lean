/-
# ZeroFreeTables/XY/SupCfun

The two elementary bounds on the oscillatory integral `Cc t = ∫₀^{3/4} g(x) cos(tx) dx`
of `LamPrimeData`, used by `LamPrimeSup` to control the "main" term `C`:

* `|Cc t| ≤ 2/3` for every `t`, since `|cos| ≤ 1` and `∫₀^{3/4} g = 2/3`;
* `Cc t ≥ 2/3 - 3t²/80` for every `t`, since `cos y ≥ 1 - y²/2`, `∫₀^{3/4} g = 2/3`
  and `∫₀^{3/4} g x² = 3/40`.

Both rest on the explicit form `g x = (4/3)(1 - (16/9)x²)` on `[0,3/4]` (`xyG_eq_poly`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XY.LamPrimeData

open MeasureTheory intervalIntegral
noncomputable section

namespace Work.ZeroFreeTables.XY

/-- `∫₀^{3/4} g = 2/3`. -/
lemma integral_xyG : ∫ x in (0:ℝ)..(3/4), xyG x = 2/3 := by
  rw [intervalIntegral.integral_congr (g := fun x => (4/3)*(1-(16/9)*x^2)) ?_]
  · rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
    · exact intervalIntegrable_const
    · exact (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
  · intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3/4)] at hx
    exact xyG_eq_poly x hx

/-- `∫₀^{3/4} g(x) x² dx = 3/40`. -/
lemma integral_xyG_sq : ∫ x in (0:ℝ)..(3/4), xyG x * x^2 = 3/40 := by
  rw [intervalIntegral.integral_congr (g := fun x => (4/3)*((1-(16/9)*x^2)*x^2)) ?_]
  · rw [intervalIntegral.integral_const_mul]
    rw [show (fun x : ℝ => (1-(16/9)*x^2)*x^2) = (fun x : ℝ => x^2 - (16/9)*x^4) from by funext x; ring]
    rw [intervalIntegral.integral_sub]
    · rw [integral_pow]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
    · exact (continuous_pow 2).intervalIntegrable _ _
    · exact (continuous_const.mul (continuous_pow 4)).intervalIntegrable _ _
  · intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3/4)] at hx
    show xyG x * x^2 = (4/3)*((1-(16/9)*x^2)*x^2)
    rw [xyG_eq_poly x hx]; ring

theorem SupCfun : ∀ t : ℝ, 2/3 - 3*t^2/80 ≤ Work.ZeroFreeTables.XY.Cc t ∧ |Work.ZeroFreeTables.XY.Cc t| ≤ 2/3 := by
  intro t
  have hcf : Continuous (fun x : ℝ => xyG x * (1 - (t*x)^2/2)) := by
    apply xyG_cont.mul
    fun_prop
  have hcg : Continuous (fun x : ℝ => xyG x * Real.cos (t*x)) := by
    apply xyG_cont.mul
    exact Real.continuous_cos.comp (by fun_prop)
  constructor
  · rw [Cc]
    have hmono : ∫ x in (0:ℝ)..(3/4), xyG x * (1 - (t*x)^2/2)
        ≤ ∫ x in (0:ℝ)..(3/4), xyG x * Real.cos (t*x) := by
      apply intervalIntegral.integral_mono (by norm_num)
      · exact hcf.intervalIntegrable _ _
      · exact hcg.intervalIntegrable _ _
      · intro x
        have hcos := Real.one_sub_sq_div_two_le_cos (x := t*x)
        have hg := xyG_nonneg x
        nlinarith [hg, hcos]
    have heq : ∫ x in (0:ℝ)..(3/4), xyG x * (1 - (t*x)^2/2) = 2/3 - 3*t^2/80 := by
      rw [show (fun x : ℝ => xyG x * (1 - (t*x)^2/2))
            = (fun x : ℝ => xyG x - xyG x * ((t*x)^2/2)) from by funext x; ring]
      rw [intervalIntegral.integral_sub]
      · rw [integral_xyG]
        rw [show (fun x : ℝ => xyG x * ((t*x)^2/2))
              = (fun x : ℝ => (t^2/2) * (xyG x * x^2)) from by funext x; ring]
        rw [intervalIntegral.integral_const_mul, integral_xyG_sq]
        ring
      · exact xyG_cont.intervalIntegrable _ _
      · apply Continuous.intervalIntegrable
        apply xyG_cont.mul
        fun_prop
    linarith [hmono, heq.ge]
  · rw [Cc]
    have h1 : |∫ x in (0:ℝ)..(3/4), xyG x * Real.cos (t*x)|
        ≤ ∫ x in (0:ℝ)..(3/4), |xyG x * Real.cos (t*x)| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    have h2 : ∫ x in (0:ℝ)..(3/4), |xyG x * Real.cos (t*x)| ≤ ∫ x in (0:ℝ)..(3/4), xyG x := by
      apply intervalIntegral.integral_mono (by norm_num)
      · exact hcg.abs.intervalIntegrable _ _
      · exact xyG_cont.intervalIntegrable _ _
      · intro x
        show |xyG x * Real.cos (t*x)| ≤ xyG x
        rw [abs_mul, abs_of_nonneg (xyG_nonneg x)]
        exact mul_le_of_le_one_right (xyG_nonneg x) (Real.abs_cos_le_one _)
    calc |∫ x in (0:ℝ)..(3/4), xyG x * Real.cos (t*x)|
        ≤ ∫ x in (0:ℝ)..(3/4), |xyG x * Real.cos (t*x)| := h1
      _ ≤ ∫ x in (0:ℝ)..(3/4), xyG x := h2
      _ = 2/3 := integral_xyG

end Work.ZeroFreeTables.XY
