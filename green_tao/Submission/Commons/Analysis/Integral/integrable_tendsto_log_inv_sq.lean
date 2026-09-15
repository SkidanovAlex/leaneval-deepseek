import Mathlib
import Submission.Commons.Analysis.Integral.integrable_log_lorentz

open Filter MeasureTheory

namespace Commons.Analysis.Integral

/-- `(log x + c)/x² → 0` as `x → +∞`.  The logarithmic growth of the numerator is
beaten by the quadratic decay of the denominator. -/
lemma tendsto_log_add_const_div_sq (c : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x + c) / x ^ 2) atTop (nhds 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x ^ 2) atTop (nhds 0) := by
    have h : Real.log =o[atTop] (fun x : ℝ => x ^ 2) := by
      simpa [Real.rpow_natCast, Nat.cast_ofNat]
        using isLittleO_log_rpow_atTop (r := 2) two_pos
    exact h.tendsto_div_nhds_zero
  have hconst : Tendsto (fun x : ℝ => c / x ^ 2) atTop (nhds 0) := by
    have h2 : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := by simp
    have h := (h2.inv_tendsto_atTop).const_mul c
    simpa [div_eq_mul_inv] using h
  have hsum := hlog.add hconst
  simpa [add_div] using hsum

/-- The decay weight `t ↦ (log(|t|+2)+1)/(a²+t²)` tends to `0` at `+∞` when `a > 0`. -/
lemma tendsto_log_abs_add_div_sq_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => (Real.log (|t| + 2) + 1) / (a ^ 2 + t ^ 2)) atTop (nhds 0) := by
  have hcore : Tendsto (fun s : ℝ => (Real.log (s + 2) + 1) / (a ^ 2 + s ^ 2)) atTop (nhds 0) := by
    refine squeeze_zero' (g := fun s : ℝ => (Real.log s + (Real.log 3 + 1)) / s ^ 2) ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      refine div_nonneg ?_ (by positivity)
      have h0 : 0 ≤ Real.log (s + 2) := Real.log_nonneg (by linarith)
      linarith
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
      have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
      have hnum : Real.log (s + 2) + 1 ≤ Real.log s + (Real.log 3 + 1) := by
        have hle : s + 2 ≤ 3 * s := by linarith
        have h1 : Real.log (s + 2) ≤ Real.log (3 * s) := Real.log_le_log (by linarith) hle
        rw [Real.log_mul (by norm_num) (ne_of_gt hs0)] at h1
        linarith
      have hnum0 : 0 ≤ Real.log s + (Real.log 3 + 1) := by
        have h0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
        have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
        linarith
      have hden : 0 < s ^ 2 := by positivity
      have hdenle : s ^ 2 ≤ a ^ 2 + s ^ 2 := by nlinarith [sq_nonneg a]
      calc (Real.log (s + 2) + 1) / (a ^ 2 + s ^ 2)
          ≤ (Real.log s + (Real.log 3 + 1)) / (a ^ 2 + s ^ 2) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ (Real.log s + (Real.log 3 + 1)) / s ^ 2 :=
            div_le_div_of_nonneg_left hnum0 hden hdenle
    · exact tendsto_log_add_const_div_sq (Real.log 3 + 1)
  have h := hcore.comp tendsto_abs_atTop_atTop
  refine Tendsto.congr' ?_ h
  filter_upwards with x
  rw [Function.comp_apply, sq_abs]

/-- The weight `t ↦ (log(|t|+2)+1)/(a²+t²)` (`a > 0`) is integrable and tends to `0` at `±∞`.
This is the decay weight used in the vertical contour shifts of Green–Tao §10.
PROOF SKETCH: `(log(|t|+2)+1)/(a²+t²) ≤ (log(|t|+2)+1)/(1+t²)`, and `log(|t|+2) ≤ C·(1+t²)^{1/4}`
(or simply: `(log(|t|+2)+1)/(1+t²) ≤ C·(1+t²)^{-3/4}` since `log(|t|+2) ≤ C(1+t²)^{1/4}`), which is
integrable by comparison with `(1+t²)^{-3/4}` (integrable on `ℝ` because `3/4 > 1/2`).  For the
limit: the numerator grows like `log|t|` and the denominator like `t²`. -/
lemma integrable_tendsto_log_inv_sq {a : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable (fun t : ℝ => (Real.log (|t| + 2) + 1) / (a ^ 2 + t ^ 2))
      ∧ Filter.Tendsto (fun t : ℝ => (Real.log (|t| + 2) + 1) / (a ^ 2 + t ^ 2))
          Filter.atTop (nhds 0)
      ∧ Filter.Tendsto (fun t : ℝ => (Real.log (|t| + 2) + 1) / (a ^ 2 + t ^ 2))
          Filter.atBot (nhds 0) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := integrable_log_lorentz a 0 ha
    have hfun : (fun t : ℝ => (Real.log (2 + |t|) + 1) / (a ^ 2 + (t - 0) ^ 2))
        = fun t : ℝ => (Real.log (|t| + 2) + 1) / (a ^ 2 + t ^ 2) := by
      funext t
      rw [sub_zero, add_comm (2 : ℝ) |t|]
    rwa [hfun] at h
  · exact tendsto_log_abs_add_div_sq_atTop ha
  · have h := (tendsto_log_abs_add_div_sq_atTop ha).comp tendsto_abs_atBot_atTop
    refine Tendsto.congr' ?_ h
    filter_upwards with x
    rw [Function.comp_apply, abs_abs, sq_abs]

end Commons.Analysis.Integral
