import Mathlib

namespace Work.FIArea3.JointCount

/-- For `t ∈ [0,1]`, `4 (e^t - 1) ≥ t (2 e^t + 1)`.

This is the numerical heart of `gn_ge`: the lower bound `e^t ≥ 1 + t + t²/2 + t³/6`
(partial Taylor sum) gives `(4-2t) e^t - 4 - t ≥ t - t³/3 - t⁴/3 ≥ 0`, and left-multiplying
by the nonnegative `4 - 2t` keeps the inequality in the right direction. -/
private lemma four_mul_exp_sub_one_ge (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (2 * Real.exp t + 1) ≤ 4 * (Real.exp t - 1) := by
  have hsum := Real.sum_le_exp_of_nonneg ht0 4
  have hsum' : 1 + t + t^2/2 + t^3/6 ≤ Real.exp t := by
    simpa [Finset.sum_range_succ, Nat.factorial] using hsum
  have hcoef : 0 ≤ 4 - 2*t := by linarith
  have h1 := mul_le_mul_of_nonneg_left hsum' hcoef
  have hp : 0 ≤ t - t^3/3 - t^4/3 := by
    nlinarith [ht0, ht1, sq_nonneg (t^2 - t), sq_nonneg (t - 1)]
  nlinarith [h1, hp]

theorem gn_ge (n : ℕ) (hn : 4 ≤ n) (v : ℝ) (hv : (n:ℝ) ≤ v) (hv2 : v < n+1) :
    0.5 * Real.exp n / n ≤ Real.exp v * (1.5/v - 1/n) := by
  have hn4 : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  set t : ℝ := v - (n:ℝ) with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have ht1 : t ≤ 1 := by
    rw [ht]
    have h : v < (n:ℝ) + 1 := by exact_mod_cast hv2
    linarith
  have hv_eq : v = (n:ℝ) + t := by rw [ht]; ring
  have hcore : t * (2 * Real.exp t + 1) ≤ (n:ℝ) * (Real.exp t - 1) := by
    have h4 : t * (2 * Real.exp t + 1) ≤ 4 * (Real.exp t - 1) :=
      four_mul_exp_sub_one_ge t ht0 ht1
    have hexp1 : 0 ≤ Real.exp t - 1 := by
      have := Real.one_le_exp ht0; linarith
    have hmono : 4 * (Real.exp t - 1) ≤ (n:ℝ) * (Real.exp t - 1) :=
      mul_le_mul_of_nonneg_right hn4 hexp1
    linarith
  -- `e^t (n - 2t) ≥ n + t = v`
  have hmain :
      Real.exp (n:ℝ) * ((n:ℝ) + t) ≤ Real.exp (n:ℝ) * Real.exp t * ((n:ℝ) - 2*t) := by
    have hEn : 0 < Real.exp (n:ℝ) := Real.exp_pos _
    have hcore' : 0 ≤ (n:ℝ) * (Real.exp t - 1) - t*(2*Real.exp t + 1) := by linarith
    have hm := mul_nonneg hEn.le hcore'
    nlinarith [hm]
  rw [hv_eq, Real.exp_add]
  have hden : 0 ≤ 2 * (n:ℝ) * ((n:ℝ) + t) := by
    have : 0 ≤ (n:ℝ) + t := by linarith
    positivity
  calc
    0.5 * Real.exp (n:ℝ) / (n:ℝ)
        = Real.exp (n:ℝ) * ((n:ℝ) + t) / (2 * (n:ℝ) * ((n:ℝ) + t)) := by
            field_simp
            ring
    _ ≤ Real.exp (n:ℝ) * Real.exp t * ((n:ℝ) - 2*t) / (2 * (n:ℝ) * ((n:ℝ) + t)) :=
            div_le_div_of_nonneg_right hmain hden
    _ = Real.exp (n:ℝ) * Real.exp t * (((n:ℝ) - 2*t) / (2 * (n:ℝ) * ((n:ℝ) + t))) := by ring
    _ = Real.exp (n:ℝ) * Real.exp t * (1.5/((n:ℝ) + t) - 1/(n:ℝ)) := by
            congr 1
            field_simp
            ring

end Work.FIArea3.JointCount
