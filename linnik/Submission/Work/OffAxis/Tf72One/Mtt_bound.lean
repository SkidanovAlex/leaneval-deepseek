import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.OffAxis.G72MomentClosed
import Submission.Work.OffAxis.G72Mom234
import Submission.Work.ZeroFreeTables.tf72_exp_taylor_upper

open scoped Interval
open MeasureTheory

namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables

/-- Crude exponential upper bound by a quartic: `e^u ≤ 1 + u + u²/2 + u³/6 + (4/45)u⁴`
for `0 ≤ u ≤ 17/8`.  This is the order-4 truncated series plus a geometric-remainder
bound `e^u ≤ Σ_{k<4} uᵏ/k! + (u⁴/24)·(1-u/4)⁻¹ ≤ Σ_{k<4} uᵏ/k! + (32/15)·u⁴/24`. -/
lemma exp_series_quartic (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 17/8) :
    Real.exp u ≤ 1 + u + u^2/2 + u^3/6 + (4/45)*u^4 := by
  obtain ⟨_, hub⟩ := Work.ZeroFreeTables.P9F.exp_series_bounds 4 (by norm_num) u hu0
    (by push_cast; linarith)
  have hsum : (∑ k ∈ Finset.range 4, u^k/(k.factorial:ℝ)) = 1 + u + u^2/2 + u^3/6 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at hub
  have hden : (0:ℝ) < 1 - u/4 := by linarith
  have hfrac : (1:ℝ)/(1 - u/4) ≤ 32/15 := by
    have hle : (15:ℝ)/32 ≤ 1 - u/4 := by linarith
    calc (1:ℝ)/(1 - u/4) ≤ 1/((15:ℝ)/32) :=
          one_div_le_one_div_of_le (by norm_num) hle
      _ = 32/15 := by norm_num
  have h4 : ((4:ℕ).factorial : ℝ) = 24 := by norm_num
  rw [h4] at hub
  have hnn : (0:ℝ) ≤ u^4/24 := by positivity
  calc Real.exp u ≤ 1 + u + u^2/2 + u^3/6 + u^4/24 * (1/(1-u/4)) := hub
    _ ≤ 1 + u + u^2/2 + u^3/6 + u^4/24 * (32/15) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hfrac hnn)
    _ = 1 + u + u^2/2 + u^3/6 + (4/45)*u^4 := by ring

/-- `e^{17y/16} ≤ 3 + (9/20)y⁴` for `0 ≤ y ≤ 2`. -/
lemma exp_1716_quartic (y : ℝ) (hy0 : 0 ≤ y) (hy2 : y ≤ 2) :
    Real.exp (17*y/16) ≤ 3 + (9/20)*y^4 := by
  have hu0 : 0 ≤ 17*y/16 := by positivity
  have hu17 : 17*y/16 ≤ 17/8 := by nlinarith
  have h1 := exp_series_quartic (17*y/16) hu0 hu17
  have h2 : 1 + 17*y/16 + (17*y/16)^2/2 + (17*y/16)^3/6 + (4/45)*(17*y/16)^4
      ≤ 3 + (9/20)*y^4 := by
    nlinarith [sq_nonneg (y - 3/2), sq_nonneg (y - 1), sq_nonneg (y - 2), sq_nonneg y]
  linarith

/-- Pointwise bound `|e^{sy} - 2| ≤ 1 + (9/20)y⁴` for `0 ≤ s ≤ 17/16`, `0 ≤ y ≤ 2`. -/
lemma abs_exp_2_le (s y : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 17/16) (hy0 : 0 ≤ y) (hy2 : y ≤ 2) :
    |Real.exp (s*y) - 2| ≤ 1 + (9/20)*y^4 := by
  rcases le_total (Real.exp (s*y)) 2 with h | h
  · have hle : Real.exp (s*y) - 2 ≤ 0 := by linarith
    rw [abs_of_nonpos hle]
    have hge : 1 ≤ Real.exp (s*y) := Real.one_le_exp (by positivity)
    have : (0:ℝ) ≤ (9/20)*y^4 := by positivity
    linarith
  · have hnn : 0 ≤ Real.exp (s*y) - 2 := by linarith
    rw [abs_of_nonneg hnn]
    have he : Real.exp (s*y) ≤ Real.exp (17*y/16) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hb := exp_1716_quartic y hy0 hy2
    linarith

/-- `∫₀² y² (1 + (9/20)y⁴) g72 y dy = 944/1575`. -/
lemma integral_quadratic_weight :
    ∫ y in (0:ℝ)..2, y^2 * (1 + (9/20)*y^4) * Work.ZeroFreeTables.g72 y = 944/1575 := by
  have hI2 : IntervalIntegrable (fun y : ℝ => y^2 * Work.ZeroFreeTables.g72 y)
      MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]; fun_prop
  have hI6 : IntervalIntegrable (fun y : ℝ => y^6 * Work.ZeroFreeTables.g72 y)
      MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]; fun_prop
  have hcongr : (∫ y in (0:ℝ)..2, y^2 * (1 + (9/20)*y^4) * Work.ZeroFreeTables.g72 y)
      = ∫ y in (0:ℝ)..2,
          (y^2 * Work.ZeroFreeTables.g72 y + (9/20) * (y^6 * Work.ZeroFreeTables.g72 y)) := by
    apply intervalIntegral.integral_congr
    intro y _
    ring
  rw [hcongr, intervalIntegral.integral_add hI2 (hI6.const_mul (9/20)),
    intervalIntegral.integral_const_mul, Work.OffAxis.G72Mom234.1,
    Work.OffAxis.G72MomentClosed 6]
  norm_num

/-- `∫₀² y² |e^{sy}-2| g72 y dy ≤ 5/8` for `0 ≤ s ≤ 17/16` (the `σ`-second-derivative bound for the
Lemma 7.2 Laplace transform at `λ = 1`). -/
theorem Mtt_bound (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 17/16) :
    ∫ y in (0:ℝ)..2, y ^ 2 * |Real.exp (s * y) - 2| * Work.ZeroFreeTables.g72 y ≤ 5/8 := by
  have hpt : ∀ y ∈ Set.Icc (0:ℝ) 2,
      y ^ 2 * |Real.exp (s * y) - 2| * Work.ZeroFreeTables.g72 y
        ≤ y ^ 2 * (1 + (9/20)*y^4) * Work.ZeroFreeTables.g72 y := by
    intro y hy
    have hy0 : 0 ≤ y := hy.1
    have hy2 : y ≤ 2 := hy.2
    have hg : 0 ≤ Work.ZeroFreeTables.g72 y := Work.ZeroFreeTables.OffAxis.g72_nonneg hy0 hy2
    have h1 : |Real.exp (s*y) - 2| ≤ 1 + (9/20)*y^4 := abs_exp_2_le s y hs0 hs1 hy0 hy2
    have hy2' : (0:ℝ) ≤ y^2 := sq_nonneg y
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hy2') hg
  have hmono : (∫ y in (0:ℝ)..2, y ^ 2 * |Real.exp (s * y) - 2| * Work.ZeroFreeTables.g72 y)
      ≤ ∫ y in (0:ℝ)..2, y^2 * (1 + (9/20)*y^4) * Work.ZeroFreeTables.g72 y := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply Continuous.intervalIntegrable
      simp only [Work.ZeroFreeTables.g72]; fun_prop
    · apply Continuous.intervalIntegrable
      simp only [Work.ZeroFreeTables.g72]; fun_prop
    · exact hpt
  have hval : (∫ y in (0:ℝ)..2, y^2 * (1 + (9/20)*y^4) * Work.ZeroFreeTables.g72 y) ≤ 5/8 := by
    rw [integral_quadratic_weight]; norm_num
  linarith

end Work.OffAxis.Tf72One
