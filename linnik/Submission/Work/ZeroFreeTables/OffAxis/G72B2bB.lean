import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables

/-- **`G72B2` in its "min" form.**  With `Y ≥ min 2 (log 2 / s)` the head of the splitting
integral `∫_0^{min 2 (log 2/s)}` is contained in `[0, Y]`, so that the quadratic factor
`1 - a y - (a y)^2/2` (non-negative there by `hfac`) may be integrated up to `Y`. -/
theorem G72B2b (s σ a b Y : ℝ) (ha : 0 < a) (hY0 : 0 ≤ Y) (hY2 : Y ≤ 2)
    (hs : a ≤ s) (hsb : s ≤ b) (hb1 : b ≤ 1)
    (hy0 : min 2 (Real.log 2 / s) ≤ Y) (hfac : 0 ≤ 1 - a*Y - (a*Y)^2/2) (hσ : 0 ≤ σ) :
    Work.ZeroFreeTables.OffAxis.Isub s σ
      ≤ (Work.ZeroFreeTables.G72 (-(b : ℂ))).re - 16/9
        + (σ^2/2) * (∫ y in (0:ℝ)..Y, (1 - a*y - (a*y)^2/2) * y^2 * Work.ZeroFreeTables.g72 y) := by
  have hs_pos : 0 < s := lt_of_lt_of_le ha hs
  have hne : s ≠ 0 := ne_of_gt hs_pos
  set y0 : ℝ := Real.log 2 / s with hy0def
  set m : ℝ := min 2 y0 with hmdef
  have hm_le_y0 : m ≤ y0 := by rw [hmdef]; exact min_le_right _ _
  have hm_le_Y : m ≤ Y := hy0
  have hm_nonneg : 0 ≤ m := by
    rw [hmdef]
    exact le_min (by norm_num) (div_nonneg (Real.log_nonneg (by norm_num)) (le_of_lt hs_pos))
  have hm_le2 : m ≤ 2 := by rw [hmdef]; exact min_le_left _ _
  have hy0pos : 0 < y0 := by rw [hy0def]; exact div_pos (Real.log_pos (by norm_num)) hs_pos
  have hsy0 : s * y0 = Real.log 2 := by rw [hy0def, mul_div_cancel₀ _ hne]
  set f : ℝ → ℝ := fun y => (Real.exp (s*y) - 2) * Real.cos (σ*y) * g72 y with hf
  set F : ℝ → ℝ := fun y => (Real.exp (b*y) - 2) * g72 y with hF
  set H : ℝ → ℝ := fun y => (1 - a*y - (a*y)^2/2) * y^2 * g72 y with hH
  have hcf : Continuous f := by rw [hf]; simp only [g72]; fun_prop
  have hcF : Continuous F := by rw [hF]; simp only [g72]; fun_prop
  have hcH : Continuous H := by rw [hH]; simp only [g72]; fun_prop
  have hcSH : Continuous (fun y => (σ^2/2) * H y) := continuous_const.mul hcH
  have hIf_0m : IntervalIntegrable f MeasureTheory.volume (0:ℝ) m := hcf.intervalIntegrable _ _
  have hIf_m2 : IntervalIntegrable f MeasureTheory.volume m 2 := hcf.intervalIntegrable _ _
  have hIF_0m : IntervalIntegrable F MeasureTheory.volume (0:ℝ) m := hcF.intervalIntegrable _ _
  have hIF_m2 : IntervalIntegrable F MeasureTheory.volume m 2 := hcF.intervalIntegrable _ _
  have hIH_0m : IntervalIntegrable H MeasureTheory.volume (0:ℝ) m := hcH.intervalIntegrable _ _
  have hIH_mY : IntervalIntegrable H MeasureTheory.volume m Y := hcH.intervalIntegrable _ _
  have hIg_0m : IntervalIntegrable (fun y => F y + (σ^2/2) * H y) MeasureTheory.volume (0:ℝ) m :=
    (hcF.add hcSH).intervalIntegrable _ _
  have hG : (G72 (-(b:ℂ))).re = ∫ y in (0:ℝ)..2, Real.exp (b*y) * g72 y := by
    rw [G72_re_eq_integral (-(b:ℂ))]
    apply intervalIntegral.integral_congr
    intro y _
    have hre : (-(b:ℂ)).re = -b := by simp
    have him : (-(b:ℂ)).im = 0 := by simp
    rw [hre, him]
    simp
  have hFre : (G72 (-(b:ℂ))).re - 16/9 = ∫ y in (0:ℝ)..2, F y := by
    rw [hG, hF]
    have h16 : (16:ℝ)/9 = 2 * ∫ y in (0:ℝ)..2, g72 y := by rw [integral_g72]; norm_num
    rw [h16, ← intervalIntegral.integral_const_mul]
    have hi1 : IntervalIntegrable (fun y : ℝ => Real.exp (b*y) * g72 y)
        MeasureTheory.volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hi2 : IntervalIntegrable (fun y : ℝ => (2:ℝ) * g72 y)
        MeasureTheory.volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    rw [← intervalIntegral.integral_sub hi1 hi2]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  have hIsub : Isub s σ = ∫ y in (0:ℝ)..2, f y := Isub_eq_integral s σ
  rw [hIsub, hFre]
  have hH_nonneg : ∀ u ∈ Set.Icc (0:ℝ) Y, 0 ≤ H u := by
    intro u hu
    have hfac_u : 0 ≤ 1 - a*u - (a*u)^2/2 := by
      have h3 : a*u ≤ a*Y := mul_le_mul_of_nonneg_left hu.2 (le_of_lt ha)
      have h4 : 0 ≤ a*u := mul_nonneg (le_of_lt ha) hu.1
      have h2 : 0 ≤ (a*Y)^2 - (a*u)^2 := by
        have hx : 0 ≤ a*Y - a*u := by linarith only [h3]
        have hy : 0 ≤ a*Y + a*u := by linarith only [h3, h4]
        linarith only [mul_nonneg hx hy, hx, hy]
      linarith only [hfac, h2, h3]
    have hg : 0 ≤ g72 u := g72_nonneg hu.1 (le_trans hu.2 hY2)
    show 0 ≤ H u
    rw [hH]
    exact mul_nonneg (mul_nonneg hfac_u (sq_nonneg u)) hg
  have hhead_pt : ∀ y ∈ Set.Icc (0:ℝ) m, f y ≤ F y + (σ^2/2) * H y := by
    intro y hy
    have hyn : 0 ≤ y := hy.1
    have hym : s*y ≤ Real.log 2 := by
      have h1 : y ≤ y0 := le_trans hy.2 hm_le_y0
      have h2 : s*y ≤ s*y0 := mul_le_mul_of_nonneg_left h1 (le_of_lt hs_pos)
      rwa [hsy0] at h2
    have hgy : 0 ≤ g72 y := g72_nonneg hyn (le_trans hy.2 hm_le2)
    have hsy_nonneg : 0 ≤ s*y := mul_nonneg (le_of_lt hs_pos) hyn
    have hexp_le2 : Real.exp (s*y) ≤ 2 := by
      have h : Real.exp (s*y) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hym
      rwa [Real.exp_log (by norm_num)] at h
    have htaylor : 1 + s*y + (s*y)^2/2 ≤ Real.exp (s*y) := by
      have h := Real.sum_le_exp_of_nonneg hsy_nonneg 3
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
      norm_num at h
      linarith only [h]
    have hquad : 2 - Real.exp (s*y) ≤ 1 - a*y - (a*y)^2/2 := by
      have hay : a*y ≤ s*y := mul_le_mul_of_nonneg_right hs hyn
      have hay0 : 0 ≤ a*y := mul_nonneg (le_of_lt ha) hyn
      have h1 : 2 - Real.exp (s*y) ≤ 1 - s*y - (s*y)^2/2 := by linarith only [htaylor]
      have h2 : 1 - s*y - (s*y)^2/2 ≤ 1 - a*y - (a*y)^2/2 := by
        have hp : 0 ≤ (s*y - a*y)*(2 + s*y + a*y) :=
          mul_nonneg (sub_nonneg.mpr hay) (by linarith only [hay0, hsy_nonneg])
        linarith only [hp]
      linarith only [h1, h2, htaylor]
    have hcos : 1 - Real.cos (σ*y) ≤ (σ*y)^2/2 := by
      have h := Real.one_sub_sq_div_two_le_cos (x := σ*y)
      linarith only [h]
    have h2e : 0 ≤ 2 - Real.exp (s*y) := by linarith only [hexp_le2]
    have hsiny : Real.exp (s*y) ≤ Real.exp (b*y) := Real.exp_le_exp.mpr (by nlinarith only [hsb, hyn])
    have hsq : (0:ℝ) ≤ (σ*y)^2/2 := by positivity
    have hp : (Real.exp (s*y) - 2) * Real.cos (σ*y)
        ≤ (Real.exp (b*y) - 2) + (σ^2/2) * (1 - a*y - (a*y)^2/2) * y^2 := by
      have key : (Real.exp (s*y) - 2) * Real.cos (σ*y)
          = (Real.exp (s*y) - 2) + (2 - Real.exp (s*y)) * (1 - Real.cos (σ*y)) := by ring
      rw [key]
      have step1 : (2 - Real.exp (s*y)) * (1 - Real.cos (σ*y))
          ≤ (2 - Real.exp (s*y)) * ((σ*y)^2/2) := mul_le_mul_of_nonneg_left hcos h2e
      have step2 : (2 - Real.exp (s*y)) * ((σ*y)^2/2)
          ≤ (1 - a*y - (a*y)^2/2) * ((σ*y)^2/2) := mul_le_mul_of_nonneg_right hquad hsq
      linarith only [step1, step2, hsiny]
    show f y ≤ F y + (σ^2/2) * H y
    rw [hf, hF, hH]
    calc (Real.exp (s*y) - 2) * Real.cos (σ*y) * g72 y
        = ((Real.exp (s*y) - 2) * Real.cos (σ*y)) * g72 y := by ring
      _ ≤ ((Real.exp (b*y) - 2) + (σ^2/2) * (1 - a*y - (a*y)^2/2) * y^2) * g72 y :=
          mul_le_mul_of_nonneg_right hp hgy
      _ = (Real.exp (b*y) - 2) * g72 y + (σ^2/2) * ((1 - a*y - (a*y)^2/2) * y^2 * g72 y) := by ring
  have hhead : (∫ y in (0:ℝ)..m, f y) ≤ ∫ y in (0:ℝ)..m, (F y + (σ^2/2) * H y) :=
    intervalIntegral.integral_mono_on hm_nonneg hIf_0m hIg_0m hhead_pt
  have htail : (∫ y in m..2, f y) ≤ ∫ y in m..2, F y := by
    by_cases hy02 : y0 ≤ 2
    · have hm_eq : m = y0 := by rw [hmdef]; exact min_eq_right hy02
      rw [hm_eq]
      apply intervalIntegral.integral_mono_on hy02 (hcf.intervalIntegrable _ _)
        (hcF.intervalIntegrable _ _)
      intro y hy
      have hyn : 0 ≤ y := le_trans (le_of_lt hy0pos) hy.1
      have hly : Real.log 2 ≤ s*y := by
        have h2 : s*y0 ≤ s*y := mul_le_mul_of_nonneg_left hy.1 (le_of_lt hs_pos)
        rwa [hsy0] at h2
      have hgy : 0 ≤ g72 y := g72_nonneg hyn hy.2
      have he2 : (2:ℝ) ≤ Real.exp (s*y) := by
        have h : Real.exp (Real.log 2) ≤ Real.exp (s*y) := Real.exp_le_exp.mpr hly
        rwa [Real.exp_log (by norm_num)] at h
      have hpos : 0 ≤ Real.exp (s*y) - 2 := by linarith only [he2]
      have hcos : Real.cos (σ*y) ≤ 1 := Real.cos_le_one _
      have h1 : (Real.exp (s*y) - 2) * Real.cos (σ*y) ≤ (Real.exp (s*y) - 2) * 1 :=
        mul_le_mul_of_nonneg_left hcos hpos
      have hsiny : Real.exp (s*y) ≤ Real.exp (b*y) := Real.exp_le_exp.mpr (by nlinarith only [hsb, hyn])
      have hp : (Real.exp (s*y) - 2) * Real.cos (σ*y) ≤ Real.exp (b*y) - 2 := by
        linarith only [h1, hsiny]
      show f y ≤ F y
      rw [hf, hF]
      calc (Real.exp (s*y) - 2) * Real.cos (σ*y) * g72 y
          = ((Real.exp (s*y) - 2) * Real.cos (σ*y)) * g72 y := by ring
        _ ≤ (Real.exp (b*y) - 2) * g72 y := mul_le_mul_of_nonneg_right hp hgy
    · have hm_eq : m = 2 := by rw [hmdef]; exact min_eq_left (le_of_lt (not_le.mp hy02))
      rw [hm_eq, intervalIntegral.integral_same, intervalIntegral.integral_same]
  have hstep : (∫ y in (0:ℝ)..m, (F y + (σ^2/2) * H y))
      = (∫ y in (0:ℝ)..m, F y) + (σ^2/2) * (∫ y in (0:ℝ)..m, H y) := by
    rw [intervalIntegral.integral_add hIF_0m (hcSH.intervalIntegrable 0 m),
        intervalIntegral.integral_const_mul]
  have hadj : (∫ y in (0:ℝ)..m, F y) + (∫ y in m..2, F y) = ∫ y in (0:ℝ)..2, F y :=
    intervalIntegral.integral_add_adjacent_intervals hIF_0m hIF_m2
  have hHY : (∫ y in (0:ℝ)..m, H y) ≤ ∫ y in (0:ℝ)..Y, H y := by
    have hadj2 : (∫ y in (0:ℝ)..m, H y) + (∫ y in m..Y, H y) = ∫ y in (0:ℝ)..Y, H y :=
      intervalIntegral.integral_add_adjacent_intervals hIH_0m hIH_mY
    have hnn : 0 ≤ ∫ y in m..Y, H y := by
      apply intervalIntegral.integral_nonneg hm_le_Y
      intro u hu
      exact hH_nonneg u ⟨le_trans hm_nonneg hu.1, hu.2⟩
    rw [← hadj2]; exact le_add_of_nonneg_right hnn
  have hss : 0 ≤ σ^2/2 := by positivity
  calc (∫ y in (0:ℝ)..2, f y)
      = (∫ y in (0:ℝ)..m, f y) + (∫ y in m..2, f y) :=
        (intervalIntegral.integral_add_adjacent_intervals hIf_0m hIf_m2).symm
    _ ≤ (∫ y in (0:ℝ)..m, (F y + (σ^2/2) * H y)) + (∫ y in m..2, F y) := add_le_add hhead htail
    _ = (∫ y in (0:ℝ)..2, F y) + (σ^2/2) * (∫ y in (0:ℝ)..m, H y) := by
        rw [hstep, ← hadj]; ring
    _ ≤ (∫ y in (0:ℝ)..2, F y) + (σ^2/2) * (∫ y in (0:ℝ)..Y, H y) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hHY hss)

end Work.ZeroFreeTables.OffAxis
