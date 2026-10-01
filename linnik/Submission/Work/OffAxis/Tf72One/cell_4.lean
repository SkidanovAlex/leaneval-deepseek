/-
# OffAxis/Tf72One/cell_4

HB (10.8) on the box `σ ∈ [13/4, 7/2]`:  for `0 ≤ s ≤ 17/16` and `t ∈ [13/4, 7/2]`,
`Isub s t ≤ 1/100`.

The two interpolation lemmas `interp_s_axfree`, `interp_t_axfree` below are axiom-free
restatements of `Isub_le_interp_s` / `Isub_le_interp_t` (whose current proofs in the
workspace still rest on `sorry`).  They are obtained from `abs_interp_error_le` applied
pointwise in `y` (with `|∂²_s Isub| ≤ ∫ y²e^{s₁y}g72 ≤ 13/10` from `Mss_bound`, resp.
`|∂²_t Isub| ≤ ∫ y²|e^{sy}-2|g72 ≤ 5/8` from `Mtt_bound`), then integrated.
-/
import Mathlib
import Submission.Work.OffAxis.Tf72One.corner_mid
import Submission.Work.OffAxis.Tf72One.abs_interp_error_le
import Submission.Work.OffAxis.Tf72One.Mss_bound
import Submission.Work.OffAxis.Tf72One.Mtt_bound

open scoped Interval
open MeasureTheory
open Work.ZeroFreeTables
open Work.ZeroFreeTables.OffAxis

namespace Work.OffAxis.Tf72One

/-- Pointwise (in `y`) linear-interpolation error bound for `u ↦ e^{uy}` on `[s0,s1]`. -/
lemma exp_interp_abs (s s0 s1 y : ℝ) (hs0 : s0 ≤ s) (hs1 : s ≤ s1) (h01 : s0 < s1) (hy : 0 ≤ y) :
    |Real.exp (s*y) - ((s1-s)/(s1-s0)*Real.exp (s0*y) + (s-s0)/(s1-s0)*Real.exp (s1*y))|
      ≤ (s1-s0)^2/8 * (y^2 * Real.exp (s1*y)) := by
  have hx : s ∈ Set.Icc s0 s1 := ⟨hs0, hs1⟩
  have hf : ContDiffOn ℝ 2 (fun u : ℝ => Real.exp (u * y)) (Set.Icc s0 s1) := by fun_prop
  have hbd : ∀ u ∈ Set.Ioo s0 s1,
      |iteratedDeriv 2 (fun u : ℝ => Real.exp (u * y)) u| ≤ y^2 * Real.exp (s1*y) := by
    intro u hu
    have hu1 : u ≤ s1 := le_of_lt hu.2
    have h : (fun u : ℝ => Real.exp (u * y)) = (fun u : ℝ => Real.exp (y * u)) := by
      funext u; rw [mul_comm]
    rw [h, iteratedDeriv_exp_const_mul]
    rw [abs_mul, abs_of_nonneg (sq_nonneg y), abs_of_pos (Real.exp_pos (y*u))]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [hu1, hy])) (sq_nonneg y)
  exact abs_interp_error_le (fun u : ℝ => Real.exp (u * y))
      s0 s1 s (y^2 * Real.exp (s1*y)) h01 hx hf hbd

/-- Pointwise (in `y`) linear-interpolation error bound for `u ↦ cos (uy)` on `[t0,t1]`. -/
lemma cos_interp_abs (t t0 t1 y : ℝ) (ht0 : t0 ≤ t) (ht1 : t ≤ t1) (h01 : t0 < t1) :
    |Real.cos (t*y) - ((t1-t)/(t1-t0)*Real.cos (t0*y) + (t-t0)/(t1-t0)*Real.cos (t1*y))|
      ≤ (t1-t0)^2/8 * y^2 := by
  have hx : t ∈ Set.Icc t0 t1 := ⟨ht0, ht1⟩
  have hf : ContDiffOn ℝ 2 (fun u : ℝ => Real.cos (u * y)) (Set.Icc t0 t1) := by fun_prop
  have hbd : ∀ u ∈ Set.Ioo t0 t1,
      |iteratedDeriv 2 (fun u : ℝ => Real.cos (u * y)) u| ≤ y^2 := by
    intro u _
    have h : (fun u : ℝ => Real.cos (u * y)) = (fun u : ℝ => Real.cos (y * u)) := by
      funext u; rw [mul_comm]
    rw [h, iteratedDeriv_comp_const_mul Real.contDiff_cos y]
    rw [abs_mul, abs_of_nonneg (sq_nonneg y)]
    calc y^2 * |iteratedDeriv 2 Real.cos (y*u)| ≤ y^2 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg y)
          exact Real.abs_iteratedDeriv_cos_le_one 2 (y*u)
      _ = y^2 := by ring
  exact abs_interp_error_le (fun u : ℝ => Real.cos (u * y))
      t0 t1 t (y^2) h01 hx hf hbd

/-- **`s`-interpolation for `Isub` (axiom-free).** -/
theorem interp_s_axfree (s t s0 s1 : ℝ) (hs0 : s0 ≤ s) (hs1 : s ≤ s1)
    (h0 : 0 ≤ s0) (h17 : s1 ≤ 17/16) :
    Isub s t ≤
      max (Isub s0 t) (Isub s1 t) + (s1 - s0) ^ 2 / 8 * (13/10) := by
  rcases lt_or_ge s0 s1 with h01 | hle
  · have hsd : (0:ℝ) < s1 - s0 := by linarith
    have h0w : 0 ≤ (s1-s)/(s1-s0) := div_nonneg (by linarith) (le_of_lt hsd)
    have h1w : 0 ≤ (s-s0)/(s1-s0) := div_nonneg (by linarith) (le_of_lt hsd)
    have hsum : (s1-s)/(s1-s0) + (s-s0)/(s1-s0) = 1 := by
      rw [← add_div, show s1 - s + (s - s0) = s1 - s0 by ring, div_self (ne_of_gt hsd)]
    have hpt : ∀ y ∈ Set.Icc (0:ℝ) 2,
        (Real.exp (s*y)-2)*Real.cos (t*y)*g72 y ≤
          (s1-s)/(s1-s0) * ((Real.exp (s0*y)-2)*Real.cos (t*y)*g72 y)
          + (s-s0)/(s1-s0) * ((Real.exp (s1*y)-2)*Real.cos (t*y)*g72 y)
          + (s1-s0)^2/8 * (y^2 * Real.exp (s1*y) * g72 y) := by
      intro y hy
      have hy0 : 0 ≤ y := hy.1
      have hgy : 0 ≤ g72 y := g72_nonneg hy.1 hy.2
      set Lin : ℝ := (s1-s)/(s1-s0)*Real.exp (s0*y) + (s-s0)/(s1-s0)*Real.exp (s1*y) with hLin
      set E : ℝ := (s1-s0)^2/8 * (y^2 * Real.exp (s1*y)) with hEdef
      have hE : |Real.exp (s*y) - Lin| ≤ E := by
        rw [hLin, hEdef]; exact exp_interp_abs s s0 s1 y hs0 hs1 h01 hy0
      have hE0 : 0 ≤ E := by rw [hEdef]; positivity
      have hWabs : |Real.cos (t*y) * g72 y| ≤ g72 y := by
        rw [abs_mul, abs_of_nonneg hgy]
        calc |Real.cos (t*y)| * g72 y ≤ 1 * g72 y :=
              mul_le_mul_of_nonneg_right (Real.abs_cos_le_one (t*y)) hgy
          _ = g72 y := one_mul _
      have key : (Real.exp (s*y) - Lin) * (Real.cos (t*y) * g72 y) ≤ E * g72 y := by
        calc (Real.exp (s*y) - Lin) * (Real.cos (t*y) * g72 y)
            ≤ |(Real.exp (s*y) - Lin) * (Real.cos (t*y) * g72 y)| := le_abs_self _
          _ = |Real.exp (s*y) - Lin| * |Real.cos (t*y) * g72 y| := abs_mul _ _
          _ ≤ E * g72 y := mul_le_mul hE hWabs (abs_nonneg _) hE0
      have hLin2 : Lin - 2 =
          (s1-s)/(s1-s0)*(Real.exp (s0*y)-2) + (s-s0)/(s1-s0)*(Real.exp (s1*y)-2) := by
        rw [hLin]
        have e0 : (s1-s)/(s1-s0) * Real.exp (s0*y) + (s-s0)/(s1-s0) * Real.exp (s1*y)
            = (s1-s)/(s1-s0)*(Real.exp (s0*y)-2) + (s-s0)/(s1-s0)*(Real.exp (s1*y)-2)
              + 2*((s1-s)/(s1-s0) + (s-s0)/(s1-s0)) := by ring
        rw [e0, hsum]; ring
      have step : (Lin - 2) * (Real.cos (t*y) * g72 y)
          = (s1-s)/(s1-s0) * ((Real.exp (s0*y)-2)*Real.cos (t*y)*g72 y)
            + (s-s0)/(s1-s0) * ((Real.exp (s1*y)-2)*Real.cos (t*y)*g72 y) := by
        rw [hLin2]; ring
      calc (Real.exp (s*y)-2)*Real.cos (t*y)*g72 y
          = (Real.exp (s*y) - Lin) * (Real.cos (t*y) * g72 y)
            + (Lin-2)*(Real.cos (t*y) * g72 y) := by ring
        _ ≤ E * g72 y + ((s1-s)/(s1-s0) * ((Real.exp (s0*y)-2)*Real.cos (t*y)*g72 y)
              + (s-s0)/(s1-s0) * ((Real.exp (s1*y)-2)*Real.cos (t*y)*g72 y)) := by
            rw [step]; linarith [key]
        _ = (s1-s)/(s1-s0) * ((Real.exp (s0*y)-2)*Real.cos (t*y)*g72 y)
              + (s-s0)/(s1-s0) * ((Real.exp (s1*y)-2)*Real.cos (t*y)*g72 y)
              + (s1-s0)^2/8 * (y^2 * Real.exp (s1*y) * g72 y) := by
            rw [hEdef]; ring
    have hI0 : IntervalIntegrable
        (fun y : ℝ => (Real.exp (s0*y) - 2) * Real.cos (t*y) * g72 y) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hI1 : IntervalIntegrable
        (fun y : ℝ => (Real.exp (s1*y) - 2) * Real.cos (t*y) * g72 y) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hIe : IntervalIntegrable
        (fun y : ℝ => y^2 * Real.exp (s1*y) * g72 y) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hIt : IntervalIntegrable
        (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hIg : IntervalIntegrable (fun y : ℝ =>
        (s1-s)/(s1-s0) * ((Real.exp (s0*y)-2)*Real.cos (t*y)*g72 y)
        + (s-s0)/(s1-s0) * ((Real.exp (s1*y)-2)*Real.cos (t*y)*g72 y)
        + (s1-s0)^2/8 * (y^2 * Real.exp (s1*y) * g72 y)) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hmono := intervalIntegral.integral_mono_on (show (0:ℝ) ≤ 2 by norm_num) hIt hIg hpt
    have hFsym : (∫ y in (0:ℝ)..2, (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y)
        = Isub s t := (Isub_eq_integral s t).symm
    rw [hFsym] at hmono
    have hGrew : (∫ y in (0:ℝ)..2,
        (s1-s)/(s1-s0) * ((Real.exp (s0*y)-2)*Real.cos (t*y)*g72 y)
        + (s-s0)/(s1-s0) * ((Real.exp (s1*y)-2)*Real.cos (t*y)*g72 y)
        + (s1-s0)^2/8 * (y^2 * Real.exp (s1*y) * g72 y))
      = (s1-s)/(s1-s0) * Isub s0 t + (s-s0)/(s1-s0) * Isub s1 t
        + (s1-s0)^2/8 * (∫ y in (0:ℝ)..2, y^2 * Real.exp (s1*y) * g72 y) := by
      rw [intervalIntegral.integral_add ((hI0.const_mul _).add (hI1.const_mul _)) (hIe.const_mul _),
          intervalIntegral.integral_add (hI0.const_mul _) (hI1.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul,
          ← Isub_eq_integral s0 t, ← Isub_eq_integral s1 t]
    rw [hGrew] at hmono
    have hEm : (∫ y in (0:ℝ)..2, y^2 * Real.exp (s1*y) * g72 y) ≤ 13/10 :=
      Mss_bound s1 (le_trans h0 (le_of_lt h01)) h17
    have hmax : (s1-s)/(s1-s0) * Isub s0 t + (s-s0)/(s1-s0) * Isub s1 t
        ≤ max (Isub s0 t) (Isub s1 t) := by
      calc (s1-s)/(s1-s0) * Isub s0 t + (s-s0)/(s1-s0) * Isub s1 t
          ≤ (s1-s)/(s1-s0) * max (Isub s0 t) (Isub s1 t)
            + (s-s0)/(s1-s0) * max (Isub s0 t) (Isub s1 t) :=
            add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h0w)
              (mul_le_mul_of_nonneg_left (le_max_right _ _) h1w)
        _ = max (Isub s0 t) (Isub s1 t) := by rw [← add_mul, hsum, one_mul]
    have hstep : (s1-s0)^2/8 * (∫ y in (0:ℝ)..2, y^2 * Real.exp (s1*y) * g72 y)
        ≤ (s1-s0)^2/8 * (13/10) := mul_le_mul_of_nonneg_left hEm (by positivity)
    linarith [hmono, hmax, hstep]
  · have hs0s1 : s0 ≤ s1 := le_trans hs0 hs1
    have h1 : s1 = s0 := le_antisymm hle hs0s1
    have h2 : s = s0 := le_antisymm (hs1.trans_eq h1) hs0
    rw [h1, h2]; simp

/-- **`σ`-interpolation for `Isub` (axiom-free).** -/
theorem interp_t_axfree (s t t0 t1 : ℝ) (hs0 : 0 ≤ s) (hs17 : s ≤ 17/16)
    (ht0 : t0 ≤ t) (ht1 : t ≤ t1) :
    Isub s t ≤
      max (Isub s t0) (Isub s t1) + (t1 - t0) ^ 2 / 8 * (5/8) := by
  rcases lt_or_ge t0 t1 with h01 | hle
  · have htd : (0:ℝ) < t1 - t0 := by linarith
    have h0w : 0 ≤ (t1-t)/(t1-t0) := div_nonneg (by linarith) (le_of_lt htd)
    have h1w : 0 ≤ (t-t0)/(t1-t0) := div_nonneg (by linarith) (le_of_lt htd)
    have hsum : (t1-t)/(t1-t0) + (t-t0)/(t1-t0) = 1 := by
      rw [← add_div, show t1 - t + (t - t0) = t1 - t0 by ring, div_self (ne_of_gt htd)]
    have hpt : ∀ y ∈ Set.Icc (0:ℝ) 2,
        (Real.exp (s*y)-2)*Real.cos (t*y)*g72 y ≤
          (t1-t)/(t1-t0) * ((Real.exp (s*y)-2)*Real.cos (t0*y)*g72 y)
          + (t-t0)/(t1-t0) * ((Real.exp (s*y)-2)*Real.cos (t1*y)*g72 y)
          + (t1-t0)^2/8 * (y^2 * |Real.exp (s*y)-2| * g72 y) := by
      intro y hy
      have hgy : 0 ≤ g72 y := g72_nonneg hy.1 hy.2
      set A : ℝ := (Real.exp (s*y)-2)*g72 y with hA
      set Lin : ℝ := (t1-t)/(t1-t0)*Real.cos (t0*y) + (t-t0)/(t1-t0)*Real.cos (t1*y) with hLin
      set E : ℝ := (t1-t0)^2/8 * y^2 with hEdef
      have hEc : |Real.cos (t*y) - Lin| ≤ E := by
        rw [hLin, hEdef]; exact cos_interp_abs t t0 t1 y ht0 ht1 h01
      have hE0 : 0 ≤ E := by rw [hEdef]; positivity
      have hAabs : |A| = |Real.exp (s*y)-2| * g72 y := by
        rw [hA, abs_mul, abs_of_nonneg hgy]
      have key : A * (Real.cos (t*y) - Lin) ≤ |A| * E := by
        calc A * (Real.cos (t*y) - Lin) ≤ |A * (Real.cos (t*y) - Lin)| := le_abs_self _
          _ = |A| * |Real.cos (t*y) - Lin| := abs_mul _ _
          _ ≤ |A| * E := mul_le_mul_of_nonneg_left hEc (abs_nonneg A)
      calc (Real.exp (s*y)-2)*Real.cos (t*y)*g72 y
          = A * Real.cos (t*y) := by rw [hA]; ring
        _ = A * Lin + A * (Real.cos (t*y) - Lin) := by ring
        _ ≤ A * Lin + |A| * E := by linarith [key]
        _ = (t1-t)/(t1-t0) * ((Real.exp (s*y)-2)*Real.cos (t0*y)*g72 y)
              + (t-t0)/(t1-t0) * ((Real.exp (s*y)-2)*Real.cos (t1*y)*g72 y)
              + (t1-t0)^2/8 * (y^2 * |Real.exp (s*y)-2| * g72 y) := by
            rw [hAabs, hA, hLin, hEdef]; ring
    have hIt : IntervalIntegrable
        (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hI0 : IntervalIntegrable
        (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (t0*y) * g72 y) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hI1 : IntervalIntegrable
        (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (t1*y) * g72 y) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hIe : IntervalIntegrable
        (fun y : ℝ => y^2 * |Real.exp (s*y) - 2| * g72 y) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hIg : IntervalIntegrable (fun y : ℝ =>
        (t1-t)/(t1-t0) * ((Real.exp (s*y)-2)*Real.cos (t0*y)*g72 y)
        + (t-t0)/(t1-t0) * ((Real.exp (s*y)-2)*Real.cos (t1*y)*g72 y)
        + (t1-t0)^2/8 * (y^2 * |Real.exp (s*y)-2| * g72 y)) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hmono := intervalIntegral.integral_mono_on (show (0:ℝ) ≤ 2 by norm_num) hIt hIg hpt
    have hFsym : (∫ y in (0:ℝ)..2, (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y)
        = Isub s t := (Isub_eq_integral s t).symm
    rw [hFsym] at hmono
    have hGrew : (∫ y in (0:ℝ)..2,
        (t1-t)/(t1-t0) * ((Real.exp (s*y)-2)*Real.cos (t0*y)*g72 y)
        + (t-t0)/(t1-t0) * ((Real.exp (s*y)-2)*Real.cos (t1*y)*g72 y)
        + (t1-t0)^2/8 * (y^2 * |Real.exp (s*y)-2| * g72 y))
      = (t1-t)/(t1-t0) * Isub s t0 + (t-t0)/(t1-t0) * Isub s t1
        + (t1-t0)^2/8 * (∫ y in (0:ℝ)..2, y^2 * |Real.exp (s*y)-2| * g72 y) := by
      rw [intervalIntegral.integral_add ((hI0.const_mul _).add (hI1.const_mul _)) (hIe.const_mul _),
          intervalIntegral.integral_add (hI0.const_mul _) (hI1.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul,
          ← Isub_eq_integral s t0, ← Isub_eq_integral s t1]
    rw [hGrew] at hmono
    have hEm : (∫ y in (0:ℝ)..2, y^2 * |Real.exp (s*y) - 2| * g72 y) ≤ 5/8 :=
      Mtt_bound s hs0 hs17
    have hmax : (t1-t)/(t1-t0) * Isub s t0 + (t-t0)/(t1-t0) * Isub s t1
        ≤ max (Isub s t0) (Isub s t1) := by
      calc (t1-t)/(t1-t0) * Isub s t0 + (t-t0)/(t1-t0) * Isub s t1
          ≤ (t1-t)/(t1-t0) * max (Isub s t0) (Isub s t1)
            + (t-t0)/(t1-t0) * max (Isub s t0) (Isub s t1) :=
            add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h0w)
              (mul_le_mul_of_nonneg_left (le_max_right _ _) h1w)
        _ = max (Isub s t0) (Isub s t1) := by rw [← add_mul, hsum, one_mul]
    have hstep : (t1-t0)^2/8 * (∫ y in (0:ℝ)..2, y^2 * |Real.exp (s*y) - 2| * g72 y)
        ≤ (t1-t0)^2/8 * (5/8) := mul_le_mul_of_nonneg_left hEm (by positivity)
    linarith [hmono, hmax, hstep]
  · have ht0t1 : t0 ≤ t1 := le_trans ht0 ht1
    have h1 : t1 = t0 := le_antisymm hle ht0t1
    have h2 : t = t0 := le_antisymm (ht1.trans_eq h1) ht0
    rw [h1, h2]; simp

/-- Glue: if `Isub` is `≤ -7/200` at the four corners `(s0,13/4)`, `(s0,7/2)`, `(s1,13/4)`,
`(s1,7/2)` of `[s0,s1] × [13/4,7/2]` (with `[s0,s1] ⊆ [0,17/16]` and `(s1-s0)² ≤ 9/400`), then
`Isub s t ≤ 1/100` on the whole box. -/
private lemma box_bound (s t s0 s1 : ℝ) (hs0 : s0 ≤ s) (hs1 : s ≤ s1) (h0 : 0 ≤ s0)
    (h17 : s1 ≤ 17/16) (hsq : (s1 - s0)^2 ≤ 9/400) (ht0 : 13/4 ≤ t) (ht1 : t ≤ 7/2)
    (h00 : Isub s0 (13/4) ≤ -7/200) (h01 : Isub s0 (7/2) ≤ -7/200)
    (h10 : Isub s1 (13/4) ≤ -7/200) (h11 : Isub s1 (7/2) ≤ -7/200) :
    Isub s t ≤ 1/100 := by
  have hs1' : 0 ≤ s1 := le_trans h0 (le_trans hs0 hs1)
  have hs017 : s0 ≤ 17/16 := le_trans hs0 (le_trans hs1 h17)
  have hIs := interp_s_axfree s t s0 s1 hs0 hs1 h0 h17
  have h0t := interp_t_axfree s0 t (13/4) (7/2) h0 hs017 ht0 ht1
  have h1t := interp_t_axfree s1 t (13/4) (7/2) hs1' h17 ht0 ht1
  have h45 : (7/2 - (13/4:ℝ))^2/8*(5/8) = 5/1024 := by norm_num
  have hb0 : max (Isub s0 t) (Isub s1 t) ≤ -7/200 + 5/1024 := by
    apply max_le
    · linarith [h0t, max_le h00 h01, h45]
    · linarith [h1t, max_le h10 h11, h45]
  have hcm : (s1 - s0)^2/8*(13/10) ≤ (9/400)/8*(13/10) := by nlinarith [hsq]
  have hfin : -7/200 + 5/1024 + (9/400)/8*(13/10) ≤ 1/100 := by norm_num
  linarith [hIs, hb0, hcm, hfin]

/-- **HB (10.8) on the box `σ ∈ [13/4, 7/2]`.**  For `0 ≤ s ≤ 17/16` and `t ∈ [13/4, 7/2]`,
`Isub s t ≤ 1/100`.

Proof route: split `s` into the eight intervals of the grid
`0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16` and on each apply the box bound with the four
corner bounds from `corner_mid` (`-7/200` at `σ = 13/4` and `σ = 7/2`); the interpolation error
`(3/20)²/8·(13/10) + (1/4)²/8·(5/8) = 0.00854` gives `-0.0265 ≤ 1/100`. -/
theorem cell_4 (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 17/16) (ht0 : 13/4 ≤ t) (ht1 : t ≤ 7/2) :
    Work.ZeroFreeTables.OffAxis.Isub s t ≤ 1/100 := by
  have h13 : (13/4 : ℝ) ∈ ({3, 13/4, 7/2} : Finset ℝ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton]
  have h72 : (7/2 : ℝ) ∈ ({3, 13/4, 7/2} : Finset ℝ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton]
  have m0 : (0:ℝ) ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton]
  have m1 : (3/20:ℝ) ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton]
  have m2 : (3/10:ℝ) ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton]
  have m3 : (9/20:ℝ) ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton]
  have m4 : (3/5:ℝ) ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton]
  have m5 : (3/4:ℝ) ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton]
  have m6 : (9/10:ℝ) ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton]
  have m7 : (21/20:ℝ) ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton]
  have m8 : (17/16:ℝ) ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton]
  rcases le_or_gt s (3/20) with h | h
  · exact box_bound s t 0 (3/20) hs0 h (by norm_num) (by norm_num) (by norm_num) ht0 ht1
      (corner_mid 0 (13/4) m0 h13) (corner_mid 0 (7/2) m0 h72)
      (corner_mid (3/20) (13/4) m1 h13) (corner_mid (3/20) (7/2) m1 h72)
  · rcases le_or_gt s (3/10) with h' | h'
    · exact box_bound s t (3/20) (3/10) (le_of_lt h) h' (by norm_num) (by norm_num) (by norm_num)
        ht0 ht1 (corner_mid (3/20) (13/4) m1 h13) (corner_mid (3/20) (7/2) m1 h72)
        (corner_mid (3/10) (13/4) m2 h13) (corner_mid (3/10) (7/2) m2 h72)
    · rcases le_or_gt s (9/20) with h'' | h''
      · exact box_bound s t (3/10) (9/20) (le_of_lt h') h'' (by norm_num) (by norm_num) (by norm_num)
          ht0 ht1 (corner_mid (3/10) (13/4) m2 h13) (corner_mid (3/10) (7/2) m2 h72)
          (corner_mid (9/20) (13/4) m3 h13) (corner_mid (9/20) (7/2) m3 h72)
      · rcases le_or_gt s (3/5) with h3 | h3
        · exact box_bound s t (9/20) (3/5) (le_of_lt h'') h3 (by norm_num) (by norm_num) (by norm_num)
            ht0 ht1 (corner_mid (9/20) (13/4) m3 h13) (corner_mid (9/20) (7/2) m3 h72)
            (corner_mid (3/5) (13/4) m4 h13) (corner_mid (3/5) (7/2) m4 h72)
        · rcases le_or_gt s (3/4) with h4 | h4
          · exact box_bound s t (3/5) (3/4) (le_of_lt h3) h4 (by norm_num) (by norm_num) (by norm_num)
              ht0 ht1 (corner_mid (3/5) (13/4) m4 h13) (corner_mid (3/5) (7/2) m4 h72)
              (corner_mid (3/4) (13/4) m5 h13) (corner_mid (3/4) (7/2) m5 h72)
          · rcases le_or_gt s (9/10) with h5 | h5
            · exact box_bound s t (3/4) (9/10) (le_of_lt h4) h5 (by norm_num) (by norm_num) (by norm_num)
                ht0 ht1 (corner_mid (3/4) (13/4) m5 h13) (corner_mid (3/4) (7/2) m5 h72)
                (corner_mid (9/10) (13/4) m6 h13) (corner_mid (9/10) (7/2) m6 h72)
            · rcases le_or_gt s (21/20) with h6 | h6
              · exact box_bound s t (9/10) (21/20) (le_of_lt h5) h6 (by norm_num) (by norm_num) (by norm_num)
                  ht0 ht1 (corner_mid (9/10) (13/4) m6 h13) (corner_mid (9/10) (7/2) m6 h72)
                  (corner_mid (21/20) (13/4) m7 h13) (corner_mid (21/20) (7/2) m7 h72)
              · exact box_bound s t (21/20) (17/16) (le_of_lt h6) hs1 (by norm_num) (by norm_num)
                  (by norm_num) ht0 ht1 (corner_mid (21/20) (13/4) m7 h13) (corner_mid (21/20) (7/2) m7 h72)
                  (corner_mid (17/16) (13/4) m8 h13) (corner_mid (17/16) (7/2) m8 h72)

end Work.OffAxis.Tf72One
