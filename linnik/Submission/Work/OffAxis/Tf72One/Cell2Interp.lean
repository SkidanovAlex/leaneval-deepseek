/-
# OffAxis/Tf72One/Cell2Interp

Sorry-free integrated two-point interpolation bounds for `Isub`, obtained by integrating the
pointwise bounds `integrand_interp_t_cell2` / `integrand_interp_s_cell2` of `Cell2Ptwise`
over `y ∈ [0,2]` and using `Mtt_bound` (resp. `Mss_bound`) for the resulting moment.
-/
import Mathlib
import Submission.Work.OffAxis.Tf72One.Cell2Ptwise
import Submission.Work.OffAxis.Tf72One.Mss_bound
import Submission.Work.OffAxis.Tf72One.Mtt_bound

open scoped Interval
open MeasureTheory

namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables Work.ZeroFreeTables.OffAxis

/-- **Auxiliary: `t`-interpolation for `Isub`** with the second-derivative moment bound `M`
supplied as a hypothesis. -/
theorem isub_le_interp_aux_t_cell2 (s t a b : ℝ) (hab : a < b) (hta : a ≤ t) (htb : t ≤ b)
    (hM : ∫ y in (0:ℝ)..2, y ^ 2 * |Real.exp (s * y) - 2| * g72 y ≤ 5/8) :
    Isub s t ≤ max (Isub s a) (Isub s b) + (b - a) ^ 2 / 8 * (5/8) := by
  have hba : (0:ℝ) < b - a := by linarith
  have hIt : IntervalIntegrable (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]; fun_prop
  have hIa : IntervalIntegrable (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (a*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]; fun_prop
  have hIb : IntervalIntegrable (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (b*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]; fun_prop
  have hIe : IntervalIntegrable (fun y : ℝ => y^2 * |Real.exp (s*y) - 2| * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]; fun_prop
  have hpt : ∀ y ∈ Set.Icc (0:ℝ) 2,
      (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y ≤
        (b - t) / (b - a) * ((Real.exp (s*y) - 2) * Real.cos (a*y) * g72 y)
        + (t - a) / (b - a) * ((Real.exp (s*y) - 2) * Real.cos (b*y) * g72 y)
        + (b - a)^2 / 8 * (y^2 * |Real.exp (s*y) - 2| * g72 y) :=
    fun y hy => integrand_interp_t_cell2 s t a b y hab hta htb hy
  have hsumI : IntervalIntegrable
      (fun y : ℝ => (b - t)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (a*y) * g72 y)
        + (t - a)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (b*y) * g72 y)
        + (b - a)^2/8 * (y^2 * |Real.exp (s*y) - 2| * g72 y)) volume (0:ℝ) 2 :=
    ((hIa.const_mul _).add (hIb.const_mul _)).add (hIe.const_mul _)
  have hmono := intervalIntegral.integral_mono_on (show (0:ℝ) ≤ 2 by norm_num) hIt hsumI hpt
  have hsplit : (∫ y in (0:ℝ)..2, ((b - t)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (a*y) * g72 y)
        + (t - a)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (b*y) * g72 y)
        + (b - a)^2/8 * (y^2 * |Real.exp (s*y) - 2| * g72 y)))
      = (b - t)/(b - a) * Isub s a
        + (t - a)/(b - a) * Isub s b
        + (b - a)^2/8 * (∫ y in (0:ℝ)..2, y^2 * |Real.exp (s*y) - 2| * g72 y) := by
    rw [intervalIntegral.integral_add ((hIa.const_mul _).add (hIb.const_mul _)) (hIe.const_mul _),
        intervalIntegral.integral_add (hIa.const_mul _) (hIb.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        ← Isub_eq_integral s a, ← Isub_eq_integral s b]
  rw [hsplit, ← Isub_eq_integral s t] at hmono
  have h0 : 0 ≤ (b - t)/(b - a) := div_nonneg (by linarith) (le_of_lt hba)
  have h1 : 0 ≤ (t - a)/(b - a) := div_nonneg (by linarith) (le_of_lt hba)
  have hsum : (b - t)/(b - a) + (t - a)/(b - a) = 1 := by
    rw [← add_div, show b - t + (t - a) = b - a by ring, div_self (ne_of_gt hba)]
  have hmax : (b - t)/(b - a) * Isub s a + (t - a)/(b - a) * Isub s b
      ≤ max (Isub s a) (Isub s b) := by
    have hMx : (b - t)/(b - a) * Isub s a + (t - a)/(b - a) * Isub s b
        ≤ (b - t)/(b - a) * max (Isub s a) (Isub s b)
          + (t - a)/(b - a) * max (Isub s a) (Isub s b) :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h0)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) h1)
    calc (b - t)/(b - a) * Isub s a + (t - a)/(b - a) * Isub s b
        ≤ _ := hMx
      _ = max (Isub s a) (Isub s b) := by rw [← add_mul, hsum, one_mul]
  have herr : (b - a)^2/8 * (∫ y in (0:ℝ)..2, y^2 * |Real.exp (s*y) - 2| * g72 y)
      ≤ (b - a)^2/8 * (5/8) := mul_le_mul_of_nonneg_left hM (by positivity)
  linarith [hmono, hmax, herr]

/-- **`σ`-interpolation for `Isub`** (`t`-direction). -/
theorem Isub_le_interp_t_cell2 (s t t0 t1 : ℝ) (hs0 : 0 ≤ s) (hs17 : s ≤ 17/16)
    (ht0 : t0 ≤ t) (ht1 : t ≤ t1) :
    Isub s t ≤ max (Isub s t0) (Isub s t1) + (t1 - t0) ^ 2 / 8 * (5/8) := by
  rcases lt_or_ge t0 t1 with h | h
  · exact isub_le_interp_aux_t_cell2 s t t0 t1 h ht0 ht1 (Mtt_bound s hs0 hs17)
  · have ht1t0 : t1 = t0 := le_antisymm h (le_trans ht0 ht1)
    have htt0 : t = t0 := le_antisymm (by rw [ht1t0] at ht1; exact ht1) ht0
    rw [htt0, ht1t0]
    simp

/-- **Auxiliary: `s`-interpolation for `Isub`** with the moment bound supplied. -/
theorem isub_le_interp_aux_s_cell2 (s t s0 s1 : ℝ) (hab : s0 < s1) (hs0 : s0 ≤ s) (hs1 : s ≤ s1)
    (hM : ∫ y in (0:ℝ)..2, y ^ 2 * Real.exp (s1 * y) * g72 y ≤ 13/10) :
    Isub s t ≤ max (Isub s0 t) (Isub s1 t) + (s1 - s0) ^ 2 / 8 * (13/10) := by
  have hba : (0:ℝ) < s1 - s0 := by linarith
  have hIt : IntervalIntegrable (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]; fun_prop
  have hI0 : IntervalIntegrable (fun y : ℝ => (Real.exp (s0*y) - 2) * Real.cos (t*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]; fun_prop
  have hI1 : IntervalIntegrable (fun y : ℝ => (Real.exp (s1*y) - 2) * Real.cos (t*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]; fun_prop
  have hIe : IntervalIntegrable (fun y : ℝ => y^2 * Real.exp (s1*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]; fun_prop
  have hpt : ∀ y ∈ Set.Icc (0:ℝ) 2,
      (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y ≤
        (s1 - s) / (s1 - s0) * ((Real.exp (s0*y) - 2) * Real.cos (t*y) * g72 y)
        + (s - s0) / (s1 - s0) * ((Real.exp (s1*y) - 2) * Real.cos (t*y) * g72 y)
        + (s1 - s0)^2 / 8 * (y^2 * Real.exp (s1*y) * g72 y) :=
    fun y hy => integrand_interp_s_cell2 s t s0 s1 y hab hs0 hs1 hy
  have hsumI : IntervalIntegrable
      (fun y : ℝ => (s1 - s)/(s1 - s0) * ((Real.exp (s0*y) - 2) * Real.cos (t*y) * g72 y)
        + (s - s0)/(s1 - s0) * ((Real.exp (s1*y) - 2) * Real.cos (t*y) * g72 y)
        + (s1 - s0)^2/8 * (y^2 * Real.exp (s1*y) * g72 y)) volume (0:ℝ) 2 :=
    ((hI0.const_mul _).add (hI1.const_mul _)).add (hIe.const_mul _)
  have hmono := intervalIntegral.integral_mono_on (show (0:ℝ) ≤ 2 by norm_num) hIt hsumI hpt
  have hsplit : (∫ y in (0:ℝ)..2, ((s1 - s)/(s1 - s0) * ((Real.exp (s0*y) - 2) * Real.cos (t*y) * g72 y)
        + (s - s0)/(s1 - s0) * ((Real.exp (s1*y) - 2) * Real.cos (t*y) * g72 y)
        + (s1 - s0)^2/8 * (y^2 * Real.exp (s1*y) * g72 y)))
      = (s1 - s)/(s1 - s0) * Isub s0 t
        + (s - s0)/(s1 - s0) * Isub s1 t
        + (s1 - s0)^2/8 * (∫ y in (0:ℝ)..2, y^2 * Real.exp (s1*y) * g72 y) := by
    rw [intervalIntegral.integral_add ((hI0.const_mul _).add (hI1.const_mul _)) (hIe.const_mul _),
        intervalIntegral.integral_add (hI0.const_mul _) (hI1.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        ← Isub_eq_integral s0 t, ← Isub_eq_integral s1 t]
  rw [hsplit, ← Isub_eq_integral s t] at hmono
  have h0 : 0 ≤ (s1 - s)/(s1 - s0) := div_nonneg (by linarith) (le_of_lt hba)
  have h1 : 0 ≤ (s - s0)/(s1 - s0) := div_nonneg (by linarith) (le_of_lt hba)
  have hsum : (s1 - s)/(s1 - s0) + (s - s0)/(s1 - s0) = 1 := by
    rw [← add_div, show s1 - s + (s - s0) = s1 - s0 by ring, div_self (ne_of_gt hba)]
  have hmax : (s1 - s)/(s1 - s0) * Isub s0 t + (s - s0)/(s1 - s0) * Isub s1 t
      ≤ max (Isub s0 t) (Isub s1 t) := by
    have hMx : (s1 - s)/(s1 - s0) * Isub s0 t + (s - s0)/(s1 - s0) * Isub s1 t
        ≤ (s1 - s)/(s1 - s0) * max (Isub s0 t) (Isub s1 t)
          + (s - s0)/(s1 - s0) * max (Isub s0 t) (Isub s1 t) :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h0)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) h1)
    calc (s1 - s)/(s1 - s0) * Isub s0 t + (s - s0)/(s1 - s0) * Isub s1 t
        ≤ _ := hMx
      _ = max (Isub s0 t) (Isub s1 t) := by rw [← add_mul, hsum, one_mul]
  have herr : (s1 - s0)^2/8 * (∫ y in (0:ℝ)..2, y^2 * Real.exp (s1*y) * g72 y)
      ≤ (s1 - s0)^2/8 * (13/10) := mul_le_mul_of_nonneg_left hM (by positivity)
  linarith [hmono, hmax, herr]

/-- **`s`-interpolation for `Isub`.** -/
theorem Isub_le_interp_s_cell2 (s t s0 s1 : ℝ) (hs0 : s0 ≤ s) (hs1 : s ≤ s1)
    (h0 : 0 ≤ s0) (h17 : s1 ≤ 17/16) :
    Isub s t ≤ max (Isub s0 t) (Isub s1 t) + (s1 - s0) ^ 2 / 8 * (13/10) := by
  rcases lt_or_ge s0 s1 with h | h
  · exact isub_le_interp_aux_s_cell2 s t s0 s1 h hs0 hs1
      (Mss_bound s1 (le_trans h0 (le_trans hs0 hs1)) h17)
  · have hs1s0 : s1 = s0 := le_antisymm h (le_trans hs0 hs1)
    have hss0 : s = s0 := le_antisymm (by rw [hs1s0] at hs1; exact hs1) hs0
    rw [hss0, hs1s0]
    simp

end Work.OffAxis.Tf72One
