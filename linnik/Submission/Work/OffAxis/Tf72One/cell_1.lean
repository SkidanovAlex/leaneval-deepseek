import Mathlib
import Submission.Work.OffAxis.Tf72One.Core
import Submission.Work.OffAxis.Tf72One.corner_low
import Submission.Work.OffAxis.Tf72One.abs_interp_error_le
import Submission.Work.OffAxis.Tf72One.Mtt_bound
import Submission.Work.OffAxis.Tf72One.Mss_bound

open scoped Interval
open MeasureTheory

namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables
open Work.ZeroFreeTables.OffAxis

/-! ## Second derivatives of the one-parameter families used below -/

private lemma iteratedDeriv_two_cos (y z : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => Real.cos (x * y)) z = -y ^ 2 * Real.cos (z * y) := by
  have h1 : ∀ x : ℝ, deriv (fun x : ℝ => Real.cos (x * y)) x = -y * Real.sin (x * y) := by
    intro x
    have hd : HasDerivAt (fun x : ℝ => Real.cos (x * y)) (-(Real.sin (x * y)) * y) x := by
      simpa only [id_eq, mul_one, one_mul] using (((hasDerivAt_id x).mul_const y).cos)
    rw [hd.deriv]; ring
  have h2 : ∀ x : ℝ, deriv (fun x : ℝ => -y * Real.sin (x * y)) x = -y ^ 2 * Real.cos (x * y) := by
    intro x
    have hd : HasDerivAt (fun x : ℝ => Real.sin (x * y)) (Real.cos (x * y) * y) x := by
      simpa only [id_eq, mul_one, one_mul] using (((hasDerivAt_id x).mul_const y).sin)
    have hd2 : HasDerivAt (fun x : ℝ => -y * Real.sin (x * y)) (-y * (Real.cos (x * y) * y)) x :=
      hd.const_mul (-y)
    rw [hd2.deriv]; ring
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [show deriv (deriv fun x : ℝ => Real.cos (x * y)) z
      = deriv (fun x : ℝ => -y * Real.sin (x * y)) z from by congr 1; funext x; exact h1 x]
  exact h2 z

private lemma iteratedDeriv_two_exp_sub (y z : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => Real.exp (x * y) - 2) z = y ^ 2 * Real.exp (z * y) := by
  have h1 : ∀ x : ℝ, deriv (fun x : ℝ => Real.exp (x * y) - 2) x = y * Real.exp (x * y) := by
    intro x
    have hd : HasDerivAt (fun x : ℝ => Real.exp (x * y) - 2) (Real.exp (x * y) * y) x := by
      have h2 : HasDerivAt (fun x : ℝ => Real.exp (x * y)) (Real.exp (x * y) * y) x := by
        simpa only [id_eq, mul_one, one_mul] using (((hasDerivAt_id x).mul_const y).exp)
      simpa using h2.sub_const 2
    rw [hd.deriv]; ring
  have h2 : ∀ x : ℝ, deriv (fun x : ℝ => y * Real.exp (x * y)) x = y ^ 2 * Real.exp (x * y) := by
    intro x
    have hd : HasDerivAt (fun x : ℝ => Real.exp (x * y)) (Real.exp (x * y) * y) x := by
      simpa only [id_eq, mul_one, one_mul] using (((hasDerivAt_id x).mul_const y).exp)
    have hd2 : HasDerivAt (fun x : ℝ => y * Real.exp (x * y)) (y * (Real.exp (x * y) * y)) x :=
      hd.const_mul y
    rw [hd2.deriv]; ring
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [show deriv (deriv fun x : ℝ => Real.exp (x * y) - 2) z
      = deriv (fun x : ℝ => y * Real.exp (x * y)) z from by congr 1; funext x; exact h1 x]
  exact h2 z

private lemma iteratedDeriv_two_const_exp_sub (c y z : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => c * (Real.exp (x * y) - 2)) z
      = c * (y ^ 2 * Real.exp (z * y)) := by
  rw [iteratedDeriv_const_mul c
      (by fun_prop : ContDiffAt ℝ 2 (fun x : ℝ => Real.exp (x * y) - 2) z),
    iteratedDeriv_two_exp_sub]

/-! ## The two pointwise interpolation bounds

Both are obtained by applying the sharp two-point interpolation bound
`abs_interp_error_le` to the integrand of `Isub` viewed as a function of the
interpolation variable. -/

/-- Pointwise `σ`-direction chord bound for the integrand of `Isub`. -/
private lemma pt_t (s t a b y : ℝ) (hab : a < b) (hta : a ≤ t) (htb : t ≤ b)
    (hy : y ∈ Set.Icc (0 : ℝ) 2) :
    (Real.exp (s * y) - 2) * Real.cos (t * y) * g72 y ≤
      (b - t) / (b - a) * ((Real.exp (s * y) - 2) * Real.cos (a * y) * g72 y)
        + (t - a) / (b - a) * ((Real.exp (s * y) - 2) * Real.cos (b * y) * g72 y)
        + (b - a) ^ 2 / 8 * (y ^ 2 * |Real.exp (s * y) - 2| * g72 y) := by
  have hf : ContDiffOn ℝ 2
      (fun x : ℝ => ((Real.exp (s * y) - 2) * g72 y) * Real.cos (x * y)) (Set.Icc a b) := by
    fun_prop
  have hM : ∀ z ∈ Set.Ioo a b,
      |iteratedDeriv 2 (fun x : ℝ => ((Real.exp (s * y) - 2) * g72 y) * Real.cos (x * y)) z|
        ≤ y ^ 2 * |Real.exp (s * y) - 2| * g72 y := by
    intro z _
    rw [iteratedDeriv_const_mul ((Real.exp (s * y) - 2) * g72 y)
        (by fun_prop : ContDiffAt ℝ 2 (fun x : ℝ => Real.cos (x * y)) z),
      iteratedDeriv_two_cos]
    have hg : 0 ≤ g72 y := g72_nonneg hy.1 hy.2
    have hcos : |Real.cos (z * y)| ≤ 1 := Real.abs_cos_le_one _
    have habs : |((Real.exp (s * y) - 2) * g72 y) * (-y ^ 2 * Real.cos (z * y))|
        = |Real.exp (s * y) - 2| * g72 y * (y ^ 2 * |Real.cos (z * y)|) := by
      simp only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg y), abs_of_nonneg hg]
    rw [habs]
    calc |Real.exp (s * y) - 2| * g72 y * (y ^ 2 * |Real.cos (z * y)|)
        ≤ |Real.exp (s * y) - 2| * g72 y * (y ^ 2 * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hcos (sq_nonneg y)
      _ = y ^ 2 * |Real.exp (s * y) - 2| * g72 y := by ring
  have hb := abs_interp_error_le
    (fun x : ℝ => ((Real.exp (s * y) - 2) * g72 y) * Real.cos (x * y)) a b t
    (y ^ 2 * |Real.exp (s * y) - 2| * g72 y) hab ⟨hta, htb⟩ hf hM
  have hle : ((Real.exp (s * y) - 2) * g72 y) * Real.cos (t * y)
      ≤ (b - t) / (b - a) * (((Real.exp (s * y) - 2) * g72 y) * Real.cos (a * y))
        + (t - a) / (b - a) * (((Real.exp (s * y) - 2) * g72 y) * Real.cos (b * y))
        + (b - a) ^ 2 / 8 * (y ^ 2 * |Real.exp (s * y) - 2| * g72 y) := by
    linarith [(abs_le.mp hb).2]
  calc (Real.exp (s * y) - 2) * Real.cos (t * y) * g72 y
      = ((Real.exp (s * y) - 2) * g72 y) * Real.cos (t * y) := by ring
    _ ≤ (b - t) / (b - a) * (((Real.exp (s * y) - 2) * g72 y) * Real.cos (a * y))
        + (t - a) / (b - a) * (((Real.exp (s * y) - 2) * g72 y) * Real.cos (b * y))
        + (b - a) ^ 2 / 8 * (y ^ 2 * |Real.exp (s * y) - 2| * g72 y) := hle
    _ = (b - t) / (b - a) * ((Real.exp (s * y) - 2) * Real.cos (a * y) * g72 y)
        + (t - a) / (b - a) * ((Real.exp (s * y) - 2) * Real.cos (b * y) * g72 y)
        + (b - a) ^ 2 / 8 * (y ^ 2 * |Real.exp (s * y) - 2| * g72 y) := by ring

/-- Pointwise `s`-direction chord bound for the integrand of `Isub`. -/
private lemma pt_s (s t a b y : ℝ) (hab : a < b) (hta : a ≤ s) (htb : s ≤ b)
    (hy : y ∈ Set.Icc (0 : ℝ) 2) :
    (Real.exp (s * y) - 2) * Real.cos (t * y) * g72 y ≤
      (b - s) / (b - a) * ((Real.exp (a * y) - 2) * Real.cos (t * y) * g72 y)
        + (s - a) / (b - a) * ((Real.exp (b * y) - 2) * Real.cos (t * y) * g72 y)
        + (b - a) ^ 2 / 8 * (y ^ 2 * Real.exp (b * y) * g72 y) := by
  have hf : ContDiffOn ℝ 2
      (fun x : ℝ => (Real.cos (t * y) * g72 y) * (Real.exp (x * y) - 2)) (Set.Icc a b) := by
    fun_prop
  have hM : ∀ z ∈ Set.Ioo a b,
      |iteratedDeriv 2 (fun x : ℝ => (Real.cos (t * y) * g72 y) * (Real.exp (x * y) - 2)) z|
        ≤ y ^ 2 * Real.exp (b * y) * g72 y := by
    intro z hz
    rw [iteratedDeriv_two_const_exp_sub]
    have hg : 0 ≤ g72 y := g72_nonneg hy.1 hy.2
    have hy0 : 0 ≤ y := hy.1
    have hzy : z ≤ b := le_of_lt hz.2
    have hexp : Real.exp (z * y) ≤ Real.exp (b * y) := Real.exp_le_exp.mpr (by nlinarith)
    have hcos : |Real.cos (t * y)| ≤ 1 := Real.abs_cos_le_one _
    have habs : |(Real.cos (t * y) * g72 y) * (y ^ 2 * Real.exp (z * y))|
        = |Real.cos (t * y)| * g72 y * (y ^ 2 * Real.exp (z * y)) := by
      simp only [abs_mul, abs_of_nonneg hg, abs_of_nonneg (sq_nonneg y),
        abs_of_nonneg (Real.exp_pos (z * y)).le]
    rw [habs]
    calc |Real.cos (t * y)| * g72 y * (y ^ 2 * Real.exp (z * y))
        ≤ 1 * g72 y * (y ^ 2 * Real.exp (z * y)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcos hg) (by positivity)
      _ ≤ 1 * g72 y * (y ^ 2 * Real.exp (b * y)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (sq_nonneg y))
            (by positivity)
      _ = y ^ 2 * Real.exp (b * y) * g72 y := by ring
  have hb := abs_interp_error_le
    (fun x : ℝ => (Real.cos (t * y) * g72 y) * (Real.exp (x * y) - 2)) a b s
    (y ^ 2 * Real.exp (b * y) * g72 y) hab ⟨hta, htb⟩ hf hM
  have hle : (Real.cos (t * y) * g72 y) * (Real.exp (s * y) - 2)
      ≤ (b - s) / (b - a) * ((Real.cos (t * y) * g72 y) * (Real.exp (a * y) - 2))
        + (s - a) / (b - a) * ((Real.cos (t * y) * g72 y) * (Real.exp (b * y) - 2))
        + (b - a) ^ 2 / 8 * (y ^ 2 * Real.exp (b * y) * g72 y) := by
    linarith [(abs_le.mp hb).2]
  calc (Real.exp (s * y) - 2) * Real.cos (t * y) * g72 y
      = (Real.cos (t * y) * g72 y) * (Real.exp (s * y) - 2) := by ring
    _ ≤ (b - s) / (b - a) * ((Real.cos (t * y) * g72 y) * (Real.exp (a * y) - 2))
        + (s - a) / (b - a) * ((Real.cos (t * y) * g72 y) * (Real.exp (b * y) - 2))
        + (b - a) ^ 2 / 8 * (y ^ 2 * Real.exp (b * y) * g72 y) := hle
    _ = (b - s) / (b - a) * ((Real.exp (a * y) - 2) * Real.cos (t * y) * g72 y)
        + (s - a) / (b - a) * ((Real.exp (b * y) - 2) * Real.cos (t * y) * g72 y)
        + (b - a) ^ 2 / 8 * (y ^ 2 * Real.exp (b * y) * g72 y) := by ring

end Work.OffAxis.Tf72One

namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables
open Work.ZeroFreeTables.OffAxis

/-! ## Integrating the pointwise bounds -/

/-- Integrating the pointwise `σ`-direction chord bound over `y ∈ [0,2]` bounds `Isub s t` by the
values of `Isub s ·` at the endpoints plus the interpolation error `(b-a)²/8 · (5/8)`. -/
private lemma interp_t_aux (s t a b : ℝ) (hab : a < b) (hta : a ≤ t) (htb : t ≤ b)
    (hpt : ∀ y ∈ Set.Icc (0 : ℝ) 2,
      (Real.exp (s * y) - 2) * Real.cos (t * y) * g72 y ≤
        (b - t) / (b - a) * ((Real.exp (s * y) - 2) * Real.cos (a * y) * g72 y)
          + (t - a) / (b - a) * ((Real.exp (s * y) - 2) * Real.cos (b * y) * g72 y)
          + (b - a) ^ 2 / 8 * (y ^ 2 * |Real.exp (s * y) - 2| * g72 y))
    (hM : ∫ y in (0 : ℝ)..2, y ^ 2 * |Real.exp (s * y) - 2| * g72 y ≤ 5/8) :
    Isub s t ≤ max (Isub s a) (Isub s b) + (b - a) ^ 2 / 8 * (5/8) := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hIt : IntervalIntegrable (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y)
      volume (0 : ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]; fun_prop
  have hIa : IntervalIntegrable (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (a*y) * g72 y)
      volume (0 : ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]; fun_prop
  have hIb : IntervalIntegrable (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (b*y) * g72 y)
      volume (0 : ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]; fun_prop
  have hIe : IntervalIntegrable (fun y : ℝ => y^2 * |Real.exp (s*y) - 2| * g72 y)
      volume (0 : ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]; fun_prop
  have hsumI : IntervalIntegrable
      (fun y : ℝ => (b - t)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (a*y) * g72 y)
        + (t - a)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (b*y) * g72 y)
        + (b - a)^2/8 * (y^2 * |Real.exp (s*y) - 2| * g72 y)) volume (0 : ℝ) 2 :=
    ((hIa.const_mul _).add (hIb.const_mul _)).add (hIe.const_mul _)
  have hmono := intervalIntegral.integral_mono_on (show (0:ℝ) ≤ 2 by norm_num) hIt hsumI hpt
  have hsplit : (∫ y in (0 : ℝ)..2, ((b - t)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (a*y) * g72 y)
        + (t - a)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (b*y) * g72 y)
        + (b - a)^2/8 * (y^2 * |Real.exp (s*y) - 2| * g72 y)))
      = (b - t)/(b - a) * Isub s a + (t - a)/(b - a) * Isub s b
        + (b - a)^2/8 * (∫ y in (0 : ℝ)..2, y^2 * |Real.exp (s*y) - 2| * g72 y) := by
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
  have herr : (b - a)^2/8 * (∫ y in (0 : ℝ)..2, y^2 * |Real.exp (s*y) - 2| * g72 y)
      ≤ (b - a)^2/8 * (5/8) := mul_le_mul_of_nonneg_left hM (by positivity)
  linarith [hmono, hmax, herr]

/-- Integrating the pointwise `s`-direction chord bound over `y ∈ [0,2]` bounds `Isub s t` by the
values of `Isub · t` at the endpoints plus the interpolation error `(b-a)²/8 · (13/10)`. -/
private lemma interp_s_aux (s t a b : ℝ) (hab : a < b) (hta : a ≤ s) (htb : s ≤ b)
    (hpt : ∀ y ∈ Set.Icc (0 : ℝ) 2,
      (Real.exp (s * y) - 2) * Real.cos (t * y) * g72 y ≤
        (b - s) / (b - a) * ((Real.exp (a * y) - 2) * Real.cos (t * y) * g72 y)
          + (s - a) / (b - a) * ((Real.exp (b * y) - 2) * Real.cos (t * y) * g72 y)
          + (b - a) ^ 2 / 8 * (y ^ 2 * Real.exp (b * y) * g72 y))
    (hM : ∫ y in (0 : ℝ)..2, y ^ 2 * Real.exp (b * y) * g72 y ≤ 13/10) :
    Isub s t ≤ max (Isub a t) (Isub b t) + (b - a) ^ 2 / 8 * (13/10) := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hIt : IntervalIntegrable (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y)
      volume (0 : ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]; fun_prop
  have hIa : IntervalIntegrable (fun y : ℝ => (Real.exp (a*y) - 2) * Real.cos (t*y) * g72 y)
      volume (0 : ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]; fun_prop
  have hIb : IntervalIntegrable (fun y : ℝ => (Real.exp (b*y) - 2) * Real.cos (t*y) * g72 y)
      volume (0 : ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]; fun_prop
  have hIe : IntervalIntegrable (fun y : ℝ => y^2 * Real.exp (b*y) * g72 y)
      volume (0 : ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]; fun_prop
  have hsumI : IntervalIntegrable
      (fun y : ℝ => (b - s)/(b - a) * ((Real.exp (a*y) - 2) * Real.cos (t*y) * g72 y)
        + (s - a)/(b - a) * ((Real.exp (b*y) - 2) * Real.cos (t*y) * g72 y)
        + (b - a)^2/8 * (y^2 * Real.exp (b*y) * g72 y)) volume (0 : ℝ) 2 :=
    ((hIa.const_mul _).add (hIb.const_mul _)).add (hIe.const_mul _)
  have hmono := intervalIntegral.integral_mono_on (show (0:ℝ) ≤ 2 by norm_num) hIt hsumI hpt
  have hsplit : (∫ y in (0 : ℝ)..2, ((b - s)/(b - a) * ((Real.exp (a*y) - 2) * Real.cos (t*y) * g72 y)
        + (s - a)/(b - a) * ((Real.exp (b*y) - 2) * Real.cos (t*y) * g72 y)
        + (b - a)^2/8 * (y^2 * Real.exp (b*y) * g72 y)))
      = (b - s)/(b - a) * Isub a t + (s - a)/(b - a) * Isub b t
        + (b - a)^2/8 * (∫ y in (0 : ℝ)..2, y^2 * Real.exp (b*y) * g72 y) := by
    rw [intervalIntegral.integral_add ((hIa.const_mul _).add (hIb.const_mul _)) (hIe.const_mul _),
        intervalIntegral.integral_add (hIa.const_mul _) (hIb.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        ← Isub_eq_integral a t, ← Isub_eq_integral b t]
  rw [hsplit, ← Isub_eq_integral s t] at hmono
  have h0 : 0 ≤ (b - s)/(b - a) := div_nonneg (by linarith) (le_of_lt hba)
  have h1 : 0 ≤ (s - a)/(b - a) := div_nonneg (by linarith) (le_of_lt hba)
  have hsum : (b - s)/(b - a) + (s - a)/(b - a) = 1 := by
    rw [← add_div, show b - s + (s - a) = b - a by ring, div_self (ne_of_gt hba)]
  have hmax : (b - s)/(b - a) * Isub a t + (s - a)/(b - a) * Isub b t
      ≤ max (Isub a t) (Isub b t) := by
    have hMx : (b - s)/(b - a) * Isub a t + (s - a)/(b - a) * Isub b t
        ≤ (b - s)/(b - a) * max (Isub a t) (Isub b t)
          + (s - a)/(b - a) * max (Isub a t) (Isub b t) :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h0)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) h1)
    calc (b - s)/(b - a) * Isub a t + (s - a)/(b - a) * Isub b t
        ≤ _ := hMx
      _ = max (Isub a t) (Isub b t) := by rw [← add_mul, hsum, one_mul]
  have herr : (b - a)^2/8 * (∫ y in (0 : ℝ)..2, y^2 * Real.exp (b*y) * g72 y)
      ≤ (b - a)^2/8 * (13/10) := mul_le_mul_of_nonneg_left hM (by positivity)
  linarith [hmono, hmax, herr]

/-! ## Interpolation in each variable -/

/-- `σ`-interpolation for `Isub`: on `[t0,t1]` the values of `Isub s ·` are controlled by the
endpoint values, with error `(t1-t0)²/8 · (5/8)`. -/
private lemma Isub_le_interp_t' (s t t0 t1 : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 17/16)
    (ht0 : t0 ≤ t) (ht1 : t ≤ t1) :
    Isub s t ≤ max (Isub s t0) (Isub s t1) + (t1 - t0) ^ 2 / 8 * (5/8) := by
  rcases lt_or_ge t0 t1 with h | h
  · exact interp_t_aux s t t0 t1 h ht0 ht1
      (fun y hy => pt_t s t t0 t1 y h ht0 ht1 hy) (Mtt_bound s hs0 hs1)
  · have ht1t0 : t1 = t0 := le_antisymm h (le_trans ht0 ht1)
    have htt0 : t = t0 := le_antisymm (by rw [ht1t0] at ht1; exact ht1) ht0
    rw [htt0, ht1t0]
    simp

/-- `s`-interpolation for `Isub`: on `[s0,s1]` the values of `Isub · t` are controlled by the
endpoint values, with error `(s1-s0)²/8 · (13/10)`. -/
private lemma Isub_le_interp_s' (s t s0 s1 : ℝ) (hs0 : s0 ≤ s) (hs1 : s ≤ s1)
    (h0 : 0 ≤ s0) (h17 : s1 ≤ 17/16) :
    Isub s t ≤ max (Isub s0 t) (Isub s1 t) + (s1 - s0) ^ 2 / 8 * (13/10) := by
  rcases lt_or_ge s0 s1 with h | h
  · have hs1' : 0 ≤ s1 := le_trans h0 (le_trans hs0 hs1)
    exact interp_s_aux s t s0 s1 h hs0 hs1
      (fun y hy => pt_s s t s0 s1 y h hs0 hs1 hy) (Mss_bound s1 hs1' h17)
  · have hs1s0 : s1 = s0 := le_antisymm h (le_trans hs0 hs1)
    have hss0 : s = s0 := le_antisymm (by rw [hs1s0] at hs1; exact hs1) hs0
    rw [hss0, hs1s0]
    simp

/-! ## The box bound and the cell -/

/-- Box bound: four corner bounds `≤ B` plus the two interpolation errors bound `Isub` on the whole
box `[s0,s1] × [t0,t1]`. -/
private lemma box_cell (s t s0 s1 t0 t1 B : ℝ) (hs0 : s0 ≤ s) (hs1 : s ≤ s1)
    (ht0 : t0 ≤ t) (ht1 : t ≤ t1) (h0 : 0 ≤ s0) (h17 : s1 ≤ 17/16)
    (h00 : Isub s0 t0 ≤ B) (h01 : Isub s0 t1 ≤ B) (h10 : Isub s1 t0 ≤ B)
    (h11 : Isub s1 t1 ≤ B) :
    Isub s t ≤ B + (s1 - s0) ^ 2 / 8 * (13/10) + (t1 - t0) ^ 2 / 8 * (5/8) := by
  have hs1' : 0 ≤ s1 := le_trans h0 (le_trans hs0 hs1)
  have hs017 : s0 ≤ 17/16 := le_trans hs0 (le_trans hs1 h17)
  have hIs := Isub_le_interp_s' s t s0 s1 hs0 hs1 h0 h17
  have h0t := Isub_le_interp_t' s0 t t0 t1 h0 hs017 ht0 ht1
  have h1t := Isub_le_interp_t' s1 t t0 t1 hs1' h17 ht0 ht1
  have hmax0 : max (Isub s0 t0) (Isub s0 t1) ≤ B := max_le h00 h01
  have hmax1 : max (Isub s1 t0) (Isub s1 t1) ≤ B := max_le h10 h11
  have h0t' : Isub s0 t ≤ B + (t1 - t0) ^ 2 / 8 * (5/8) := by linarith [h0t, hmax0]
  have h1t' : Isub s1 t ≤ B + (t1 - t0) ^ 2 / 8 * (5/8) := by linarith [h1t, hmax1]
  have hmax : max (Isub s0 t) (Isub s1 t) ≤ B + (t1 - t0) ^ 2 / 8 * (5/8) :=
    max_le h0t' h1t'
  linarith [hIs, hmax]

/-! ## The cell `σ ∈ [7/4, 5/2]`

The implementation below splits `s` at the single grid point `3/4` and applies the box bound
`box_cell` on the two boxes `[0, 3/4] × [7/4, 5/2]` and `[3/4, 17/16] × [7/4, 5/2]`.  On each box
the four corner values are bounded by `corner_low` (`≤ -193/1000`, all four corners have
`σ ∈ {7/4, 5/2}`), and the two interpolation errors are `(3/4)²/8·(13/10) = 0.0914…` (`s`-direction,
constant `13/10` from `Mss_bound`) and `(3/4)²/8·(5/8) = 0.0439…` (`σ`-direction, constant `5/8` from
`Mtt_bound`), giving respectively `-0.0577` and `-0.1332`, both `≤ 1/100`. -/

/-- **HB (10.8) on the box `σ ∈ [7/4, 5/2]`.**  For `0 ≤ s ≤ 17/16` and `t ∈ [7/4, 5/2]`,
`Isub s t ≤ 1/100`.

Proof route: as in `cell_0` (`corner_low` gives `-193/1000` at both endpoints); the error is at most
`(3/20)²/8·(13/10) + (3/4)²/8·(5/8) = 0.0476`, giving `-0.145 ≤ 1/100`. -/
theorem cell_1 (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 17/16) (ht0 : 7/4 ≤ t) (ht1 : t ≤ 5/2) :
    Work.ZeroFreeTables.OffAxis.Isub s t ≤ 1/100 := by
  have hB0 : Isub 0 (7/4) ≤ (-193/1000 : ℝ) := corner_low 0 (7/4) (by simp) (by simp)
  have hB1 : Isub 0 (5/2) ≤ (-193/1000 : ℝ) := corner_low 0 (5/2) (by simp) (by simp)
  have hB2 : Isub (3/4) (7/4) ≤ (-193/1000 : ℝ) := corner_low (3/4) (7/4) (by simp) (by simp)
  have hB3 : Isub (3/4) (5/2) ≤ (-193/1000 : ℝ) := corner_low (3/4) (5/2) (by simp) (by simp)
  have hB4 : Isub (17/16) (7/4) ≤ (-193/1000 : ℝ) := corner_low (17/16) (7/4) (by simp) (by simp)
  have hB5 : Isub (17/16) (5/2) ≤ (-193/1000 : ℝ) := corner_low (17/16) (5/2) (by simp) (by simp)
  rcases le_total s (3/4) with h | h
  · have hbox := box_cell s t 0 (3/4) (7/4) (5/2) (-193/1000) hs0 h ht0 ht1
      (by norm_num) (by norm_num) hB0 hB1 hB2 hB3
    refine hbox.trans ?_
    norm_num
  · have hbox := box_cell s t (3/4) (17/16) (7/4) (5/2) (-193/1000) h hs1 ht0 ht1
      (by norm_num) (by norm_num) hB2 hB3 hB4 hB5
    refine hbox.trans ?_
    norm_num

end Work.OffAxis.Tf72One
