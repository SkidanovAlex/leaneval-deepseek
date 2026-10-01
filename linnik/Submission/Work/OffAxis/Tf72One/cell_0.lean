import Mathlib
import Submission.Work.OffAxis.Tf72One.Core
import Submission.Work.OffAxis.Tf72One.corner_low
import Submission.Work.OffAxis.Tf72One.abs_interp_error_le
import Submission.Work.OffAxis.Tf72One.Mss_bound
import Submission.Work.OffAxis.Tf72One.Mtt_bound

noncomputable section
namespace Work.OffAxis.Tf72One

open MeasureTheory intervalIntegral
open Work.ZeroFreeTables
open Work.ZeroFreeTables.OffAxis

/-! ## Pointwise interpolation lemmas

The pointwise bound for the `s`-direction uses the sharp two-point interpolation error bound
`abs_interp_error_le` applied to `x ↦ (e^{xy}-2) cos(ty) g72 y` (second derivative `y² e^{xy} cos(ty) g72 y`,
bounded by `y² e^{by} g72 y` on `[a,b]`), and the one for the `t`-direction applies it to
`x ↦ (e^{sy}-2) cos(xy) g72 y` (second derivative `-y² (e^{sy}-2) cos(xy) g72 y`, bounded by
`y² |e^{sy}-2| g72 y`).  These are the pointwise inputs to the integral interpolation lemmas,
reproved here (self-contained) because the `integrand_interp_le` of the tree still carries a `sorry`. -/

/-- Pointwise interpolation in the first variable of the integrand. -/
private lemma integrand_interp_le_s (s t a b y : ℝ) (hab : a < b) (hsa : a ≤ s) (hsb : s ≤ b)
    (hy : y ∈ Set.Icc (0:ℝ) 2) :
    (Real.exp (s * y) - 2) * Real.cos (t * y) * g72 y ≤
      (b - s) / (b - a) * ((Real.exp (a * y) - 2) * Real.cos (t * y) * g72 y)
        + (s - a) / (b - a) * ((Real.exp (b * y) - 2) * Real.cos (t * y) * g72 y)
        + (b - a) ^ 2 / 8 * (y ^ 2 * Real.exp (b * y) * g72 y) := by
  have hg : 0 ≤ g72 y := Work.ZeroFreeTables.OffAxis.g72_nonneg hy.1 hy.2
  have hf : ContDiffOn ℝ 2 (fun x : ℝ => (Real.exp (x * y) - 2) * Real.cos (t * y) * g72 y) (Set.Icc a b) := by
    fun_prop
  have hiter : ∀ x : ℝ, iteratedDeriv 2 (fun x : ℝ => (Real.exp (x * y) - 2) * Real.cos (t * y) * g72 y) x
      = y^2 * Real.exp (x*y) * (Real.cos (t*y) * g72 y) := by
    intro x
    have hB : iteratedDeriv 2 (fun x : ℝ => Real.exp (x * y) - 2) x = y^2 * Real.exp (x * y) := by
      rw [show (fun x : ℝ => Real.exp (x*y) - 2) = (fun z : ℝ => (-2:ℝ) + Real.exp (z*y)) by funext z; ring]
      rw [iteratedDeriv_const_add (by norm_num)]
      rw [show (fun z : ℝ => Real.exp (z*y)) = (fun z : ℝ => Real.exp (y*z)) by funext z; ring_nf]
      rw [iteratedDeriv_exp_const_mul]
      ring_nf
    have h1 : iteratedDeriv 2 (fun x : ℝ => (Real.exp (x*y) - 2) * Real.cos (t*y)) x
        = (y^2 * Real.exp (x*y)) * Real.cos (t*y) := by
      rw [iteratedDeriv_mul_const_field, hB]
    have h2 : iteratedDeriv 2 (fun x : ℝ => (Real.exp (x*y) - 2) * Real.cos (t*y) * g72 y) x
        = iteratedDeriv 2 (fun x : ℝ => (Real.exp (x*y) - 2) * Real.cos (t*y)) x * g72 y := by
      rw [iteratedDeriv_mul_const_field]
    rw [h2, h1]; ring
  have hM : ∀ x ∈ Set.Ioo a b,
      |iteratedDeriv 2 (fun x : ℝ => (Real.exp (x * y) - 2) * Real.cos (t * y) * g72 y) x|
        ≤ y^2 * Real.exp (b*y) * g72 y := by
    intro x hx
    rw [hiter x]
    have hxy : x*y ≤ b*y := by nlinarith [hx.2, hy.1]
    have hexpb : Real.exp (x*y) ≤ Real.exp (b*y) := Real.exp_le_exp.mpr hxy
    have hcos : |Real.cos (t*y)| ≤ 1 := Real.abs_cos_le_one _
    calc |y^2 * Real.exp (x*y) * (Real.cos (t*y) * g72 y)|
        = (y^2 * Real.exp (x*y)) * (|Real.cos (t*y)| * g72 y) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg y), abs_of_nonneg (Real.exp_nonneg _), abs_mul, abs_of_nonneg hg]
      _ ≤ (y^2 * Real.exp (b*y)) * (1 * g72 y) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hexpb (sq_nonneg y)
          · exact mul_le_mul_of_nonneg_right hcos hg
          · positivity
          · positivity
      _ = y^2 * Real.exp (b*y) * g72 y := by ring
  have hmain := abs_interp_error_le
    (fun x : ℝ => (Real.exp (x * y) - 2) * Real.cos (t * y) * g72 y) a b s
    (y^2 * Real.exp (b*y) * g72 y) hab ⟨hsa, hsb⟩ hf hM
  linarith [(abs_le.mp hmain).2]

/-- Pointwise interpolation in the second variable of the integrand. -/
private lemma integrand_interp_le_t (s t a b y : ℝ) (hab : a < b) (hta : a ≤ t) (htb : t ≤ b)
    (hy : y ∈ Set.Icc (0:ℝ) 2) :
    (Real.exp (s * y) - 2) * Real.cos (t * y) * g72 y ≤
      (b - t) / (b - a) * ((Real.exp (s * y) - 2) * Real.cos (a * y) * g72 y)
        + (t - a) / (b - a) * ((Real.exp (s * y) - 2) * Real.cos (b * y) * g72 y)
        + (b - a) ^ 2 / 8 * (y ^ 2 * |Real.exp (s * y) - 2| * g72 y) := by
  have hg : 0 ≤ g72 y := Work.ZeroFreeTables.OffAxis.g72_nonneg hy.1 hy.2
  have hf : ContDiffOn ℝ 2 (fun x : ℝ => Real.cos (x * y)) (Set.Icc a b) := by fun_prop
  have hM : ∀ x ∈ Set.Ioo a b, |iteratedDeriv 2 (fun x : ℝ => Real.cos (x * y)) x| ≤ y^2 := by
    intro x _
    have h1 : iteratedDeriv 2 (fun x : ℝ => Real.cos (x * y)) x = -(y^2) * Real.cos (x*y) := by
      rw [show (fun x : ℝ => Real.cos (x * y)) = (fun x : ℝ => Real.cos (y * x)) by funext z; ring_nf]
      rw [iteratedDeriv_comp_const_mul Real.contDiff_cos y]
      have : iteratedDeriv 2 Real.cos (y * x) = -Real.cos (y*x) := by
        have h := Real.iteratedDeriv_even_cos 1
        simpa using congrFun h (y*x)
      simp only [this]
      ring_nf
    rw [h1, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg y)]
    nlinarith [Real.abs_cos_le_one (x*y)]
  have hmain := abs_interp_error_le (fun x : ℝ => Real.cos (x * y)) a b t (y^2) hab ⟨hta, htb⟩ hf hM
  have h1 : (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y
      = (Real.exp (s*y) - 2) * g72 y * Real.cos (t*y) := by ring
  rw [h1]
  have h2 : (Real.exp (s*y) - 2) * g72 y * Real.cos (t*y)
      = (Real.exp (s*y) - 2) * g72 y * (Real.cos (t*y)
          - ((b - t) / (b - a) * Real.cos (a * y) + (t - a) / (b - a) * Real.cos (b * y)))
        + (Real.exp (s*y) - 2) * g72 y * ((b - t) / (b - a) * Real.cos (a * y) + (t - a) / (b - a) * Real.cos (b * y)) := by ring
  rw [h2]
  have hb1 : (Real.exp (s*y) - 2) * g72 y * (Real.cos (t*y)
        - ((b - t) / (b - a) * Real.cos (a * y) + (t - a) / (b - a) * Real.cos (b * y)))
      ≤ ((b - a)^2 / 8 * (y^2)) * (|Real.exp (s*y) - 2| * g72 y) := by
    calc (Real.exp (s*y) - 2) * g72 y * (Real.cos (t*y)
          - ((b - t) / (b - a) * Real.cos (a * y) + (t - a) / (b - a) * Real.cos (b * y)))
        ≤ |(Real.exp (s*y) - 2) * g72 y * (Real.cos (t*y)
          - ((b - t) / (b - a) * Real.cos (a * y) + (t - a) / (b - a) * Real.cos (b * y)))| := le_abs_self _
      _ = |(Real.exp (s*y) - 2) * g72 y| * |Real.cos (t*y)
          - ((b - t) / (b - a) * Real.cos (a * y) + (t - a) / (b - a) * Real.cos (b * y))| := abs_mul _ _
      _ = (|Real.exp (s*y) - 2| * g72 y) * |Real.cos (t*y)
          - ((b - t) / (b - a) * Real.cos (a * y) + (t - a) / (b - a) * Real.cos (b * y))| := by
          rw [abs_mul, abs_of_nonneg hg]
      _ ≤ (|Real.exp (s*y) - 2| * g72 y) * ((b - a)^2 / 8 * y^2) :=
          mul_le_mul_of_nonneg_left hmain (mul_nonneg (abs_nonneg _) hg)
      _ = ((b - a)^2 / 8 * (y^2)) * (|Real.exp (s*y) - 2| * g72 y) := by ring
  have hb2 : (Real.exp (s*y) - 2) * g72 y * ((b - t) / (b - a) * Real.cos (a * y) + (t - a) / (b - a) * Real.cos (b * y))
      = (b - t) / (b - a) * ((Real.exp (s * y) - 2) * Real.cos (a * y) * g72 y)
        + (t - a) / (b - a) * ((Real.exp (s * y) - 2) * Real.cos (b * y) * g72 y) := by ring
  have hb3 : ((b - a)^2 / 8 * (y^2)) * (|Real.exp (s*y) - 2| * g72 y)
      = (b - a) ^ 2 / 8 * (y ^ 2 * |Real.exp (s * y) - 2| * g72 y) := by ring
  linarith [hb1, hb2, hb3]

/-! ## Integral interpolation lemmas -/

/-- **`s`-interpolation for `Isub`** (self-contained version). -/
private theorem isub_le_interp_s_aux (s t s0 s1 : ℝ) (hab : s0 < s1) (hsa : s0 ≤ s) (hsb : s ≤ s1)
    (h0 : 0 ≤ s0) (h17 : s1 ≤ 17/16) :
    Isub s t ≤ max (Isub s0 t) (Isub s1 t) + (s1 - s0) ^ 2 / 8 * (13/10) := by
  have hba : (0:ℝ) < s1 - s0 := by linarith
  have hIt : IntervalIntegrable (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  have hI0 : IntervalIntegrable (fun y : ℝ => (Real.exp (s0*y) - 2) * Real.cos (t*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  have hI1 : IntervalIntegrable (fun y : ℝ => (Real.exp (s1*y) - 2) * Real.cos (t*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  have hIe : IntervalIntegrable (fun y : ℝ => y^2 * Real.exp (s1*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  have hpt : ∀ y ∈ Set.Icc (0:ℝ) 2,
      (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y ≤
        (s1 - s) / (s1 - s0) * ((Real.exp (s0*y) - 2) * Real.cos (t*y) * g72 y)
        + (s - s0) / (s1 - s0) * ((Real.exp (s1*y) - 2) * Real.cos (t*y) * g72 y)
        + (s1 - s0)^2 / 8 * (y^2 * Real.exp (s1*y) * g72 y) :=
    fun y hy => integrand_interp_le_s s t s0 s1 y hab hsa hsb hy
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
        ← Isub_eq_integral s0 t,
        ← Isub_eq_integral s1 t]
  rw [hsplit, ← Isub_eq_integral s t] at hmono
  have h0' : 0 ≤ (s1 - s)/(s1 - s0) := div_nonneg (by linarith) (le_of_lt hba)
  have h1' : 0 ≤ (s - s0)/(s1 - s0) := div_nonneg (by linarith) (le_of_lt hba)
  have hsum : (s1 - s)/(s1 - s0) + (s - s0)/(s1 - s0) = 1 := by
    rw [← add_div, show s1 - s + (s - s0) = s1 - s0 by ring, div_self (ne_of_gt hba)]
  have hmax : (s1 - s)/(s1 - s0) * Isub s0 t
      + (s - s0)/(s1 - s0) * Isub s1 t
      ≤ max (Isub s0 t) (Isub s1 t) := by
    have hMx : (s1 - s)/(s1 - s0) * Isub s0 t
        + (s - s0)/(s1 - s0) * Isub s1 t
        ≤ (s1 - s)/(s1 - s0) * max (Isub s0 t) (Isub s1 t)
          + (s - s0)/(s1 - s0) * max (Isub s0 t) (Isub s1 t) :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h0')
        (mul_le_mul_of_nonneg_left (le_max_right _ _) h1')
    calc (s1 - s)/(s1 - s0) * Isub s0 t
          + (s - s0)/(s1 - s0) * Isub s1 t
        ≤ _ := hMx
      _ = max (Isub s0 t) (Isub s1 t) := by rw [← add_mul, hsum, one_mul]
  have hs1' : 0 ≤ s1 := le_trans h0 (le_of_lt hab)
  have herr : (s1 - s0)^2/8 * (∫ y in (0:ℝ)..2, y^2 * Real.exp (s1*y) * g72 y)
      ≤ (s1 - s0)^2/8 * (13/10) := mul_le_mul_of_nonneg_left (Mss_bound s1 hs1' h17) (by positivity)
  linarith [hmono, hmax, herr]

/-- **`s`-interpolation for `Isub`** (self-contained version). -/
private theorem Isub_le_interp_s_self (s t s0 s1 : ℝ) (hs0 : s0 ≤ s) (hs1 : s ≤ s1)
    (h0 : 0 ≤ s0) (h17 : s1 ≤ 17/16) :
    Isub s t ≤ max (Isub s0 t) (Isub s1 t) + (s1 - s0) ^ 2 / 8 * (13/10) := by
  rcases lt_or_ge s0 s1 with h | h
  · exact isub_le_interp_s_aux s t s0 s1 h hs0 hs1 h0 h17
  · have hs1s0 : s1 = s0 := le_antisymm h (le_trans hs0 hs1)
    have hss0 : s = s0 := le_antisymm (by rw [hs1s0] at hs1; exact hs1) hs0
    rw [hss0, hs1s0]; simp

/-- **`σ`-interpolation for `Isub`** (self-contained version). -/
private theorem isub_le_interp_t_aux (s t a b : ℝ) (hab : a < b) (hta : a ≤ t) (htb : t ≤ b)
    (hM : ∫ y in (0:ℝ)..2, y ^ 2 * |Real.exp (s * y) - 2| * g72 y ≤ 5/8) :
    Isub s t ≤ max (Isub s a) (Isub s b) + (b - a) ^ 2 / 8 * (5/8) := by
  have hba : (0:ℝ) < b - a := by linarith
  have hIt : IntervalIntegrable (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  have hIa : IntervalIntegrable (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (a*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  have hIb : IntervalIntegrable (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (b*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  have hIe : IntervalIntegrable (fun y : ℝ => y^2 * |Real.exp (s*y) - 2| * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  have hpt : ∀ y ∈ Set.Icc (0:ℝ) 2,
      (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y ≤
        (b - t) / (b - a) * ((Real.exp (s*y) - 2) * Real.cos (a*y) * g72 y)
        + (t - a) / (b - a) * ((Real.exp (s*y) - 2) * Real.cos (b*y) * g72 y)
        + (b - a)^2 / 8 * (y^2 * |Real.exp (s*y) - 2| * g72 y) :=
    fun y hy => integrand_interp_le_t s t a b y hab hta htb hy
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
        ← Isub_eq_integral s a,
        ← Isub_eq_integral s b]
  rw [hsplit, ← Isub_eq_integral s t] at hmono
  have h0 : 0 ≤ (b - t)/(b - a) := div_nonneg (by linarith) (le_of_lt hba)
  have h1 : 0 ≤ (t - a)/(b - a) := div_nonneg (by linarith) (le_of_lt hba)
  have hsum : (b - t)/(b - a) + (t - a)/(b - a) = 1 := by
    rw [← add_div, show b - t + (t - a) = b - a by ring, div_self (ne_of_gt hba)]
  have hmax : (b - t)/(b - a) * Isub s a
      + (t - a)/(b - a) * Isub s b
      ≤ max (Isub s a) (Isub s b) := by
    have hMx : (b - t)/(b - a) * Isub s a
        + (t - a)/(b - a) * Isub s b
        ≤ (b - t)/(b - a) * max (Isub s a) (Isub s b)
          + (t - a)/(b - a) * max (Isub s a) (Isub s b) :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h0)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) h1)
    calc (b - t)/(b - a) * Isub s a
          + (t - a)/(b - a) * Isub s b
        ≤ _ := hMx
      _ = max (Isub s a) (Isub s b) := by rw [← add_mul, hsum, one_mul]
  have herr : (b - a)^2/8 * (∫ y in (0:ℝ)..2, y^2 * |Real.exp (s*y) - 2| * g72 y)
      ≤ (b - a)^2/8 * (5/8) := mul_le_mul_of_nonneg_left hM (by positivity)
  linarith [hmono, hmax, herr]

/-- **`σ`-interpolation for `Isub`** (self-contained version). -/
private theorem Isub_le_interp_t_self (s t t0 t1 : ℝ) (hs0 : 0 ≤ s) (hs17 : s ≤ 17/16)
    (ht0 : t0 ≤ t) (ht1 : t ≤ t1) :
    Isub s t ≤ max (Isub s t0) (Isub s t1) + (t1 - t0) ^ 2 / 8 * (5/8) := by
  rcases lt_or_ge t0 t1 with h | h
  · exact isub_le_interp_t_aux s t t0 t1 h ht0 ht1 (Mtt_bound s hs0 hs17)
  · have ht1t0 : t1 = t0 := le_antisymm h (le_trans ht0 ht1)
    have htt0 : t = t0 := le_antisymm (by rw [ht1t0] at ht1; exact ht1) ht0
    rw [htt0, ht1t0]
    simp

/-- **Box bound from corner bounds** (self-contained version). -/
private theorem Isub_le_box_self (s t s0 s1 t0 t1 B00 B01 B10 B11 : ℝ)
    (hs0 : s0 ≤ s) (hs1 : s ≤ s1) (ht0 : t0 ≤ t) (ht1 : t ≤ t1)
    (h0 : 0 ≤ s0) (h17 : s1 ≤ 17/16)
    (h00 : Isub s0 t0 ≤ B00) (h01 : Isub s0 t1 ≤ B01)
    (h10 : Isub s1 t0 ≤ B10) (h11 : Isub s1 t1 ≤ B11) :
    Isub s t ≤ max (max B00 B01) (max B10 B11)
      + (s1 - s0) ^ 2 / 8 * (13/10) + (t1 - t0) ^ 2 / 8 * (5/8) := by
  have hs1' : 0 ≤ s1 := le_trans h0 (le_trans hs0 hs1)
  have hs017 : s0 ≤ 17/16 := le_trans hs0 (le_trans hs1 h17)
  have hIs := Isub_le_interp_s_self s t s0 s1 hs0 hs1 h0 h17
  have h0t := Isub_le_interp_t_self s0 t t0 t1 h0 hs017 ht0 ht1
  have h1t := Isub_le_interp_t_self s1 t t0 t1 hs1' h17 ht0 ht1
  have hmax0 : max (Isub s0 t0) (Isub s0 t1) ≤ max B00 B01 := max_le_max h00 h01
  have hmax1 : max (Isub s1 t0) (Isub s1 t1) ≤ max B10 B11 := max_le_max h10 h11
  have h0t' : Isub s0 t ≤ max (max B00 B01) (max B10 B11) + (t1 - t0) ^ 2 / 8 * (5/8) := by
    have hle : max B00 B01 ≤ max (max B00 B01) (max B10 B11) := le_max_left _ _
    linarith [h0t, hmax0, hle]
  have h1t' : Isub s1 t ≤ max (max B00 B01) (max B10 B11) + (t1 - t0) ^ 2 / 8 * (5/8) := by
    have hle : max B10 B11 ≤ max (max B00 B01) (max B10 B11) := le_max_right _ _
    linarith [h1t, hmax1, hle]
  have hmax : max (Isub s0 t) (Isub s1 t)
      ≤ max (max B00 B01) (max B10 B11) + (t1 - t0) ^ 2 / 8 * (5/8) := max_le h0t' h1t'
  linarith [hIs, hmax]

/-- One grid cell of the `s`-range: given `-193/1000` at the four corners of `[s0,s1]×[3/4,7/4]`
and `s1 - s0 ≤ 3/20`, the box bound gives `Isub s t ≤ 1/100`. -/
private lemma cell_eight (s t s0 s1 : ℝ) (hs0 : s0 ≤ s) (hs1 : s ≤ s1)
    (ht0 : 3/4 ≤ t) (ht1 : t ≤ 7/4)
    (h0 : 0 ≤ s0) (h17 : s1 ≤ 17/16)
    (h00 : Isub s0 (3/4) ≤ (-193/1000 : ℝ)) (h01 : Isub s0 (7/4) ≤ (-193/1000 : ℝ))
    (h10 : Isub s1 (3/4) ≤ (-193/1000 : ℝ)) (h11 : Isub s1 (7/4) ≤ (-193/1000 : ℝ))
    (hw : s1 - s0 ≤ 3/20) :
    Isub s t ≤ 1/100 := by
  have hbox := Isub_le_box_self s t s0 s1 (3/4) (7/4) (-193/1000) (-193/1000) (-193/1000) (-193/1000)
    hs0 hs1 ht0 ht1 h0 h17 h00 h01 h10 h11
  have hmax : max (max (-193/1000:ℝ) (-193/1000)) (max (-193/1000) (-193/1000)) = -193/1000 := by
    norm_num
  rw [hmax] at hbox
  have hw0 : 0 ≤ s1 - s0 := by linarith
  have hsq : (s1 - s0)^2 ≤ (3/20:ℝ)^2 := by nlinarith [hw, hw0]
  have h5 : (7/4 - 3/4 : ℝ)^2 / 8 * (5/8) = 5/64 := by norm_num
  rw [h5] at hbox
  nlinarith [hbox, hsq]

/-- **HB (10.8) on the box `σ ∈ [3/4, 7/4]`.**  For `0 ≤ s ≤ 17/16` and `t ∈ [3/4, 7/4]`,
`Isub s t ≤ 1/100`.

Proof route: split `s` into the eight intervals of the grid
`0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16` and on each apply `Tf72One.Isub_le_box` with the
four corner bounds from `corner_low` (`-193/1000` at both `t = 3/4` and `t = 7/4`); with
`(3/20)²/8·(13/10) + 1²/8·(5/8) = 0.0818` the bound `-0.111 ≤ 1/100` follows by `norm_num`/`linarith`
(the last `s`-cell is only `1/80` wide). -/
theorem cell_0 (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 17/16) (ht0 : 3/4 ≤ t) (ht1 : t ≤ 7/4) :
    Work.ZeroFreeTables.OffAxis.Isub s t ≤ 1/100 := by
  rcases lt_or_ge s (3/20) with h1 | h1
  · exact cell_eight s t 0 (3/20) hs0 (le_of_lt h1) ht0 ht1 (by norm_num) (by norm_num)
      (corner_low 0 (3/4) (by simp) (by simp)) (corner_low 0 (7/4) (by simp) (by simp))
      (corner_low (3/20) (3/4) (by simp) (by simp)) (corner_low (3/20) (7/4) (by simp) (by simp))
      (by norm_num)
  · rcases lt_or_ge s (3/10) with h2 | h2
    · exact cell_eight s t (3/20) (3/10) h1 (le_of_lt h2) ht0 ht1 (by norm_num) (by norm_num)
        (corner_low (3/20) (3/4) (by simp) (by simp)) (corner_low (3/20) (7/4) (by simp) (by simp))
        (corner_low (3/10) (3/4) (by simp) (by simp)) (corner_low (3/10) (7/4) (by simp) (by simp))
        (by norm_num)
    · rcases lt_or_ge s (9/20) with h3 | h3
      · exact cell_eight s t (3/10) (9/20) h2 (le_of_lt h3) ht0 ht1 (by norm_num) (by norm_num)
          (corner_low (3/10) (3/4) (by simp) (by simp)) (corner_low (3/10) (7/4) (by simp) (by simp))
          (corner_low (9/20) (3/4) (by simp) (by simp)) (corner_low (9/20) (7/4) (by simp) (by simp))
          (by norm_num)
      · rcases lt_or_ge s (3/5) with h4 | h4
        · exact cell_eight s t (9/20) (3/5) h3 (le_of_lt h4) ht0 ht1 (by norm_num) (by norm_num)
            (corner_low (9/20) (3/4) (by simp) (by simp)) (corner_low (9/20) (7/4) (by simp) (by simp))
            (corner_low (3/5) (3/4) (by simp) (by simp)) (corner_low (3/5) (7/4) (by simp) (by simp))
            (by norm_num)
        · rcases lt_or_ge s (3/4) with h5 | h5
          · exact cell_eight s t (3/5) (3/4) h4 (le_of_lt h5) ht0 ht1 (by norm_num) (by norm_num)
              (corner_low (3/5) (3/4) (by simp) (by simp)) (corner_low (3/5) (7/4) (by simp) (by simp))
              (corner_low (3/4) (3/4) (by simp) (by simp)) (corner_low (3/4) (7/4) (by simp) (by simp))
              (by norm_num)
          · rcases lt_or_ge s (9/10) with h6 | h6
            · exact cell_eight s t (3/4) (9/10) h5 (le_of_lt h6) ht0 ht1 (by norm_num) (by norm_num)
                (corner_low (3/4) (3/4) (by simp) (by simp)) (corner_low (3/4) (7/4) (by simp) (by simp))
                (corner_low (9/10) (3/4) (by simp) (by simp)) (corner_low (9/10) (7/4) (by simp) (by simp))
                (by norm_num)
            · rcases lt_or_ge s (21/20) with h7 | h7
              · exact cell_eight s t (9/10) (21/20) h6 (le_of_lt h7) ht0 ht1 (by norm_num) (by norm_num)
                  (corner_low (9/10) (3/4) (by simp) (by simp)) (corner_low (9/10) (7/4) (by simp) (by simp))
                  (corner_low (21/20) (3/4) (by simp) (by simp)) (corner_low (21/20) (7/4) (by simp) (by simp))
                  (by norm_num)
              · exact cell_eight s t (21/20) (17/16) h7 hs1 ht0 ht1 (by norm_num) (by norm_num)
                  (corner_low (21/20) (3/4) (by simp) (by simp)) (corner_low (21/20) (7/4) (by simp) (by simp))
                  (corner_low (17/16) (3/4) (by simp) (by simp)) (corner_low (17/16) (7/4) (by simp) (by simp))
                  (by norm_num)

end Work.OffAxis.Tf72One
