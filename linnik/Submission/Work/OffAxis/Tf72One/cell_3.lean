import Mathlib
import Submission.Work.OffAxis.Tf72One.Box
import Submission.Work.OffAxis.Tf72One.corner_mid
import Submission.Work.OffAxis.Tf72One.Mss_bound
import Submission.Work.OffAxis.Tf72One.Mtt_bound
import Submission.Work.OffAxis.Tf72One.abs_interp_error_le

noncomputable section
namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables
open Work.ZeroFreeTables.OffAxis
open MeasureTheory intervalIntegral

/-! ## Sorry-free interpolation lemmas for `Isub`

`Box.lean` glues corner bounds into a box bound `Isub_le_box` using two interpolation lemmas,
but those (`Work.OffAxis.Tf72One.Isub_le_interp_s` and, through `integrand_interp_le`,
`Work.OffAxis.Tf72One.Isub_le_interp_t`) still rest on `sorry`.  We reprove them here, with
independent names and self-contained proofs, so that `cell_3` rests only on the permitted axioms. -/

/-- `iteratedDeriv 2 F = deriv (deriv F)` (the two-fold iterate of `deriv`). -/
private lemma itderiv_two (F : ℝ → ℝ) : iteratedDeriv 2 F = deriv (deriv F) := by
  have h1 : iteratedDeriv 2 F = deriv (iteratedDeriv 1 F) := by
    simpa using (iteratedDeriv_succ (f := F) (n := 1))
  have h2 : iteratedDeriv 1 F = deriv F := by
    simpa [iteratedDeriv_zero] using (iteratedDeriv_succ (f := F) (n := 0))
  rw [h1, h2]

/-! ### Pointwise interpolation for the `σ`-integrand -/

/-- **Pointwise `σ`-interpolation.**  For fixed `y`, the function `t ↦ (e^{sy}-2)cos(ty)g72 y`
has second derivative of absolute value at most `y²|e^{sy}-2|g72 y`, so the sharp two-point
interpolation bound applies pointwise. -/
theorem integrand_interp_le_t (s t a b y : ℝ) (hab : a < b) (hta : a ≤ t) (htb : t ≤ b)
    (hy : y ∈ Set.Icc (0:ℝ) 2) :
    (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y ≤
      (b - t)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (a*y) * g72 y)
        + (t - a)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (b*y) * g72 y)
        + (b - a)^2/8 * (y^2 * |Real.exp (s*y) - 2| * g72 y) := by
  have hgy : 0 ≤ g72 y := g72_nonneg hy.1 hy.2
  set W : ℝ := (b - t)/(b - a) * Real.cos (a*y) + (t - a)/(b - a) * Real.cos (b*y) with hW
  set C : ℝ := (Real.exp (s*y) - 2) * g72 y with hC
  set E : ℝ := (b - a)^2/8 * y^2 with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hcos : |Real.cos (t*y) - W| ≤ E := by
    have hmain : |Real.cos (t*y)
        - ((b - t)/(b - a) * Real.cos (a*y) + (t - a)/(b - a) * Real.cos (b*y))|
        ≤ (b - a)^2/8 * y^2 := by
      refine abs_interp_error_le (fun u : ℝ => Real.cos (u*y)) a b t (y^2)
        hab ⟨hta, htb⟩ ?_ ?_
      · have hfun : (fun u : ℝ => Real.cos (u*y)) = (fun u : ℝ => Real.cos (y*u)) := by
          funext u; rw [mul_comm]
        rw [hfun]
        exact (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).contDiffOn
      · intro z _
        have hcomp := congrFun (iteratedDeriv_comp_const_mul (f := Real.cos) (n := 2)
          Real.contDiff_cos y) z
        have hfun : (fun u : ℝ => Real.cos (u*y)) = (fun u : ℝ => Real.cos (y*u)) := by
          funext u; rw [mul_comm]
        rw [hfun, hcomp, abs_mul, abs_of_nonneg (sq_nonneg y)]
        calc y^2 * |iteratedDeriv 2 Real.cos (y*z)| ≤ y^2 * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_iteratedDeriv_cos_le_one 2 (y*z)) (sq_nonneg y)
          _ = y^2 := by ring
    simpa [hW, hE] using hmain
  have key : C * Real.cos (t*y) ≤ C * W + |C| * E := by
    rcases le_total 0 C with hC0 | hC0
    · have h1 : Real.cos (t*y) ≤ W + E := by linarith [(abs_le.mp hcos).2]
      have hstep : C * Real.cos (t*y) ≤ C * (W + E) := mul_le_mul_of_nonneg_left h1 hC0
      have hCE : C * E ≤ |C| * E := mul_le_mul_of_nonneg_right (le_abs_self C) hE0
      have hexp : C * (W + E) = C * W + C * E := by ring
      linarith [hstep, hCE, hexp]
    · have h1 : W - E ≤ Real.cos (t*y) := by linarith [(abs_le.mp hcos).1]
      have hstep : C * Real.cos (t*y) ≤ C * (W - E) := mul_le_mul_of_nonpos_left h1 hC0
      have hexp : C * (W - E) = C * W + |C| * E := by rw [abs_of_nonpos hC0]; ring
      linarith [hstep, hexp]
  have hR : C * W + |C| * E
      = (b - t)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (a*y) * g72 y)
        + (t - a)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (b*y) * g72 y)
        + (b - a)^2/8 * (y^2 * |Real.exp (s*y) - 2| * g72 y) := by
    rw [hW, hE, hC, abs_mul, abs_of_nonneg hgy]
    ring
  calc (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y
      = C * Real.cos (t*y) := by rw [hC]; ring
    _ ≤ C * W + |C| * E := key
    _ = _ := hR

/-! ### Pointwise interpolation for the `s`-integrand -/

/-- **Pointwise `s`-interpolation.**  For fixed `y`, the function `u ↦ (e^{uy}-2)cos(ty)g72 y`
has second derivative at most `y² e^{s1 y} g72 y` in absolute value on `[s0,s1]` (for
`s1 ≤ 17/16`, `y ∈ [0,2]`). -/
private theorem integrand_interp_le_s_aux (t s s0 s1 y : ℝ) (hs : s0 < s1) (hs0 : s0 ≤ s) (hs1 : s ≤ s1)
    (hy : y ∈ Set.Icc (0:ℝ) 2) :
    (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y ≤
      (s1 - s)/(s1 - s0) * ((Real.exp (s0*y) - 2) * Real.cos (t*y) * g72 y)
        + (s - s0)/(s1 - s0) * ((Real.exp (s1*y) - 2) * Real.cos (t*y) * g72 y)
        + (s1 - s0)^2/8 * (y^2 * Real.exp (s1*y) * g72 y) := by
  have hgy : 0 ≤ g72 y := g72_nonneg hy.1 hy.2
  set C0 : ℝ := Real.cos (t*y) * g72 y with hC0
  set G : ℝ → ℝ := fun u => Real.exp (u*y) with hG
  set F : ℝ → ℝ := fun u => (G u - 2) * C0 with hF
  have hE : ∀ u : ℝ, HasDerivAt (fun u : ℝ => Real.exp (u*y)) (Real.exp (u*y) * y) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => u * y) y u := by
      simpa using (hasDerivAt_id u).mul_const y
    have h2 := (Real.hasDerivAt_exp (u*y)).comp u h1
    have hfun : (Real.exp ∘ fun u : ℝ => u * y) = (fun u : ℝ => Real.exp (u*y)) := by
      funext u; rfl
    rwa [hfun] at h2
  have hder1 : deriv (fun u : ℝ => Real.exp (u*y)) = fun u => Real.exp (u*y) * y :=
    funext fun u => (hE u).deriv
  have hder2 : deriv (fun u : ℝ => Real.exp (u*y) * y) = fun u => (Real.exp (u*y)*y)*y :=
    funext fun u => ((hE u).mul_const y).deriv
  have hGbound : |G s - ((s1 - s)/(s1 - s0) * G s0 + (s - s0)/(s1 - s0) * G s1)|
      ≤ (s1 - s0)^2/8 * (y^2 * Real.exp (s1*y)) := by
    refine abs_interp_error_le G s0 s1 s (y^2 * Real.exp (s1*y)) hs ⟨hs0, hs1⟩ ?_ ?_
    · rw [hG]; fun_prop
    · intro z hz
      have hit : iteratedDeriv 2 G z = (Real.exp (z*y)*y)*y := by
        rw [hG, itderiv_two, hder1, hder2]
      rw [hit]
      have h1 : |(Real.exp (z*y)*y)*y| = y^2 * Real.exp (z*y) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg _), abs_of_nonneg hy.1]; ring
      rw [h1]
      have hzy : Real.exp (z*y) ≤ Real.exp (s1*y) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_of_lt hz.2) hy.1)
      exact mul_le_mul_of_nonneg_left hzy (sq_nonneg y)
  have hsum : (s1 - s)/(s1 - s0) + (s - s0)/(s1 - s0) = 1 := by
    rw [← add_div, show s1 - s + (s - s0) = s1 - s0 by ring, div_self (by linarith)]
  have hdiff : F s - ((s1 - s)/(s1 - s0) * F s0 + (s - s0)/(s1 - s0) * F s1)
      = C0 * (G s - ((s1 - s)/(s1 - s0) * G s0 + (s - s0)/(s1 - s0) * G s1)) := by
    have h2 : (s1 - s)/(s1 - s0) * (2:ℝ) + (s - s0)/(s1 - s0) * 2 = 2 := by
      rw [← add_mul, hsum, one_mul]
    simp only [hF]
    rw [show (G s - 2) * C0
          - ((s1 - s)/(s1 - s0) * ((G s0 - 2) * C0) + (s - s0)/(s1 - s0) * ((G s1 - 2) * C0))
        = C0 * (G s - ((s1 - s)/(s1 - s0) * G s0 + (s - s0)/(s1 - s0) * G s1))
          + C0 * ((s1 - s)/(s1 - s0) * 2 + (s - s0)/(s1 - s0) * 2 - 2) by ring]
    rw [h2]; ring
  have hC0le : |C0| ≤ g72 y := by
    have h1 : |C0| = |Real.cos (t*y)| * g72 y := by rw [hC0, abs_mul, abs_of_nonneg hgy]
    rw [h1]
    calc |Real.cos (t*y)| * g72 y ≤ 1 * g72 y :=
          mul_le_mul_of_nonneg_right (Real.abs_cos_le_one (t*y)) hgy
      _ = g72 y := by ring
  have habs : |F s - ((s1 - s)/(s1 - s0) * F s0 + (s - s0)/(s1 - s0) * F s1)|
      ≤ (s1 - s0)^2/8 * (y^2 * Real.exp (s1*y) * g72 y) := by
    rw [hdiff, abs_mul]
    calc |C0| * |G s - ((s1 - s)/(s1 - s0) * G s0 + (s - s0)/(s1 - s0) * G s1)|
        ≤ g72 y * ((s1 - s0)^2/8 * (y^2 * Real.exp (s1*y))) :=
          mul_le_mul hC0le hGbound (abs_nonneg _) hgy
      _ = (s1 - s0)^2/8 * (y^2 * Real.exp (s1*y) * g72 y) := by ring
  have hFs : F s = (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y := by
    simp only [hF, hG, hC0]; ring
  have hF0 : F s0 = (Real.exp (s0*y) - 2) * Real.cos (t*y) * g72 y := by
    simp only [hF, hG, hC0]; ring
  have hF1 : F s1 = (Real.exp (s1*y) - 2) * Real.cos (t*y) * g72 y := by
    simp only [hF, hG, hC0]; ring
  have hmain := (abs_le.mp habs).2
  rw [hFs, hF0, hF1] at hmain
  linarith [hmain]


/-! ### Integration: the two interpolation lemmas -/

/-- **`σ`-interpolation for `Isub`** (auxiliary, general endpoint pair). -/
theorem isub_le_interp_aux_t2 (s t a b : ℝ) (hab : a < b) (hta : a ≤ t) (htb : t ≤ b)
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
        (b - t)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (a*y) * g72 y)
        + (t - a)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (b*y) * g72 y)
        + (b - a)^2/8 * (y^2 * |Real.exp (s*y) - 2| * g72 y) :=
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
      = (b - t)/(b - a) * Isub s a + (t - a)/(b - a) * Isub s b
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

/-- **`s`-interpolation for `Isub`** (auxiliary, general endpoint pair). -/
theorem isub_le_interp_aux_s2 (s t s0 s1 : ℝ) (hs : s0 < s1) (hs0 : s0 ≤ s) (hs1 : s ≤ s1)
    (hM : ∫ y in (0:ℝ)..2, y^2 * Real.exp (s1*y) * g72 y ≤ 13/10) :
    Isub s t ≤ max (Isub s0 t) (Isub s1 t) + (s1 - s0)^2/8 * (13/10) := by
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
        (s1 - s)/(s1 - s0) * ((Real.exp (s0*y) - 2) * Real.cos (t*y) * g72 y)
        + (s - s0)/(s1 - s0) * ((Real.exp (s1*y) - 2) * Real.cos (t*y) * g72 y)
        + (s1 - s0)^2/8 * (y^2 * Real.exp (s1*y) * g72 y) :=
    fun y hy => integrand_interp_le_s_aux t s s0 s1 y hs hs0 hs1 hy
  have hsumI : IntervalIntegrable
      (fun y : ℝ => (s1 - s)/(s1 - s0) * ((Real.exp (s0*y) - 2) * Real.cos (t*y) * g72 y)
        + (s - s0)/(s1 - s0) * ((Real.exp (s1*y) - 2) * Real.cos (t*y) * g72 y)
        + (s1 - s0)^2/8 * (y^2 * Real.exp (s1*y) * g72 y)) volume (0:ℝ) 2 :=
    ((hI0.const_mul _).add (hI1.const_mul _)).add (hIe.const_mul _)
  have hmono := intervalIntegral.integral_mono_on (show (0:ℝ) ≤ 2 by norm_num) hIt hsumI hpt
  have hsplit : (∫ y in (0:ℝ)..2, ((s1 - s)/(s1 - s0) * ((Real.exp (s0*y) - 2) * Real.cos (t*y) * g72 y)
        + (s - s0)/(s1 - s0) * ((Real.exp (s1*y) - 2) * Real.cos (t*y) * g72 y)
        + (s1 - s0)^2/8 * (y^2 * Real.exp (s1*y) * g72 y)))
      = (s1 - s)/(s1 - s0) * Isub s0 t + (s - s0)/(s1 - s0) * Isub s1 t
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

/-- **`σ`-interpolation for `Isub`.** -/
theorem Isub_le_interp_t2 (s t t0 t1 : ℝ) (hs0 : 0 ≤ s) (hs17 : s ≤ 17/16)
    (ht0 : t0 ≤ t) (ht1 : t ≤ t1) :
    Isub s t ≤ max (Isub s t0) (Isub s t1) + (t1 - t0)^2/8 * (5/8) := by
  rcases lt_or_ge t0 t1 with h | h
  · exact isub_le_interp_aux_t2 s t t0 t1 h ht0 ht1 (Mtt_bound s hs0 hs17)
  · have ht1t0 : t1 = t0 := le_antisymm h (le_trans ht0 ht1)
    have htt0 : t = t0 := le_antisymm (by rw [ht1t0] at ht1; exact ht1) ht0
    rw [htt0, ht1t0]
    simp

/-- **`s`-interpolation for `Isub`.** -/
theorem Isub_le_interp_s2 (s t s0 s1 : ℝ) (hs0 : s0 ≤ s) (hs1 : s ≤ s1) (h0 : 0 ≤ s0)
    (h17 : s1 ≤ 17/16) :
    Isub s t ≤ max (Isub s0 t) (Isub s1 t) + (s1 - s0)^2/8 * (13/10) := by
  rcases lt_or_ge s0 s1 with h | h
  · exact isub_le_interp_aux_s2 s t s0 s1 h hs0 hs1
      (Mss_bound s1 (le_trans h0 (le_trans hs0 hs1)) h17)
  · have hs1s0 : s1 = s0 := le_antisymm h (le_trans hs0 hs1)
    have hss0 : s = s0 := le_antisymm (by rw [hs1s0] at hs1; exact hs1) hs0
    rw [hss0, hs1s0]
    simp

/-- **Box bound from corner bounds** (sorry-free copy of `Isub_le_box`). -/
theorem Isub_le_box2 (s t s0 s1 t0 t1 B00 B01 B10 B11 : ℝ)
    (hs0 : s0 ≤ s) (hs1 : s ≤ s1) (ht0 : t0 ≤ t) (ht1 : t ≤ t1)
    (h0 : 0 ≤ s0) (h17 : s1 ≤ 17/16)
    (h00 : Isub s0 t0 ≤ B00) (h01 : Isub s0 t1 ≤ B01)
    (h10 : Isub s1 t0 ≤ B10) (h11 : Isub s1 t1 ≤ B11) :
    Isub s t ≤ max (max B00 B01) (max B10 B11)
      + (s1 - s0) ^ 2 / 8 * (13/10) + (t1 - t0) ^ 2 / 8 * (5/8) := by
  have hs1' : 0 ≤ s1 := le_trans h0 (le_trans hs0 hs1)
  have hs017 : s0 ≤ 17/16 := le_trans hs0 (le_trans hs1 h17)
  have hIs := Isub_le_interp_s2 s t s0 s1 hs0 hs1 h0 h17
  have h0t := Isub_le_interp_t2 s0 t t0 t1 h0 hs017 ht0 ht1
  have h1t := Isub_le_interp_t2 s1 t t0 t1 hs1' h17 ht0 ht1
  have hmax0 : max (Isub s0 t0) (Isub s0 t1) ≤ max B00 B01 := max_le_max h00 h01
  have hmax1 : max (Isub s1 t0) (Isub s1 t1) ≤ max B10 B11 := max_le_max h10 h11
  have h0t' : Isub s0 t ≤ max (max B00 B01) (max B10 B11) + (t1 - t0)^2/8*(5/8) := by
    have hle : max B00 B01 ≤ max (max B00 B01) (max B10 B11) := le_max_left _ _
    linarith [h0t, hmax0, hle]
  have h1t' : Isub s1 t ≤ max (max B00 B01) (max B10 B11) + (t1 - t0)^2/8*(5/8) := by
    have hle : max B10 B11 ≤ max (max B00 B01) (max B10 B11) := le_max_right _ _
    linarith [h1t, hmax1, hle]
  have hmax : max (Isub s0 t) (Isub s1 t)
      ≤ max (max B00 B01) (max B10 B11) + (t1 - t0)^2/8*(5/8) := max_le h0t' h1t'
  linarith [hIs, hmax]

/-- One grid cell of the `s`-range: the corner bounds `-7/200` at both `t`-endpoints plus the
two interpolation errors give `Isub s t ≤ 1/100`. -/
private lemma cellbound (s t s0 s1 : ℝ) (hs0' : s0 ≤ s) (hs1' : s ≤ s1)
    (h0 : 0 ≤ s0) (h17 : s1 ≤ 17/16) (ht0 : 3 ≤ t) (ht1 : t ≤ 13/4)
    (hg0 : s0 ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ))
    (hg1 : s1 ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ))
    (hnum : (s1 - s0)^2/8*(13/10) + (13/4 - 3)^2/8*(5/8) ≤ 1/100 + 7/200) :
    Isub s t ≤ 1/100 := by
  have h := Isub_le_box2 s t s0 s1 3 (13/4) (-7/200) (-7/200) (-7/200) (-7/200)
      hs0' hs1' ht0 ht1 h0 h17
      (corner_mid s0 3 hg0 (by simp)) (corner_mid s0 (13/4) hg0 (by simp))
      (corner_mid s1 3 hg1 (by simp)) (corner_mid s1 (13/4) hg1 (by simp))
  simp only [max_self] at h
  linarith [h, hnum]

/-- **HB (10.8) on the box `σ ∈ [3, 13/4]`.**  For `0 ≤ s ≤ 17/16` and `t ∈ [3, 13/4]`,
`Isub s t ≤ 1/100`.

Proof route: as in `cell_0`, with `corner_mid` at both endpoints (`-7/200`); the error is at most
`(3/20)²/8·(13/10) + (1/4)²/8·(5/8) = 0.00854`, giving `-0.0265 ≤ 1/100`. -/
theorem cell_3 (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 17/16) (ht0 : 3 ≤ t) (ht1 : t ≤ 13/4) :
    Work.ZeroFreeTables.OffAxis.Isub s t ≤ 1/100 := by
  rcases le_or_gt s (3/20) with h1 | h1
  · exact cellbound s t 0 (3/20) hs0 h1 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (3/10) with h2 | h2
  · exact cellbound s t (3/20) (3/10) (le_of_lt h1) h2 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (9/20) with h3 | h3
  · exact cellbound s t (3/10) (9/20) (le_of_lt h2) h3 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (3/5) with h4 | h4
  · exact cellbound s t (9/20) (3/5) (le_of_lt h3) h4 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (3/4) with h5 | h5
  · exact cellbound s t (3/5) (3/4) (le_of_lt h4) h5 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (9/10) with h6 | h6
  · exact cellbound s t (3/4) (9/10) (le_of_lt h5) h6 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (21/20) with h7 | h7
  · exact cellbound s t (9/10) (21/20) (le_of_lt h6) h7 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  · exact cellbound s t (21/20) (17/16) (le_of_lt h7) hs1 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)

end Work.OffAxis.Tf72One
