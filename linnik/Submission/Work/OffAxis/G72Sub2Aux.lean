/-
# OffAxis/G72Sub2Aux — auxiliary facts for `Work.OffAxis.G72Sub2Bound`

We prove here the structural lemmas for

  `LHF s σ = Re G72(-s+iσ) - Re G72(iσ) = ∫₀² (e^{sy}-1) cos(σy) g72 y dy`

used in the proof of `Work.OffAxis.G72Sub2Bound`:

* `LHF_eq_integral`   : the integral representation;
* `LHF_eq_closed`     : the closed form in terms of `RA72`, `RB72`, `RI72`;
* `trig_bounds`       : rational enclosures of `cos θ`, `sin θ` at `θ = 3,4,5,6,7,8`;
* `exp_bounds_e`      : rational enclosures of `e` and `e²`;
* `LHF_sigma_interp`  : two-point interpolation in `σ` with error `(t₁-t₀)²/8·(13/10)`;
* `LHF_s_interp`      : two-point interpolation in `s` with error `(s₁-s₀)²/8·(13/10)`;
* `LHF_large_sigma`   : the analytic bound `LHF s σ ≤ 4/15` for `σ ≥ 4`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.OffAxis.Tf72One.abs_interp_error_le
import Submission.Work.OffAxis.Tf72One.Mss_bound
import Submission.Work.OffAxis.Tf72One.trig_low
import Submission.Work.OffAxis.Tf72One.exp_bounds

open scoped Interval
open MeasureTheory

noncomputable section
namespace Work.OffAxis

open Work.ZeroFreeTables Work.ZeroFreeTables.OffAxis

/-- `LHF s σ = Re G72(-s+iσ) - Re G72(iσ)`: the quantity bounded by `G72Sub2Bound`. -/
noncomputable def LHF (s σ : ℝ) : ℝ :=
  (G72 ((-(s : ℂ)) + (σ : ℂ) * Complex.I)).re - (G72 ((σ : ℂ) * Complex.I)).re

/-- The integral representation of `LHF`. -/
theorem LHF_eq_integral (s σ : ℝ) :
    LHF s σ = ∫ y in (0:ℝ)..2, (Real.exp (s*y) - 1) * Real.cos (σ*y) * g72 y := by
  have h1 : (G72 ((-(s : ℂ)) + (σ : ℂ) * Complex.I)).re
      = ∫ y in (0:ℝ)..2, Real.exp (s*y) * Real.cos (σ*y) * g72 y := by
    rw [G72_re_eq_integral]
    apply intervalIntegral.integral_congr
    intro y _
    have e1 : ((-(s : ℂ)) + (σ : ℂ) * Complex.I).re = -s := by simp
    have i1 : ((-(s : ℂ)) + (σ : ℂ) * Complex.I).im = σ := by simp
    rw [e1, i1]; ring_nf
  have h2 : (G72 ((σ : ℂ) * Complex.I)).re
      = ∫ y in (0:ℝ)..2, Real.cos (σ*y) * g72 y := by
    rw [G72_re_eq_integral]
    apply intervalIntegral.integral_congr
    intro y _
    have e1 : (((σ : ℂ) * Complex.I)).re = 0 := by simp
    have i1 : (((σ : ℂ) * Complex.I)).im = σ := by simp
    rw [e1, i1]; simp
  have hint1 : IntervalIntegrable (fun y : ℝ => Real.exp (s*y) * Real.cos (σ*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
  have hint2 : IntervalIntegrable (fun y : ℝ => Real.cos (σ*y) * g72 y) volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
  rw [LHF, h1, h2, ← intervalIntegral.integral_sub hint1 hint2]
  apply intervalIntegral.integral_congr
  intro y _
  ring

/-- The closed form of `LHF` in terms of `RA72`, `RB72`, `RI72`. -/
theorem LHF_eq_closed {s σ : ℝ} (hσ : σ ≠ 0) (hρ : s^2 + σ^2 ≠ 0) :
    LHF s σ = (RA72 s σ - RA72 0 σ)
      + Real.exp (2*s) * (Real.cos (2*σ) * RB72 s σ + Real.sin (2*σ) * RI72 s σ)
      - (Real.cos (2*σ) * RB72 0 σ + Real.sin (2*σ) * RI72 0 σ) := by
  have h1 := G72ReClosed0 (s := s) (σ := σ) hρ
  have h2 := G72_re_closed_zero hσ
  have hw : (-(s : ℂ)) = ((-s : ℝ) : ℂ) := by push_cast; ring
  rw [LHF, hw, h1, h2, RA72_zero, RB72_zero, RI72_zero]
  ring

/-- Rational enclosures of `cos θ`, `sin θ` at `θ = 3, 4, 5, 6, 7, 8`. -/
theorem trig_bounds :
    (-98999250/100000000 : ℝ) ≤ Real.cos 3 ∧ Real.cos 3 ≤ (-98999249/100000000 : ℝ) ∧
      (14112000/100000000 : ℝ) ≤ Real.sin 3 ∧ Real.sin 3 ≤ (14112001/100000000 : ℝ) ∧
    (-65364363/100000000 : ℝ) ≤ Real.cos 4 ∧ Real.cos 4 ≤ (-65364362/100000000 : ℝ) ∧
      (-75680250/100000000 : ℝ) ≤ Real.sin 4 ∧ Real.sin 4 ≤ (-75680249/100000000 : ℝ) ∧
    (28366218/100000000 : ℝ) ≤ Real.cos 5 ∧ Real.cos 5 ≤ (28366219/100000000 : ℝ) ∧
      (-95892428/100000000 : ℝ) ≤ Real.sin 5 ∧ Real.sin 5 ≤ (-95892427/100000000 : ℝ) ∧
    (96017028/100000000 : ℝ) ≤ Real.cos 6 ∧ Real.cos 6 ≤ (96017029/100000000 : ℝ) ∧
      (-27941550/100000000 : ℝ) ≤ Real.sin 6 ∧ Real.sin 6 ≤ (-27941549/100000000 : ℝ) ∧
    (75390225/100000000 : ℝ) ≤ Real.cos 7 ∧ Real.cos 7 ≤ (75390226/100000000 : ℝ) ∧
      (65698659/100000000 : ℝ) ≤ Real.sin 7 ∧ Real.sin 7 ≤ (65698660/100000000 : ℝ) ∧
    (-14550004/100000000 : ℝ) ≤ Real.cos 8 ∧ Real.cos 8 ≤ (-14550003/100000000 : ℝ) ∧
      (98935824/100000000 : ℝ) ≤ Real.sin 8 ∧ Real.sin 8 ≤ (98935825/100000000 : ℝ) := by
  refine ⟨
    Tf72One.cos_tay_ge 3 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.cos_tay_le 3 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.sin_tay_ge 3 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.sin_tay_le 3 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.cos_tay_ge 4 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.cos_tay_le 4 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.sin_tay_ge 4 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.sin_tay_le 4 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.cos_tay_ge 5 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.cos_tay_le 5 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.sin_tay_ge 5 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.sin_tay_le 5 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.cos_tay_ge 6 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.cos_tay_le 6 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.sin_tay_ge 6 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.sin_tay_le 6 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.cos_tay_ge 7 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.cos_tay_le 7 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.sin_tay_ge 7 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.sin_tay_le 7 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.cos_tay_ge 8 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.cos_tay_le 8 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.sin_tay_ge 8 18 _ (by norm_num [Finset.sum_range_succ]),
    Tf72One.sin_tay_le 8 18 _ (by norm_num [Finset.sum_range_succ])⟩

/-- Rational enclosures of `e` and `e²`. -/
theorem exp_bounds_e :
    (2.7182818283 : ℝ) ≤ Real.exp 1 ∧ Real.exp 1 ≤ (2.7182818286 : ℝ) ∧
      (7.389 : ℝ) ≤ Real.exp 2 ∧ Real.exp 2 ≤ (7.39 : ℝ) := by
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
    ring
  refine ⟨Real.exp_one_gt_d9.le, Real.exp_one_lt_d9.le, ?_, ?_⟩
  · rw [h2]; nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
  · rw [h2]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]

/-! ## Pointwise two-point interpolation error bounds -/

/-- Two-point interpolation error for `u ↦ cos (u*y)`: the linear interpolant at `t0`, `t1`
differs from `cos (t*y)` by at most `(t1-t0)²/8 * y²`. -/
lemma cos_interp_point (y t t0 t1 : ℝ) (h : t0 < t1) (ht0 : t0 ≤ t) (ht1 : t ≤ t1) :
    |Real.cos (t*y) - ((t1-t)/(t1-t0) * Real.cos (t0*y) + (t-t0)/(t1-t0) * Real.cos (t1*y))|
      ≤ (t1-t0)^2/8 * y^2 := by
  have hf : ContDiffOn ℝ 2 (fun u : ℝ => Real.cos (u*y)) (Set.Icc t0 t1) := by fun_prop
  have hderiv : ∀ u : ℝ,
      iteratedDeriv 2 (fun u : ℝ => Real.cos (u*y)) u = -(y^2) * Real.cos (u*y) := by
    intro u
    have h1 : iteratedDeriv 1 (fun u : ℝ => Real.cos (u*y))
        = fun u : ℝ => -(Real.sin (u*y)) * y := by
      funext v
      rw [iteratedDeriv_one]
      have hv : HasDerivAt (fun u : ℝ => u*y) y v := by
        simpa using (hasDerivAt_id v).mul_const y
      exact hv.cos.deriv
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, h1]
    have hv : HasDerivAt (fun u : ℝ => u*y) y u := by
      simpa using (hasDerivAt_id u).mul_const y
    have hs : HasDerivAt (fun u : ℝ => Real.sin (u*y)) (Real.cos (u*y)*y) u := hv.sin
    have hm : HasDerivAt (fun u : ℝ => -(Real.sin (u*y)) * y) ((Real.cos (u*y)*y)*(-y)) u := by
      simpa using (hs.neg).mul_const y
    rw [hm.deriv]
    ring
  have hM : ∀ u ∈ Set.Ioo t0 t1,
      |iteratedDeriv 2 (fun u : ℝ => Real.cos (u*y)) u| ≤ y^2 := by
    intro u _
    rw [hderiv u, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg y)]
    exact mul_le_of_le_one_right (sq_nonneg y) (Real.abs_cos_le_one _)
  exact Tf72One.abs_interp_error_le (fun u : ℝ => Real.cos (u*y)) t0 t1 t (y^2) h
    ⟨ht0, ht1⟩ hf hM

/-- Two-point interpolation error for `u ↦ exp (u*y)`: the linear interpolant at `t0`, `t1`
differs from `exp (t*y)` by at most `(t1-t0)²/8 * y² exp (t1*y)` (for `y ≥ 0`). -/
lemma exp_interp_point (y t t0 t1 : ℝ) (hy : 0 ≤ y) (h : t0 < t1) (ht0 : t0 ≤ t)
    (ht1 : t ≤ t1) :
    |Real.exp (t*y) - ((t1-t)/(t1-t0) * Real.exp (t0*y) + (t-t0)/(t1-t0) * Real.exp (t1*y))|
      ≤ (t1-t0)^2/8 * (y^2 * Real.exp (t1*y)) := by
  have hf : ContDiffOn ℝ 2 (fun u : ℝ => Real.exp (u*y)) (Set.Icc t0 t1) := by fun_prop
  have hderiv : ∀ u : ℝ,
      iteratedDeriv 2 (fun u : ℝ => Real.exp (u*y)) u = (y^2) * Real.exp (u*y) := by
    intro u
    have h1 : iteratedDeriv 1 (fun u : ℝ => Real.exp (u*y))
        = fun u : ℝ => Real.exp (u*y) * y := by
      funext v
      rw [iteratedDeriv_one]
      have hv : HasDerivAt (fun u : ℝ => u*y) y v := by
        simpa using (hasDerivAt_id v).mul_const y
      exact hv.exp.deriv
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, h1]
    have hv : HasDerivAt (fun u : ℝ => u*y) y u := by
      simpa using (hasDerivAt_id u).mul_const y
    have he : HasDerivAt (fun u : ℝ => Real.exp (u*y) * y) ((Real.exp (u*y))*y*y) u := by
      simpa using (hv.exp).mul_const y
    rw [he.deriv]
    ring
  have hM : ∀ u ∈ Set.Ioo t0 t1,
      |iteratedDeriv 2 (fun u : ℝ => Real.exp (u*y)) u| ≤ y^2 * Real.exp (t1*y) := by
    intro u hu
    rw [hderiv u, abs_of_nonneg (by positivity)]
    have hmono : Real.exp (u*y) ≤ Real.exp (t1*y) :=
      Real.exp_le_exp.mpr (by nlinarith [hu.2, hy])
    nlinarith [sq_nonneg y, hmono]
  exact Tf72One.abs_interp_error_le (fun u : ℝ => Real.exp (u*y)) t0 t1 t
    (y^2 * Real.exp (t1*y)) h ⟨ht0, ht1⟩ hf hM

/-! ## The two interpolation theorems for `LHF` -/

/-- **`σ`-interpolation for `LHF`.** -/
theorem LHF_sigma_interp (s t t0 t1 : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : t0 ≤ t) (ht1 : t ≤ t1) :
    LHF s t ≤ max (LHF s t0) (LHF s t1) + (t1 - t0)^2/8*(13/10) := by
  rcases lt_or_ge t0 t1 with h | h
  · have hba : (0:ℝ) < t1 - t0 := by linarith
    have hpt : ∀ y ∈ Set.Icc (0:ℝ) 2,
        (Real.exp (s*y) - 1) * Real.cos (t*y) * g72 y ≤
          (t1-t)/(t1-t0) * ((Real.exp (s*y) - 1) * Real.cos (t0*y) * g72 y)
          + (t-t0)/(t1-t0) * ((Real.exp (s*y) - 1) * Real.cos (t1*y) * g72 y)
          + (t1-t0)^2/8 * (y^2 * (Real.exp (s*y) - 1) * g72 y) := by
      intro y hy
      have hgy : 0 ≤ (Real.exp (s*y) - 1) * g72 y := by
        have hg := g72_nonneg hy.1 hy.2
        have he1 : (1:ℝ) ≤ Real.exp (s*y) := by
          have hx : Real.exp (0:ℝ) ≤ Real.exp (s*y) := Real.exp_le_exp.mpr (mul_nonneg hs hy.1)
          simpa using hx
        exact mul_nonneg (by linarith) hg
      have hc := (abs_le.mp (cos_interp_point y t t0 t1 h ht0 ht1)).2
      have hmul := mul_le_mul_of_nonneg_left hc hgy
      nlinarith [hmul]
    have hA : IntervalIntegrable
        (fun y : ℝ => (Real.exp (s*y) - 1) * Real.cos (t*y) * g72 y) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hB : IntervalIntegrable
        (fun y : ℝ => (Real.exp (s*y) - 1) * Real.cos (t0*y) * g72 y) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hC : IntervalIntegrable
        (fun y : ℝ => (Real.exp (s*y) - 1) * Real.cos (t1*y) * g72 y) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hD : IntervalIntegrable
        (fun y : ℝ => y^2 * (Real.exp (s*y) - 1) * g72 y) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hE : IntervalIntegrable
        (fun y : ℝ => (t1-t)/(t1-t0) * ((Real.exp (s*y) - 1) * Real.cos (t0*y) * g72 y)
          + (t-t0)/(t1-t0) * ((Real.exp (s*y) - 1) * Real.cos (t1*y) * g72 y)
          + (t1-t0)^2/8 * (y^2 * (Real.exp (s*y) - 1) * g72 y)) volume (0:ℝ) 2 :=
      ((hB.const_mul _).add (hC.const_mul _)).add (hD.const_mul _)
    have hmono := intervalIntegral.integral_mono_on (show (0:ℝ) ≤ 2 by norm_num) hA hE hpt
    have hsplit : (∫ y in (0:ℝ)..2, ((t1-t)/(t1-t0) * ((Real.exp (s*y) - 1) * Real.cos (t0*y) * g72 y)
          + (t-t0)/(t1-t0) * ((Real.exp (s*y) - 1) * Real.cos (t1*y) * g72 y)
          + (t1-t0)^2/8 * (y^2 * (Real.exp (s*y) - 1) * g72 y)))
        = (t1-t)/(t1-t0) * LHF s t0 + (t-t0)/(t1-t0) * LHF s t1
          + (t1-t0)^2/8 * (∫ y in (0:ℝ)..2, y^2 * (Real.exp (s*y) - 1) * g72 y) := by
      rw [intervalIntegral.integral_add ((hB.const_mul _).add (hC.const_mul _)) (hD.const_mul _),
          intervalIntegral.integral_add (hB.const_mul _) (hC.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul,
          ← LHF_eq_integral s t0, ← LHF_eq_integral s t1]
    rw [hsplit, ← LHF_eq_integral s t] at hmono
    have h0 : 0 ≤ (t1 - t)/(t1 - t0) := div_nonneg (by linarith) (le_of_lt hba)
    have h1 : 0 ≤ (t - t0)/(t1 - t0) := div_nonneg (by linarith) (le_of_lt hba)
    have hsum : (t1 - t)/(t1 - t0) + (t - t0)/(t1 - t0) = 1 := by
      rw [← add_div, show t1 - t + (t - t0) = t1 - t0 by ring, div_self (ne_of_gt hba)]
    have hmax : (t1-t)/(t1-t0) * LHF s t0 + (t-t0)/(t1-t0) * LHF s t1
        ≤ max (LHF s t0) (LHF s t1) := by
      have hMx : (t1-t)/(t1-t0) * LHF s t0 + (t-t0)/(t1-t0) * LHF s t1
          ≤ (t1-t)/(t1-t0) * max (LHF s t0) (LHF s t1)
            + (t-t0)/(t1-t0) * max (LHF s t0) (LHF s t1) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h0)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) h1)
      calc (t1-t)/(t1-t0) * LHF s t0 + (t-t0)/(t1-t0) * LHF s t1
          ≤ _ := hMx
        _ = max (LHF s t0) (LHF s t1) := by rw [← add_mul, hsum, one_mul]
    have herr : (t1-t0)^2/8 * (∫ y in (0:ℝ)..2, y^2 * (Real.exp (s*y) - 1) * g72 y)
        ≤ (t1-t0)^2/8 * (13/10) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc (∫ y in (0:ℝ)..2, y^2 * (Real.exp (s*y) - 1) * g72 y)
          ≤ ∫ y in (0:ℝ)..2, y^2 * Real.exp (s*y) * g72 y := by
            apply intervalIntegral.integral_mono_on (by norm_num) hD
            · apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
            · intro y hy
              have hg := g72_nonneg hy.1 hy.2
              have h1 : (0:ℝ) ≤ Real.exp (s*y) - 1 := by
                have hx : Real.exp (0:ℝ) ≤ Real.exp (s*y) :=
                  Real.exp_le_exp.mpr (mul_nonneg hs hy.1)
                linarith [Real.exp_zero]
              have hy2 : (0:ℝ) ≤ y^2 := sq_nonneg y
              nlinarith [hg, h1, hy2, Real.exp_pos (s*y)]
        _ ≤ 13/10 := Tf72One.Mss_bound s hs (by linarith)
    linarith [hmono, hmax, herr]
  · have ht1t0 : t1 = t0 := le_antisymm h (le_trans ht0 ht1)
    have htt0 : t = t0 := le_antisymm (by rw [ht1t0] at ht1; exact ht1) ht0
    rw [htt0, ht1t0]
    simp

/-- **`s`-interpolation for `LHF`.** -/
theorem LHF_s_interp (s t s0 s1 : ℝ) (h0 : 0 ≤ s0) (h17 : s1 ≤ 17/16)
    (hs0 : s0 ≤ s) (hs1 : s ≤ s1) :
    LHF s t ≤ max (LHF s0 t) (LHF s1 t) + (s1 - s0)^2/8*(13/10) := by
  rcases lt_or_ge s0 s1 with h | h
  · have hba : (0:ℝ) < s1 - s0 := by linarith
    have hpt : ∀ y ∈ Set.Icc (0:ℝ) 2,
        (Real.exp (s*y) - 1) * Real.cos (t*y) * g72 y ≤
          (s1-s)/(s1-s0) * ((Real.exp (s0*y) - 1) * Real.cos (t*y) * g72 y)
          + (s-s0)/(s1-s0) * ((Real.exp (s1*y) - 1) * Real.cos (t*y) * g72 y)
          + (s1-s0)^2/8 * (y^2 * Real.exp (s1*y) * g72 y) := by
      intro y hy
      have hy0 : 0 ≤ y := hy.1
      have hg : 0 ≤ g72 y := g72_nonneg hy.1 hy.2
      have hD : |Real.exp (s*y) - ((s1-s)/(s1-s0) * Real.exp (s0*y)
          + (s-s0)/(s1-s0) * Real.exp (s1*y))|
          ≤ (s1-s0)^2/8 * (y^2 * Real.exp (s1*y)) :=
        exp_interp_point y s s0 s1 hy0 h hs0 hs1
      have hAB : (s1-s)/(s1-s0) + (s-s0)/(s1-s0) = 1 := by
        rw [← add_div, show s1 - s + (s - s0) = s1 - s0 by ring, div_self (ne_of_gt hba)]
      have hdiff : (Real.exp (s*y) - 1) * Real.cos (t*y) * g72 y
          - ((s1-s)/(s1-s0) * ((Real.exp (s0*y) - 1) * Real.cos (t*y) * g72 y)
             + (s-s0)/(s1-s0) * ((Real.exp (s1*y) - 1) * Real.cos (t*y) * g72 y))
          = (Real.exp (s*y) - ((s1-s)/(s1-s0) * Real.exp (s0*y)
              + (s-s0)/(s1-s0) * Real.exp (s1*y))) * Real.cos (t*y) * g72 y := by
        rw [show Real.exp (s*y) - 1
            = Real.exp (s*y) - ((s1-s)/(s1-s0) + (s-s0)/(s1-s0)) by rw [hAB] ]
        ring
      have hb : (Real.exp (s*y) - ((s1-s)/(s1-s0) * Real.exp (s0*y)
            + (s-s0)/(s1-s0) * Real.exp (s1*y))) * Real.cos (t*y) * g72 y
          ≤ (s1-s0)^2/8 * (y^2 * Real.exp (s1*y)) * g72 y := by
        have habs1 : (Real.exp (s*y) - ((s1-s)/(s1-s0) * Real.exp (s0*y)
              + (s-s0)/(s1-s0) * Real.exp (s1*y))) * Real.cos (t*y) * g72 y
            ≤ |Real.exp (s*y) - ((s1-s)/(s1-s0) * Real.exp (s0*y)
              + (s-s0)/(s1-s0) * Real.exp (s1*y))| * |Real.cos (t*y)| * g72 y := by
          have h2 : (Real.exp (s*y) - ((s1-s)/(s1-s0) * Real.exp (s0*y)
                + (s-s0)/(s1-s0) * Real.exp (s1*y))) * Real.cos (t*y)
              ≤ |Real.exp (s*y) - ((s1-s)/(s1-s0) * Real.exp (s0*y)
                + (s-s0)/(s1-s0) * Real.exp (s1*y))| * |Real.cos (t*y)| := by
            rw [← abs_mul]
            exact le_abs_self _
          exact mul_le_mul_of_nonneg_right h2 hg
        have h5 : (0:ℝ) ≤ (s1-s0)^2/8 * (y^2 * Real.exp (s1*y)) := by positivity
        have habs2 : |Real.exp (s*y) - ((s1-s)/(s1-s0) * Real.exp (s0*y)
              + (s-s0)/(s1-s0) * Real.exp (s1*y))| * |Real.cos (t*y)| * g72 y
            ≤ ((s1-s0)^2/8 * (y^2 * Real.exp (s1*y))) * 1 * g72 y := by
          have h2 : |Real.exp (s*y) - ((s1-s)/(s1-s0) * Real.exp (s0*y)
                + (s-s0)/(s1-s0) * Real.exp (s1*y))| * |Real.cos (t*y)|
              ≤ ((s1-s0)^2/8 * (y^2 * Real.exp (s1*y))) * 1 :=
            mul_le_mul hD (Real.abs_cos_le_one _) (abs_nonneg _) h5
          exact mul_le_mul_of_nonneg_right h2 hg
        calc _ ≤ |Real.exp (s*y) - ((s1-s)/(s1-s0) * Real.exp (s0*y)
              + (s-s0)/(s1-s0) * Real.exp (s1*y))| * |Real.cos (t*y)| * g72 y := habs1
          _ ≤ ((s1-s0)^2/8 * (y^2 * Real.exp (s1*y))) * 1 * g72 y := habs2
          _ = (s1-s0)^2/8 * (y^2 * Real.exp (s1*y)) * g72 y := by ring
      linarith [hdiff, hb]
    have hA : IntervalIntegrable
        (fun y : ℝ => (Real.exp (s*y) - 1) * Real.cos (t*y) * g72 y) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hB : IntervalIntegrable
        (fun y : ℝ => (Real.exp (s0*y) - 1) * Real.cos (t*y) * g72 y) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hC : IntervalIntegrable
        (fun y : ℝ => (Real.exp (s1*y) - 1) * Real.cos (t*y) * g72 y) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hD : IntervalIntegrable
        (fun y : ℝ => y^2 * Real.exp (s1*y) * g72 y) volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    have hE : IntervalIntegrable
        (fun y : ℝ => (s1-s)/(s1-s0) * ((Real.exp (s0*y) - 1) * Real.cos (t*y) * g72 y)
          + (s-s0)/(s1-s0) * ((Real.exp (s1*y) - 1) * Real.cos (t*y) * g72 y)
          + (s1-s0)^2/8 * (y^2 * Real.exp (s1*y) * g72 y)) volume (0:ℝ) 2 :=
      ((hB.const_mul _).add (hC.const_mul _)).add (hD.const_mul _)
    have hmono := intervalIntegral.integral_mono_on (show (0:ℝ) ≤ 2 by norm_num) hA hE hpt
    have hsplit : (∫ y in (0:ℝ)..2, ((s1-s)/(s1-s0) * ((Real.exp (s0*y) - 1) * Real.cos (t*y) * g72 y)
          + (s-s0)/(s1-s0) * ((Real.exp (s1*y) - 1) * Real.cos (t*y) * g72 y)
          + (s1-s0)^2/8 * (y^2 * Real.exp (s1*y) * g72 y)))
        = (s1-s)/(s1-s0) * LHF s0 t + (s-s0)/(s1-s0) * LHF s1 t
          + (s1-s0)^2/8 * (∫ y in (0:ℝ)..2, y^2 * Real.exp (s1*y) * g72 y) := by
      rw [intervalIntegral.integral_add ((hB.const_mul _).add (hC.const_mul _)) (hD.const_mul _),
          intervalIntegral.integral_add (hB.const_mul _) (hC.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul,
          ← LHF_eq_integral s0 t, ← LHF_eq_integral s1 t]
    rw [hsplit, ← LHF_eq_integral s t] at hmono
    have h0' : 0 ≤ (s1 - s)/(s1 - s0) := div_nonneg (by linarith) (le_of_lt hba)
    have h1' : 0 ≤ (s - s0)/(s1 - s0) := div_nonneg (by linarith) (le_of_lt hba)
    have hsum : (s1 - s)/(s1 - s0) + (s - s0)/(s1 - s0) = 1 := by
      rw [← add_div, show s1 - s + (s - s0) = s1 - s0 by ring, div_self (ne_of_gt hba)]
    have hmax : (s1-s)/(s1-s0) * LHF s0 t + (s-s0)/(s1-s0) * LHF s1 t
        ≤ max (LHF s0 t) (LHF s1 t) := by
      have hMx : (s1-s)/(s1-s0) * LHF s0 t + (s-s0)/(s1-s0) * LHF s1 t
          ≤ (s1-s)/(s1-s0) * max (LHF s0 t) (LHF s1 t)
            + (s-s0)/(s1-s0) * max (LHF s0 t) (LHF s1 t) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h0')
          (mul_le_mul_of_nonneg_left (le_max_right _ _) h1')
      calc (s1-s)/(s1-s0) * LHF s0 t + (s-s0)/(s1-s0) * LHF s1 t
          ≤ _ := hMx
        _ = max (LHF s0 t) (LHF s1 t) := by rw [← add_mul, hsum, one_mul]
    have herr : (s1-s0)^2/8 * (∫ y in (0:ℝ)..2, y^2 * Real.exp (s1*y) * g72 y)
        ≤ (s1-s0)^2/8 * (13/10) :=
      mul_le_mul_of_nonneg_left (Tf72One.Mss_bound s1 (by linarith) h17) (by positivity)
    linarith [hmono, hmax, herr]
  · have hs1s0 : s1 = s0 := le_antisymm h (le_trans hs0 hs1)
    have hss0 : s = s0 := le_antisymm (by rw [hs1s0] at hs1; exact hs1) hs0
    rw [hss0, hs1s0]
    simp

end Work.OffAxis
end
