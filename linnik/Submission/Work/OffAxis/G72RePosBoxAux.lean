/-
# OffAxis/G72RePosBoxAux

Auxiliary material for `Work.OffAxis.G72RePosBox`:

* explicit antiderivatives of `y ↦ y cos(3y/2) g72 y` and of `y ↦ e^{-y} cos(3y/2) g72 y`;
* the resulting integral identities (FTC);
* numerical bounds for `cos 3`, `sin 3`, `e^{-π/3}` and `Q0(π/3)`;
* the two certificates
  * `G72YCosNonneg`: `0 ≤ ∫₀² y e^{-τy} cos(3y/2) g72 y dy` for `0 ≤ τ ≤ 1`
    (so `τ ↦ Re G72(τ + 3i/2)` is non-increasing on `[0,1]`);
  * `G72ReCornerGe`: `2/5 ≤ Re G72(1 + 3i/2)` (the corner value).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.ZeroFreeTables.OffAxis.CosSinTaylor

noncomputable section
namespace Work.OffAxis

open Work.ZeroFreeTables
open Work.ZeroFreeTables.OffAxis

/-! ## Derivatives of polynomials of degree `≤ 6` -/

lemma hasDerivAt_poly7 (c0 c1 c2 c3 c4 c5 c6 t : ℝ) :
    HasDerivAt (fun s : ℝ => c0 + c1*s + c2*s^2 + c3*s^3 + c4*s^4 + c5*s^5 + c6*s^6)
      (c1 + c2*(2*t) + c3*(3*t^2) + c4*(4*t^3) + c5*(5*t^4) + c6*(6*t^5)) t := by
  have h0 : HasDerivAt (fun _ : ℝ => c0) 0 t := hasDerivAt_const t c0
  have h1 : HasDerivAt (fun s : ℝ => c1*s) c1 t := by
    simpa using (hasDerivAt_id t).const_mul c1
  have h2 : HasDerivAt (fun s : ℝ => c2*s^2) (c2*(2*t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_mul c2
  have h3 : HasDerivAt (fun s : ℝ => c3*s^3) (c3*(3*t^2)) t := by
    simpa using (hasDerivAt_pow 3 t).const_mul c3
  have h4 : HasDerivAt (fun s : ℝ => c4*s^4) (c4*(4*t^3)) t := by
    simpa using (hasDerivAt_pow 4 t).const_mul c4
  have h5 : HasDerivAt (fun s : ℝ => c5*s^5) (c5*(5*t^4)) t := by
    simpa using (hasDerivAt_pow 5 t).const_mul c5
  have h6 : HasDerivAt (fun s : ℝ => c6*s^6) (c6*(6*t^5)) t := by
    simpa using (hasDerivAt_pow 6 t).const_mul c6
  have h := (((((h0.add h1).add h2).add h3).add h4).add h5).add h6
  exact h.congr_deriv (by ring)

/-! ## The antiderivatives -/

/-- `cos`-coefficient of the antiderivative of `y cos(3y/2) g72 y`. -/
def P0 (y : ℝ) : ℝ :=
  832/405 + (-1280/243)*y + (-16/9)*y^2 + (160/81)*y^3 + 0*y^4 + (-4/45)*y^5 + 0*y^6

/-- Derivative of `P0`. -/
def dP0 (y : ℝ) : ℝ :=
  -1280/243 + (-32/9)*y + (160/27)*y^2 + 0*y^3 + (-4/9)*y^4 + 0*y^5

/-- `sin`-coefficient of the antiderivative of `y cos(3y/2) g72 y`. -/
def Q0 (y : ℝ) : ℝ :=
  2560/729 + (416/135)*y + (-320/81)*y^2 + (-8/9)*y^3 + (20/27)*y^4 + 0*y^5 + (-1/45)*y^6

/-- Derivative of `Q0`. -/
def dQ0 (y : ℝ) : ℝ :=
  416/135 + (-640/81)*y + (-8/3)*y^2 + (80/27)*y^3 + 0*y^4 + (-2/15)*y^5

/-- `cos`-coefficient of the antiderivative of `e^{-y} cos(3y/2) g72 y`. -/
def Ph (y : ℝ) : ℝ :=
  (-9660544/24134045) + (441632/1113879)*y + (44008/85683)*y^2 + (-696/2197)*y^3
    + (-10/507)*y^4 + (2/195)*y^5 + 0*y^6

/-- Derivative of `Ph`. -/
def dPh (y : ℝ) : ℝ :=
  441632/1113879 + (88016/85683)*y + (-2088/2197)*y^2 + (-40/507)*y^3 + (2/39)*y^4 + 0*y^5

/-- `sin`-coefficient of the antiderivative of `e^{-y} cos(3y/2) g72 y`. -/
def Qh (y : ℝ) : ℝ :=
  4342496/24134045 + (-156128/371293)*y + (2488/28561)*y^2 + (628/2197)*y^3
    + (-8/169)*y^4 + (-1/65)*y^5 + 0*y^6

/-- Derivative of `Qh`. -/
def dQh (y : ℝ) : ℝ :=
  -156128/371293 + (4976/28561)*y + (1884/2197)*y^2 + (-32/169)*y^3 + (-1/13)*y^4 + 0*y^5

/-- Antiderivative of `y ↦ y * cos (3y/2) * g72 y`. -/
def AY (y : ℝ) : ℝ := P0 y * Real.cos (3*y/2) + Q0 y * Real.sin (3*y/2)

/-- Antiderivative of `y ↦ exp (-y) * cos (3y/2) * g72 y`. -/
def Eh (y : ℝ) : ℝ :=
  Real.exp (-y) * (Ph y * Real.cos (3*y/2) + Qh y * Real.sin (3*y/2))

/-! ## The two ordinary differential identities -/

lemma P0_ode (y : ℝ) : dP0 y + (3/2) * Q0 y = y * g72 y := by
  simp only [dP0, Q0, g72]; ring

lemma Q0_ode (y : ℝ) : dQ0 y - (3/2) * P0 y = 0 := by
  simp only [dQ0, P0]; ring

lemma Ph_ode (y : ℝ) : -Ph y + dPh y + (3/2) * Qh y = g72 y := by
  simp only [Ph, dPh, Qh, g72]; ring

lemma Qh_ode (y : ℝ) : -Qh y + dQh y - (3/2) * Ph y = 0 := by
  simp only [Qh, dQh, Ph]; ring

/-! ## Derivative facts -/

lemma hasDerivAt_P0 (y : ℝ) : HasDerivAt P0 (dP0 y) y := by
  have h := hasDerivAt_poly7 (832/405) (-1280/243) (-16/9) (160/81) (0:ℝ) (-4/45) (0:ℝ) y
  refine h.congr_deriv ?_
  simp only [dP0]; ring

lemma hasDerivAt_Q0 (y : ℝ) : HasDerivAt Q0 (dQ0 y) y := by
  have h := hasDerivAt_poly7 (2560/729) (416/135) (-320/81) (-8/9) (20/27) (0:ℝ) (-1/45) y
  refine h.congr_deriv ?_
  simp only [dQ0]; ring

lemma hasDerivAt_Ph (y : ℝ) : HasDerivAt Ph (dPh y) y := by
  have h := hasDerivAt_poly7 (-9660544/24134045) (441632/1113879) (44008/85683) (-696/2197)
    (-10/507) (2/195) (0:ℝ) y
  refine h.congr_deriv ?_
  simp only [dPh]; ring

lemma hasDerivAt_Qh (y : ℝ) : HasDerivAt Qh (dQh y) y := by
  have h := hasDerivAt_poly7 (4342496/24134045) (-156128/371293) (2488/28561) (628/2197)
    (-8/169) (-1/65) (0:ℝ) y
  refine h.congr_deriv ?_
  simp only [dQh]; ring

lemma hasDerivAt_cos_three (y : ℝ) :
    HasDerivAt (fun z : ℝ => Real.cos (3*z/2)) (-(3/2) * Real.sin (3*y/2)) y := by
  have h1 : HasDerivAt (fun z : ℝ => 3*z/2) ((3:ℝ)/2) y := by
    have h : HasDerivAt (fun z : ℝ => 3*z) (3:ℝ) y := by
      simpa using (hasDerivAt_id y).const_mul (3:ℝ)
    simpa using h.div_const (2:ℝ)
  have h2 := (Real.hasDerivAt_cos (3*y/2)).comp y h1
  refine h2.congr_deriv ?_
  ring

lemma hasDerivAt_sin_three (y : ℝ) :
    HasDerivAt (fun z : ℝ => Real.sin (3*z/2)) ((3/2) * Real.cos (3*y/2)) y := by
  have h1 : HasDerivAt (fun z : ℝ => 3*z/2) ((3:ℝ)/2) y := by
    have h : HasDerivAt (fun z : ℝ => 3*z) (3:ℝ) y := by
      simpa using (hasDerivAt_id y).const_mul (3:ℝ)
    simpa using h.div_const (2:ℝ)
  have h2 := (Real.hasDerivAt_sin (3*y/2)).comp y h1
  refine h2.congr_deriv ?_
  ring

lemma AY_deriv (y : ℝ) :
    dP0 y * Real.cos (3*y/2) + P0 y * (-(3/2) * Real.sin (3*y/2))
      + (dQ0 y * Real.sin (3*y/2) + Q0 y * ((3/2) * Real.cos (3*y/2)))
      = y * Real.cos (3*y/2) * g72 y := by
  have h1 : dP0 y = y * g72 y - (3/2) * Q0 y := by linarith [P0_ode y]
  have h2 : dQ0 y = (3/2) * P0 y := by linarith [Q0_ode y]
  rw [h1, h2]; ring

lemma Eh_deriv (y : ℝ) :
    -Real.exp (-y) * (Ph y * Real.cos (3*y/2) + Qh y * Real.sin (3*y/2))
      + Real.exp (-y) * (dPh y * Real.cos (3*y/2) + Ph y * (-(3/2) * Real.sin (3*y/2))
          + (dQh y * Real.sin (3*y/2) + Qh y * ((3/2) * Real.cos (3*y/2))))
      = Real.exp (-y) * Real.cos (3*y/2) * g72 y := by
  have h1 : dPh y = g72 y + Ph y - (3/2) * Qh y := by linarith [Ph_ode y]
  have h2 : dQh y = Qh y + (3/2) * Ph y := by linarith [Qh_ode y]
  rw [h1, h2]; ring

lemma hasDerivAt_AY (y : ℝ) : HasDerivAt AY (y * Real.cos (3*y/2) * g72 y) y := by
  have h1 : HasDerivAt (fun z : ℝ => P0 z * Real.cos (3*z/2))
      (dP0 y * Real.cos (3*y/2) + P0 y * (-(3/2) * Real.sin (3*y/2))) y :=
    (hasDerivAt_P0 y).mul (hasDerivAt_cos_three y)
  have h2 : HasDerivAt (fun z : ℝ => Q0 z * Real.sin (3*z/2))
      (dQ0 y * Real.sin (3*y/2) + Q0 y * ((3/2) * Real.cos (3*y/2))) y :=
    (hasDerivAt_Q0 y).mul (hasDerivAt_sin_three y)
  have h := h1.add h2
  refine h.congr_deriv (AY_deriv y)

lemma hasDerivAt_Eh (y : ℝ) : HasDerivAt Eh (Real.exp (-y) * Real.cos (3*y/2) * g72 y) y := by
  have h1 : HasDerivAt (fun z : ℝ => Ph z * Real.cos (3*z/2))
      (dPh y * Real.cos (3*y/2) + Ph y * (-(3/2) * Real.sin (3*y/2))) y :=
    (hasDerivAt_Ph y).mul (hasDerivAt_cos_three y)
  have h2 : HasDerivAt (fun z : ℝ => Qh z * Real.sin (3*z/2))
      (dQh y * Real.sin (3*y/2) + Qh y * ((3/2) * Real.cos (3*y/2))) y :=
    (hasDerivAt_Qh y).mul (hasDerivAt_sin_three y)
  have h3 : HasDerivAt (fun z : ℝ => Ph z * Real.cos (3*z/2) + Qh z * Real.sin (3*z/2))
      (dPh y * Real.cos (3*y/2) + Ph y * (-(3/2) * Real.sin (3*y/2))
        + (dQh y * Real.sin (3*y/2) + Qh y * ((3/2) * Real.cos (3*y/2)))) y := h1.add h2
  have h4 : HasDerivAt (fun z : ℝ => Real.exp (-z)) (-(Real.exp (-y))) y := by
    have h : HasDerivAt (fun z : ℝ => -z) (-1:ℝ) y := (hasDerivAt_id y).neg
    have h5 := (Real.hasDerivAt_exp (-y)).comp y h
    simpa only [Function.comp_def, mul_neg, mul_one] using h5
  have h := h4.mul h3
  refine h.congr_deriv (Eh_deriv y)

/-! ## The integral identities -/

lemma AY_at_pi_div_three : AY (Real.pi/3) = Q0 (Real.pi/3) := by
  have harg : (3*(Real.pi/3)/2) = Real.pi/2 := by ring
  simp only [AY]
  rw [harg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

lemma AY_at_zero : AY 0 = 832/405 := by
  simp only [AY, P0, Q0]; norm_num

lemma AY_at_two : AY 2 = -(640/243) * Real.cos 3 - (2048/729) * Real.sin 3 := by
  have harg : (3*(2:ℝ)/2) = 3 := by norm_num
  simp only [AY, P0, Q0]
  rw [harg]
  norm_num
  ring

lemma integral_y_cos_three_pi3 :
    (∫ y in (0:ℝ)..(Real.pi/3), y * Real.cos (3*y/2) * g72 y)
      = Q0 (Real.pi/3) - 832/405 := by
  have hint : IntervalIntegrable (fun y : ℝ => y * Real.cos (3*y/2) * g72 y)
      MeasureTheory.volume (0:ℝ) (Real.pi/3) := by
    apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_AY y) hint,
    AY_at_pi_div_three, AY_at_zero]

lemma integral_y_cos_three_pi3_two :
    (∫ y in (Real.pi/3)..2, y * Real.cos (3*y/2) * g72 y)
      = -(640/243) * Real.cos 3 - (2048/729) * Real.sin 3 - Q0 (Real.pi/3) := by
  have hint : IntervalIntegrable (fun y : ℝ => y * Real.cos (3*y/2) * g72 y)
      MeasureTheory.volume (Real.pi/3) 2 := by
    apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_AY y) hint,
    AY_at_two, AY_at_pi_div_three]

lemma integral_exp_cos_three :
    (∫ y in (0:ℝ)..2, Real.exp (-y) * Real.cos (3*y/2) * g72 y)
      = Real.exp (-2) * (Ph 2 * Real.cos 3 + Qh 2 * Real.sin 3) - Ph 0 := by
  have hint : IntervalIntegrable (fun y : ℝ => Real.exp (-y) * Real.cos (3*y/2) * g72 y)
      MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
  have h2 : Eh 2 = Real.exp (-2) * (Ph 2 * Real.cos 3 + Qh 2 * Real.sin 3) := by
    have harg : (3*(2:ℝ)/2) = (3:ℝ) := by norm_num
    rw [show Eh 2 = Real.exp (-(2:ℝ))
        * (Ph 2 * Real.cos (3*(2:ℝ)/2) + Qh 2 * Real.sin (3*(2:ℝ)/2)) from by
      simp only [Eh]]
    rw [harg]
  have h0 : Eh 0 = Ph 0 := by
    have harg0 : (3*(0:ℝ)/2) = (0:ℝ) := by norm_num
    rw [show Eh 0 = Real.exp (-(0:ℝ))
        * (Ph 0 * Real.cos (3*(0:ℝ)/2) + Qh 0 * Real.sin (3*(0:ℝ)/2)) from by
      simp only [Eh]]
    rw [harg0]
    simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_Eh y) hint, h2, h0]

/-! ## Numerical bounds -/

lemma sin_three_lower : (141/1000 : ℝ) ≤ Real.sin 3 := by
  have h := sin_taylor_bound (x := (3:ℝ)) (by norm_num) 7
  have h2 : (∑ k ∈ Finset.range 7, (-1:ℝ)^k * (3:ℝ)^(2*k+1) / (Nat.factorial (2*k+1) : ℝ))
      = (516651/3660800 : ℝ) := by norm_num
  rw [h2] at h
  have h3 : (3:ℝ)^(2*7+1) / (Nat.factorial (2*7+1) : ℝ) = (19683/1793792000 : ℝ) := by norm_num
  rw [h3] at h
  have h4 := (abs_le.mp h).1
  linarith

lemma sin_three_upper : Real.sin 3 ≤ (142/1000 : ℝ) := by
  have h := sin_taylor_bound (x := (3:ℝ)) (by norm_num) 7
  have h2 : (∑ k ∈ Finset.range 7, (-1:ℝ)^k * (3:ℝ)^(2*k+1) / (Nat.factorial (2*k+1) : ℝ))
      = (516651/3660800 : ℝ) := by norm_num
  rw [h2] at h
  have h3 : (3:ℝ)^(2*7+1) / (Nat.factorial (2*7+1) : ℝ) = (19683/1793792000 : ℝ) := by norm_num
  rw [h3] at h
  have h4 := (abs_le.mp h).2
  linarith

lemma cos_three_lower : -(99/100 : ℝ) ≤ Real.cos 3 := by
  have h := cos_taylor_bound (x := (3:ℝ)) (by norm_num) 7
  have h2 : (∑ k ∈ Finset.range (7+1), (-1:ℝ)^k * (3:ℝ)^(2*k) / (Nat.factorial (2*k) : ℝ))
      = -(355168841/358758400 : ℝ) := by norm_num
  rw [h2] at h
  have h3 : (3:ℝ)^(2*(7+1)) / (Nat.factorial (2*(7+1)) : ℝ) = (59049/28700672000 : ℝ) := by
    norm_num
  rw [h3] at h
  have h4 := (abs_le.mp h).1
  linarith

lemma cos_three_upper : Real.cos 3 ≤ -(9899/10000 : ℝ) := by
  have h := cos_taylor_bound (x := (3:ℝ)) (by norm_num) 7
  have h2 : (∑ k ∈ Finset.range (7+1), (-1:ℝ)^k * (3:ℝ)^(2*k) / (Nat.factorial (2*k) : ℝ))
      = -(355168841/358758400 : ℝ) := by norm_num
  rw [h2] at h
  have h3 : (3:ℝ)^(2*(7+1)) / (Nat.factorial (2*(7+1)) : ℝ) = (59049/28700672000 : ℝ) := by
    norm_num
  rw [h3] at h
  have h4 := (abs_le.mp h).2
  linarith

lemma exp_one_le_aux : Real.exp 1 ≤ (27186/10000 : ℝ) := by
  have h := Real.exp_bound' (x := (1:ℝ)) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (1:ℝ)^m / (Nat.factorial m : ℝ)) = (685/252 : ℝ) := by
    norm_num
  rw [h2] at h
  have h5 : (1:ℝ)^8 * (8 + 1) / ((Nat.factorial 8 : ℝ) * 8) ≤ (1/3000 : ℝ) := by norm_num
  linarith

lemma exp_twenty_le_aux : Real.exp ((1:ℝ)/20) ≤ (10513/10000 : ℝ) := by
  have h := Real.exp_bound' (x := ((1:ℝ)/20)) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, ((1:ℝ)/20)^m / (Nat.factorial m : ℝ))
      = (2260653365647/2150400000000 : ℝ) := by norm_num
  rw [h2] at h
  have h5 : ((1:ℝ)/20)^8 * (8 + 1) / ((Nat.factorial 8 : ℝ) * 8) ≤ (1/1000000000000 : ℝ) := by
    norm_num
  linarith

lemma exp_21_20_le : Real.exp ((21:ℝ)/20) ≤ 10/3 := by
  have h : Real.exp ((21:ℝ)/20) = Real.exp 1 * Real.exp ((1:ℝ)/20) := by
    rw [← Real.exp_add]; norm_num
  rw [h]
  nlinarith [exp_one_le_aux, exp_twenty_le_aux, Real.exp_pos (1:ℝ), Real.exp_pos ((1:ℝ)/20)]

lemma exp_neg_pi_div_three_ge : (3/10 : ℝ) ≤ Real.exp (-(Real.pi/3)) := by
  have h1 : Real.pi/3 ≤ (21:ℝ)/20 := by nlinarith [Real.pi_lt_d2]
  have h2 : Real.exp (-(Real.pi/3)) ≥ Real.exp (-((21:ℝ)/20)) := by
    apply Real.exp_le_exp.mpr; linarith
  have h3 : (3/10 : ℝ) ≤ Real.exp (-((21:ℝ)/20)) := by
    rw [Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos ((21:ℝ)/20))]
    nlinarith [exp_21_20_le]
  linarith

/-- `π ^ k` bounds for `k ≤ 6`, from `3.14 < π < 3.15`. -/
lemma pi_sq_lt : Real.pi^2 < (9.9225 : ℝ) := by
  nlinarith [Real.pi_gt_d2, Real.pi_lt_d2]
lemma pi_sq_gt : (9.8596 : ℝ) < Real.pi^2 := by
  nlinarith [Real.pi_gt_d2, Real.pi_lt_d2]
lemma pi_cu_lt : Real.pi^3 < (31.255875 : ℝ) := by
  nlinarith [pi_sq_lt, Real.pi_lt_d2, Real.pi_pos]
lemma pi_cu_gt : (30.959144 : ℝ) < Real.pi^3 := by
  nlinarith [pi_sq_gt, Real.pi_gt_d2, Real.pi_pos]
lemma pi_four_lt : Real.pi^4 < (98.45600625 : ℝ) := by
  nlinarith [pi_cu_lt, Real.pi_lt_d2, Real.pi_pos]
lemma pi_four_gt : (97.21171216 : ℝ) < Real.pi^4 := by
  nlinarith [pi_cu_gt, Real.pi_gt_d2, Real.pi_pos]
lemma pi_five_lt : Real.pi^5 < (310.1364196875 : ℝ) := by
  nlinarith [pi_four_lt, Real.pi_lt_d2, Real.pi_pos]
lemma pi_five_gt : (305.2447761824 : ℝ) < Real.pi^5 := by
  nlinarith [pi_four_gt, Real.pi_gt_d2, Real.pi_pos]
lemma pi_six_lt : Real.pi^6 < (976.929722015625 : ℝ) := by
  nlinarith [pi_five_lt, Real.pi_lt_d2, Real.pi_pos]
lemma pi_six_gt : (958.468597212736 : ℝ) < Real.pi^6 := by
  nlinarith [pi_five_gt, Real.pi_gt_d2, Real.pi_pos]

lemma Q0_pi_div_three_lower : (2.2 : ℝ) ≤ Q0 (Real.pi/3) := by
  have h : Q0 (Real.pi/3) = 2560/729 + (416/405)*Real.pi - (320/729)*Real.pi^2
      - (8/243)*Real.pi^3 + (20/2187)*Real.pi^4 - (1/32805)*Real.pi^6 := by
    simp only [Q0]; ring
  rw [h]
  nlinarith [pi_sq_lt, pi_cu_lt, pi_four_gt, pi_six_lt, Real.pi_gt_d2, Real.pi_pos]

lemma Q0_pi_div_three_upper : Q0 (Real.pi/3) ≤ (2.255 : ℝ) := by
  have h : Q0 (Real.pi/3) = 2560/729 + (416/405)*Real.pi - (320/729)*Real.pi^2
      - (8/243)*Real.pi^3 + (20/2187)*Real.pi^4 - (1/32805)*Real.pi^6 := by
    simp only [Q0]; ring
  rw [h]
  nlinarith [pi_sq_gt, pi_cu_gt, pi_four_lt, pi_six_gt, Real.pi_lt_d2, Real.pi_pos]

/-! ## The certificates -/

theorem G72YCosNonneg (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    0 ≤ ∫ y in (0:ℝ)..2, y * Real.exp (-(τ * y)) * Real.cos (3 * y / 2) * g72 y := by
  have hpi3pos : (0:ℝ) < Real.pi/3 := by positivity
  have hpi3lt2 : Real.pi/3 < 2 := by nlinarith [Real.pi_lt_d2]
  set F : ℝ → ℝ := fun y => y * Real.exp (-(τ*y)) * Real.cos (3*y/2) * g72 y with hF
  have hI1 : IntervalIntegrable F MeasureTheory.volume (0:ℝ) (Real.pi/3) := by
    apply Continuous.intervalIntegrable; simp only [hF, g72]; fun_prop
  have hI2 : IntervalIntegrable F MeasureTheory.volume (Real.pi/3) 2 := by
    apply Continuous.intervalIntegrable; simp only [hF, g72]; fun_prop
  have hsplit : (∫ y in (0:ℝ)..2, F y)
      = (∫ y in (0:ℝ)..(Real.pi/3), F y) + (∫ y in (Real.pi/3)..2, F y) :=
    (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
  -- Piece 1: the exponential is bounded below by `3/10` and `cos` is nonnegative
  have hcomp1 : IntervalIntegrable (fun y : ℝ => (3/10:ℝ) * (y * Real.cos (3*y/2) * g72 y))
      MeasureTheory.volume (0:ℝ) (Real.pi/3) := by
    apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
  have hI1c : IntervalIntegrable (fun y : ℝ => y * Real.cos (3*y/2) * g72 y)
      MeasureTheory.volume (0:ℝ) (Real.pi/3) := by
    apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
  have hb1 : (3/10) * (∫ y in (0:ℝ)..(Real.pi/3), y * Real.cos (3*y/2) * g72 y)
      ≤ ∫ y in (0:ℝ)..(Real.pi/3), F y := by
    rw [hF, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hpi3pos.le hcomp1 hI1
    intro y hy
    have hy0 : 0 ≤ y := hy.1
    have hy1 : y ≤ Real.pi/3 := hy.2
    have hcos : 0 ≤ Real.cos (3*y/2) :=
      Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
    have hg : 0 ≤ g72 y := g72_nonneg hy0 (by linarith)
    have he : (3/10 : ℝ) ≤ Real.exp (-(τ*y)) := by
      have h4 : Real.exp (-(Real.pi/3)) ≤ Real.exp (-(τ*y)) := by
        apply Real.exp_le_exp.mpr; nlinarith
      exact le_trans exp_neg_pi_div_three_ge h4
    have h5 : (3/10) * (y * Real.cos (3*y/2) * g72 y)
        ≤ Real.exp (-(τ*y)) * (y * Real.cos (3*y/2) * g72 y) :=
      mul_le_mul_of_nonneg_right he (mul_nonneg (mul_nonneg hy0 hcos) hg)
    calc (3/10) * (y * Real.cos (3*y/2) * g72 y)
        ≤ Real.exp (-(τ*y)) * (y * Real.cos (3*y/2) * g72 y) := h5
      _ = y * Real.exp (-(τ*y)) * Real.cos (3*y/2) * g72 y := by ring
  -- Piece 2: `cos` is nonpositive and the exponential is at most `1`
  have hI2c : IntervalIntegrable (fun y : ℝ => y * Real.cos (3*y/2) * g72 y)
      MeasureTheory.volume (Real.pi/3) 2 := by
    apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
  have hb2 : (∫ y in (Real.pi/3)..2, y * Real.cos (3*y/2) * g72 y)
      ≤ ∫ y in (Real.pi/3)..2, F y := by
    rw [hF]
    apply intervalIntegral.integral_mono_on hpi3lt2.le hI2c hI2
    intro y hy
    have hy0 : 0 ≤ y := le_trans hpi3pos.le hy.1
    have hcos : Real.cos (3*y/2) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (by nlinarith [hy.1])
        (by nlinarith [hy.2, Real.pi_gt_three])
    have hg : 0 ≤ g72 y := g72_nonneg hy0 hy.2
    have he : Real.exp (-(τ*y)) ≤ 1 := by
      calc Real.exp (-(τ*y)) ≤ Real.exp 0 := by
            apply Real.exp_le_exp.mpr; nlinarith
        _ = 1 := Real.exp_zero
    have h5 : Real.cos (3*y/2) ≤ Real.cos (3*y/2) * Real.exp (-(τ*y)) := by
      have h6 : 0 ≤ 1 - Real.exp (-(τ*y)) := by linarith
      have h7 := mul_nonpos_of_nonpos_of_nonneg hcos h6
      nlinarith [h7]
    have h8 : y * Real.cos (3*y/2) * g72 y ≤ y * Real.cos (3*y/2) * Real.exp (-(τ*y)) * g72 y := by
      have h9 : 0 ≤ y * g72 y := mul_nonneg hy0 hg
      nlinarith [mul_le_mul_of_nonneg_right h5 h9]
    calc y * Real.cos (3*y/2) * g72 y
        ≤ y * Real.cos (3*y/2) * Real.exp (-(τ*y)) * g72 y := h8
      _ = y * Real.exp (-(τ*y)) * Real.cos (3*y/2) * g72 y := by ring
  rw [hsplit]
  rw [integral_y_cos_three_pi3] at hb1
  rw [integral_y_cos_three_pi3_two] at hb2
  have hnum : 0 ≤ (3/10) * (Q0 (Real.pi/3) - 832/405)
      + (-(640/243) * Real.cos 3 - (2048/729) * Real.sin 3 - Q0 (Real.pi/3)) := by
    nlinarith [Q0_pi_div_three_lower, Q0_pi_div_three_upper, cos_three_upper, sin_three_upper]
  linarith

theorem G72ReCornerGe :
    (2/5 : ℝ) ≤ (Work.ZeroFreeTables.G72 (((1:ℂ) + ((3:ℂ)/2) * Complex.I))).re := by
  have hre : (Work.ZeroFreeTables.G72 ((1:ℂ) + ((3:ℂ)/2) * Complex.I)).re
      = ∫ y in (0:ℝ)..2, Real.exp (-y) * Real.cos (3*y/2) * g72 y := by
    rw [G72_re_eq_integral]
    apply intervalIntegral.integral_congr
    intro y _
    have h1 : (((1:ℂ) + ((3:ℂ)/2) * Complex.I)).re = 1 := by simp
    have h2 : (((1:ℂ) + ((3:ℂ)/2) * Complex.I)).im = 3/2 := by simp
    rw [h1, h2]
    ring_nf
  rw [hre, integral_exp_cos_three]
  have hPh2 : Ph 2 = -(360128/4826809) := by simp only [Ph]; norm_num
  have hQh2 : Qh 2 = (3496704/4826809) := by simp only [Qh]; norm_num
  have hPh0 : Ph 0 = -(9660544/24134045) := by simp only [Ph]; norm_num
  have hcos3 : Real.cos 3 < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [Real.pi_lt_d2])
      (by linarith [Real.pi_gt_three])
  have hsin3 : 0 < Real.sin 3 :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])
  rw [hPh2, hQh2, hPh0]
  have hkey : 0 ≤ Real.exp (-2) * (-(360128/4826809) * Real.cos 3 + (3496704/4826809) * Real.sin 3) := by
    apply mul_nonneg (Real.exp_pos _).le
    have h1 : 0 ≤ -(360128/4826809) * Real.cos 3 :=
      mul_nonneg_of_nonpos_of_nonpos (by norm_num) hcos3.le
    have h2 : 0 ≤ (3496704/4826809) * Real.sin 3 := mul_nonneg (by norm_num) hsin3.le
    linarith
  have hnum : (2/5 : ℝ) ≤ 9660544/24134045 := by norm_num
  linarith

end Work.OffAxis
