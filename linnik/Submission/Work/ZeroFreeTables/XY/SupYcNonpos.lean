import Mathlib
import Submission.Work.ZeroFreeTables.XY.LamPrimeData

open MeasureTheory intervalIntegral

noncomputable section

namespace Work.ZeroFreeTables.XY

/-! ## The auxiliary polynomial `YcP` and the evaluation of `Yc`

Everything in this file is self-contained: we identify the integrand of `Yc` on `[0,3/2]`
with the polynomial `YcP`, exhibit an explicit antiderivative `YcF t` of `x ↦ YcP x * cos (t*x)`
(whose derivative is checked by hand), and conclude the closed form of `Yc t` via the
fundamental theorem of calculus.  The sign of the closed form then follows from the
Cauchy–Schwarz bound `a cos θ + b sin θ ≤ √(a²+b²)` and a polynomial inequality in `w = t²`.
-/

/-! ### The polynomial `x * f x` on `[0,3/2]` -/

/-- The polynomial equal to `x * xyFf x` on `[0,3/2]`. -/
def YcP (x : ℝ) : ℝ :=
  (64/45)*x + (-(256:ℝ)/81)*x^3 + (512/243)*x^4 + (-(2048:ℝ)/10935)*x^6

lemma YcP_eq_factored (x : ℝ) :
    YcP x = x * ((2/45) * (2 - (4/3)*x)^3 * (4 + 8*x + (16/9)*x^2)) := by
  rw [YcP]; ring

lemma Yc_eq_integral (t : ℝ) :
    Yc t = ∫ x in (0:ℝ)..(3/2), YcP x * Real.cos (t*x) := by
  unfold Yc
  refine intervalIntegral.integral_congr ?_
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3/2)] at hx
  show x * Real.cos (t*x) * xyFf x = YcP x * Real.cos (t*x)
  rw [xyFf_eq_poly x hx, YcP_eq_factored]
  ring

/-! ### The antiderivative -/

def ycQ0 (t : ℝ) : ℝ := 24*(512/243)/t^5 - 720*((-(2048:ℝ))/10935)/t^7
def ycQ1 (t : ℝ) : ℝ := (64/45)/t - 6*((-(256:ℝ))/81)/t^3
def ycQ2 (t : ℝ) : ℝ := -12*(512/243)/t^3 + 360*((-(2048:ℝ))/10935)/t^5
def ycQ3 (t : ℝ) : ℝ := ((-(256:ℝ))/81)/t
def ycQ4 (t : ℝ) : ℝ := (512/243)/t - 30*((-(2048:ℝ))/10935)/t^3
def ycQ6 (t : ℝ) : ℝ := ((-(2048:ℝ))/10935)/t

/-- The polynomial `Q` with `Q'' + t^2 Q = t·(x f(x))`. -/
def YcQ (t : ℝ) : ℝ → ℝ := fun x =>
  ycQ0 t + ycQ1 t * x + ycQ2 t * x^2 + ycQ3 t * x^3 + ycQ4 t * x^4 + ycQ6 t * x^6

/-- `Q'`. -/
def YcQD (t : ℝ) : ℝ → ℝ := fun x =>
  ycQ1 t + 2*(ycQ2 t) * x + 3*(ycQ3 t) * x^2 + 4*(ycQ4 t) * x^3 + 6*(ycQ6 t) * x^5

/-- `Q''`. -/
def YcQD2 (t : ℝ) : ℝ → ℝ := fun x =>
  2*(ycQ2 t) + 6*(ycQ3 t) * x + 12*(ycQ4 t) * x^2 + 30*(ycQ6 t) * x^4

/-- `R = Q'/t`. -/
def YcR (t : ℝ) : ℝ → ℝ := fun x => YcQD t x / t

/-- `R'`. -/
def YcRD (t : ℝ) : ℝ → ℝ := fun x => YcQD2 t x / t

/-- The antiderivative `Q·sin(tx) + R·cos(tx)`. -/
def YcF (t : ℝ) : ℝ → ℝ := fun x =>
  YcQ t x * Real.sin (t*x) + YcR t x * Real.cos (t*x)

lemma hasDerivAt_YcQ (t x : ℝ) : HasDerivAt (YcQ t) (YcQD t x) x := by
  have h0 : HasDerivAt (fun _ : ℝ => ycQ0 t) 0 x := hasDerivAt_const x (ycQ0 t)
  have h1 : HasDerivAt (fun y : ℝ => ycQ1 t * y) (ycQ1 t) x := by
    simpa using (hasDerivAt_id x).const_mul (ycQ1 t)
  have h2 : HasDerivAt (fun y : ℝ => ycQ2 t * y^2) (ycQ2 t * (2*x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_mul (ycQ2 t)
  have h3 : HasDerivAt (fun y : ℝ => ycQ3 t * y^3) (ycQ3 t * (3*x^2)) x := by
    simpa using (hasDerivAt_pow 3 x).const_mul (ycQ3 t)
  have h4 : HasDerivAt (fun y : ℝ => ycQ4 t * y^4) (ycQ4 t * (4*x^3)) x := by
    simpa using (hasDerivAt_pow 4 x).const_mul (ycQ4 t)
  have h6 : HasDerivAt (fun y : ℝ => ycQ6 t * y^6) (ycQ6 t * (6*x^5)) x := by
    simpa using (hasDerivAt_pow 6 x).const_mul (ycQ6 t)
  have h := ((((h0.add h1).add h2).add h3).add h4).add h6
  exact h.congr_deriv (by simp only [YcQD]; ring)

lemma hasDerivAt_YcQD (t x : ℝ) : HasDerivAt (YcQD t) (YcQD2 t x) x := by
  have h1 : HasDerivAt (fun _ : ℝ => ycQ1 t) 0 x := hasDerivAt_const x (ycQ1 t)
  have h2 : HasDerivAt (fun y : ℝ => 2*(ycQ2 t) * y) (2*(ycQ2 t)) x := by
    simpa using (hasDerivAt_id x).const_mul (2*(ycQ2 t))
  have h3 : HasDerivAt (fun y : ℝ => 3*(ycQ3 t) * y^2) (3*(ycQ3 t) * (2*x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_mul (3*(ycQ3 t))
  have h4 : HasDerivAt (fun y : ℝ => 4*(ycQ4 t) * y^3) (4*(ycQ4 t) * (3*x^2)) x := by
    simpa using (hasDerivAt_pow 3 x).const_mul (4*(ycQ4 t))
  have h5 : HasDerivAt (fun y : ℝ => 6*(ycQ6 t) * y^5) (6*(ycQ6 t) * (5*x^4)) x := by
    simpa using (hasDerivAt_pow 5 x).const_mul (6*(ycQ6 t))
  have h := ((((h1.add h2).add h3).add h4).add h5)
  exact h.congr_deriv (by simp only [YcQD2]; ring)

lemma hasDerivAt_YcR (t x : ℝ) : HasDerivAt (YcR t) (YcRD t x) x := by
  have h : HasDerivAt (YcQD t) (YcQD2 t x) x := hasDerivAt_YcQD t x
  have h2 := h.div_const t
  convert h2 using 1 <;> (first | rfl | (simp only [YcR, YcRD, Pi.div_apply]) | (simp only [YcRD]))

lemma hasDerivAt_YcF (t : ℝ) (ht : t ≠ 0) (x : ℝ) :
    HasDerivAt (YcF t) (YcP x * Real.cos (t*x)) x := by
  have hQ : HasDerivAt (YcQ t) (YcQD t x) x := hasDerivAt_YcQ t x
  have hR : HasDerivAt (YcR t) (YcRD t x) x := hasDerivAt_YcR t x
  have hs : HasDerivAt (fun y : ℝ => Real.sin (t*y)) (t * Real.cos (t*x)) x := by
    have h := (Real.hasDerivAt_sin (t*x)).comp x ((hasDerivAt_id x).const_mul t)
    convert h using 1 <;>
      (first | rfl | (funext y; simp only [Function.comp_apply, Pi.mul_apply]; ring) | ring)
  have hc : HasDerivAt (fun y : ℝ => Real.cos (t*y)) (-(t * Real.sin (t*x))) x := by
    have h := (Real.hasDerivAt_cos (t*x)).comp x ((hasDerivAt_id x).const_mul t)
    convert h using 1 <;>
      (first | rfl | (funext y; simp only [Function.comp_apply, Pi.mul_apply]; ring) | ring)
  have h := (hQ.mul hs).add (hR.mul hc)
  convert h using 1 <;>
    (first
      | rfl
      | (funext y; simp only [YcF, Pi.add_apply, Pi.mul_apply]; ring)
      | (simp only [YcQD, YcQD2, YcQ, YcR, YcRD, YcP, ycQ0, ycQ1, ycQ2, ycQ3, ycQ4, ycQ6]; field_simp; ring)
      | (simp only [YcQD, YcQD2, YcQ, YcR, YcRD, YcP]; field_simp; ring))

lemma Yc_closed_form (t : ℝ) (ht : t ≠ 0) :
    Yc t = -(64/45)/t^2 - (512/27)*(1 - Real.cos (t*(3/2)))/t^4
        - (8192/81)*Real.sin (t*(3/2))/t^5 - (16384/81)*Real.cos (t*(3/2))/t^6
        + (32768/243)*Real.sin (t*(3/2))/t^7 := by
  have hcont : Continuous (fun x : ℝ => YcP x * Real.cos (t*x)) := by
    have h1 : Continuous YcP := by unfold YcP; fun_prop
    have h2 : Continuous (fun x : ℝ => Real.cos (t*x)) := by fun_prop
    exact h1.mul h2
  have hF : ∀ x ∈ Set.uIcc (0:ℝ) (3/2), HasDerivAt (YcF t) (YcP x * Real.cos (t*x)) x :=
    fun x _ => hasDerivAt_YcF t ht x
  have hInt : IntervalIntegrable (fun x : ℝ => YcP x * Real.cos (t*x)) volume (0:ℝ) (3/2) :=
    hcont.intervalIntegrable 0 (3/2)
  have hFTC : (∫ x in (0:ℝ)..(3/2), YcP x * Real.cos (t*x)) = YcF t (3/2) - YcF t 0 :=
    integral_eq_sub_of_hasDerivAt (f := YcF t)
      (f' := fun y : ℝ => YcP y * Real.cos (t*y)) (a := (0:ℝ)) (b := 3/2) hF hInt
  rw [Yc_eq_integral t, hFTC]
  have hgoal : YcF t (3/2) - YcF t 0
      = -(64/45)/t^2 - (512/27)*(1 - Real.cos (t*(3/2)))/t^4
        - (8192/81)*Real.sin (t*(3/2))/t^5 - (16384/81)*Real.cos (t*(3/2))/t^6
        + (32768/243)*Real.sin (t*(3/2))/t^7 := by
    simp only [YcF, YcQ, YcR, YcQD, ycQ0, ycQ1, ycQ2, ycQ3, ycQ4, ycQ6,
      Real.sin_zero, Real.cos_zero, mul_zero, add_zero, zero_add]
    field_simp
    ring
  rw [hgoal]

/-! ### The trigonometric bound -/

lemma yc_cos_sin_le_sqrt (a b θ : ℝ) :
    a * Real.cos θ + b * Real.sin θ ≤ Real.sqrt (a^2 + b^2) := by
  by_cases h : 0 ≤ a * Real.cos θ + b * Real.sin θ
  · rw [Real.le_sqrt h (by positivity)]
    nlinarith [sq_nonneg (a * Real.sin θ - b * Real.cos θ), Real.cos_sq_add_sin_sq θ]
  · rw [not_le] at h
    exact le_trans h.le (Real.sqrt_nonneg _)

/-! ### The polynomial inequality -/

lemma yc_poly_key (w : ℝ) (hw : 9 ≤ w) :
    0 ≤ w^3*((64/45)*w + (512/27))^2 - w*((512/27)*w - (16384/81))^2
        - (-(8192/81)*w + (32768/243))^2 := by
  have hD : w^3*((64/45)*w + (512/27))^2 - w*((512/27)*w - (16384/81))^2
        - (-(8192/81)*w + (32768/243))^2
      = (4096/1476225)*(729*w^5 + 19440*w^4 - 921600*w^2 - 4915200*w - 6553600) := by
    ring
  rw [hD]
  have hw0 : (0:ℝ) ≤ w := by linarith
  have h2 : (81:ℝ) ≤ w^2 := by nlinarith [hw]
  have h3 : (729:ℝ) ≤ w^3 := by
    have hh : 0 ≤ w^2 * (w - 9) := mul_nonneg (sq_nonneg w) (by linarith)
    nlinarith [hh, h2]
  have hA : 0 ≤ 729*w^5 - 531441*w^2 := by
    have e : 729*w^5 - 531441*w^2 = 729*w^2*(w^3 - 729) := by ring
    rw [e]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg w)) (by linarith)
  have hB : 0 ≤ 19440*w^4 - 1574640*w^2 := by
    have e : 19440*w^4 - 1574640*w^2 = 19440*(w^2)*(w^2 - 81) := by ring
    rw [e]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg w)) (by linarith)
  have hC : 0 ≤ 1184481*w^2 - 4915200*w - 6553600 := by
    have e : 1184481*w^2 - 4915200*w - 6553600 = 1184481*w*(w-9) + (5745129*w - 6553600) := by ring
    rw [e]
    have h1 : 0 ≤ 1184481*w*(w-9) := by
      exact mul_nonneg (mul_nonneg (by norm_num) hw0) (by linarith)
    have h2' : 0 ≤ 5745129*w - 6553600 := by linarith
    linarith
  have hkey : 0 ≤ 729*w^5 + 19440*w^4 - 921600*w^2 - 4915200*w - 6553600 := by
    have hs : (729*w^5 - 531441*w^2) + (19440*w^4 - 1574640*w^2)
        + (1184481*w^2 - 4915200*w - 6553600)
        = 729*w^5 + 19440*w^4 - 921600*w^2 - 4915200*w - 6553600 := by ring
    have hsum : 0 ≤ (729*w^5 - 531441*w^2) + (19440*w^4 - 1574640*w^2)
        + (1184481*w^2 - 4915200*w - 6553600) := by linarith [hA, hB, hC]
    rw [hs] at hsum
    exact hsum
  exact mul_nonneg (by norm_num) hkey

lemma yc_sqrt_bound (t : ℝ) (ht : t ≠ 0) (hw : 9 ≤ t^2) :
    Real.sqrt (((512/27)/t^4 - (16384/81)/t^6)^2 + (-(8192/81)/t^5 + (32768/243)/t^7)^2)
      ≤ (64/45)/t^2 + (512/27)/t^4 := by
  have ht2 : (0:ℝ) < t^2 := sq_pos_of_ne_zero ht
  have ht14 : (0:ℝ) < t^14 := by
    have h : t^14 = (t^2)^7 := by
      rw [show (14:ℕ) = 2*7 by norm_num, pow_mul]
    rw [h]; exact pow_pos ht2 7
  have hy : 0 ≤ (64/45)/t^2 + (512/27)/t^4 := by positivity
  rw [Real.sqrt_le_left hy]
  have e1 : ((512/27)/t^4 - (16384/81)/t^6)^2 + (-(8192/81)/t^5 + (32768/243)/t^7)^2
      = (t^2*((512/27)*t^2 - (16384/81))^2 + (-(8192/81)*t^2 + (32768/243))^2)/t^14 := by
    first | (field_simp; ring) | (field_simp) | (ring_nf)
  have e2 : ((64/45)/t^2 + (512/27)/t^4)^2
      = ((t^2)^3*((64/45)*t^2 + (512/27))^2)/t^14 := by
    first | (field_simp; ring) | (field_simp) | (ring_nf)
  rw [e1, e2, div_le_div_iff_of_pos_right ht14]
  have hk := yc_poly_key (t^2) hw
  linarith

/-! ### The target -/

/-- `Yc t ≤ 0` for `|t| ≥ 3`.  Route: the exact integration-by-parts identity (three integrations by parts and the exact evaluation of `∫₀^{3/2} cos(tx)·(quadratic) dx`)
`Yc t = -(64/45)/t² - (512/27)(1-cos(3t/2))/t⁴ - (8192/81)sin(3t/2)/t⁵ - (16384/81)cos(3t/2)/t⁶ + (32768/243)sin(3t/2)/t⁷`
(at t ≠ 0), then `a cos θ + b sin θ ≤ √(a²+b²)` with `a = (512/27)/t⁴-(16384/81)/t⁶`, `b = -(8192/81)/t⁵+(32768/243)/t⁷`, reducing `Yc t ≤ 0` to the polynomial inequality `2.0227 w⁵+53.94 w⁴-2556.97 w²-13638.7 w-18183.9 ≥ 0` at `w = t² ≥ 9`. -/
theorem SupYcNonpos (t : ℝ) (h : 3 ≤ |t|) : Work.ZeroFreeTables.XY.Yc t ≤ 0 := by
  have ht0 : t ≠ 0 := by
    intro hh
    rw [hh] at h
    norm_num at h
  have hw9 : (9:ℝ) ≤ t^2 := by
    have h2 : |t|^2 = t^2 := sq_abs t
    nlinarith [abs_nonneg t, h]
  have htrig := yc_cos_sin_le_sqrt ((512/27)/t^4 - (16384/81)/t^6)
      (-(8192/81)/t^5 + (32768/243)/t^7) (t*(3/2))
  have hsqrt := yc_sqrt_bound t ht0 hw9
  have hmain : -(64/45)/t^2 - (512/27)*(1 - Real.cos (t*(3/2)))/t^4
        - (8192/81)*Real.sin (t*(3/2))/t^5 - (16384/81)*Real.cos (t*(3/2))/t^6
        + (32768/243)*Real.sin (t*(3/2))/t^7
      = -(64/45)/t^2 - (512/27)/t^4
        + (((512/27)/t^4 - (16384/81)/t^6) * Real.cos (t*(3/2))
           + (-(8192/81)/t^5 + (32768/243)/t^7) * Real.sin (t*(3/2))) := by
    field_simp
    ring
  have hX : ((512/27)/t^4 - (16384/81)/t^6) * Real.cos (t*(3/2))
      + (-(8192/81)/t^5 + (32768/243)/t^7) * Real.sin (t*(3/2))
      ≤ (64/45)/t^2 + (512/27)/t^4 := le_trans htrig hsqrt
  have hstep : -(64/45)/t^2 - (512/27)/t^4 + (((512/27)/t^4 - (16384/81)/t^6) * Real.cos (t*(3/2))
        + (-(8192/81)/t^5 + (32768/243)/t^7) * Real.sin (t*(3/2)))
      ≤ -(64/45)/t^2 - (512/27)/t^4 + ((64/45)/t^2 + (512/27)/t^4) :=
    add_le_add le_rfl hX
  have hzero : -(64/45)/t^2 - (512/27)/t^4 + ((64/45)/t^2 + (512/27)/t^4) = (0:ℝ) := by
    first | (field_simp; ring) | (ring_nf)
  rw [Yc_closed_form t ht0, hmain]
  exact le_trans hstep (le_of_eq hzero)

end Work.ZeroFreeTables.XY
