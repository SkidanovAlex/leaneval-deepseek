import Mathlib

set_option linter.unusedVariables false

namespace Work.A7

/-!
# The elementary inequality `c • F₂K₂ ≤ bfun`

This is a purely real-variable inequality feeding into the Linnik assembly (`K = 3/10`).

For `x ≥ 0` one has the "core" inequality
`2 (1 - e^{-x})² ≤ (5/9) x (1 - e^{-2x}) + (1/2) (2x - 1 + e^{-2x})`,
which is equivalent (multiply by `18`) to the nonnegativity of
`φ(x) = 28x - 45 + 72 e^{-x} - (27 + 10x) e^{-2x}`.

Writing `u = e^{-x}` and using `φ(x) = 2x(14 - 5u²) - 9(5 - 3u)(1 - u)`, the required
lower bound on `x` is the classical logarithmic estimate `log u ≤ 2(u-1)/(u+1)`
for `u ≤ 1` (obtained here from `Real.le_log_one_add_of_nonneg`). Combined with
`u ≤ 1` this turns `φ ≥ 0` into the elementary fact `(1-u)²(11 - 7u) ≥ 0`.
-/

/-- The fractional bound `log t ≤ 2(t-1)/(t+1)` valid for `0 < t ≤ 1`. -/
private theorem log_le_two_mul_sub_div_add {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    Real.log t ≤ 2 * (t - 1) / (t + 1) := by
  have hy0 : 0 ≤ (1 - t) / t := by
    apply div_nonneg _ ht0.le; linarith
  have hlog := Real.le_log_one_add_of_nonneg hy0
  have h1 : 1 + (1 - t) / t = 1 / t := by field_simp; ring
  rw [h1, Real.log_div one_ne_zero ht0.ne', Real.log_one, zero_sub] at hlog
  have hA : (1 - t) / t + 2 = (1 + t) / t := by field_simp; ring
  have h2 : 2 * ((1 - t) / t) / ((1 - t) / t + 2) = -(2 * (t - 1) / (t + 1)) := by
    rw [hA]
    rw [show 2 * ((1 - t) / t) = 2 * (1 - t) / t from by ring]
    rw [div_div_div_cancel_right₀ ht0.ne']
    ring
  linarith [hlog, h2]

/-- The auxiliary function `φ(x) = 28x - 45 + 72 e^{-x} - (27 + 10x) e^{-2x}`. -/
private noncomputable def phi (x : ℝ) : ℝ :=
  28*x - 45 + 72*Real.exp (-x) - (27 + 10*x)*Real.exp (-(2*x))

private theorem exp_neg_two_mul (x : ℝ) : Real.exp (-(2*x)) = (Real.exp (-x))^2 := by
  rw [show -(2*x) = -x + -x from by ring, Real.exp_add, sq]

/-- `φ ≥ 0` on `[0, ∞)`. -/
private theorem phi_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ phi x := by
  set u : ℝ := Real.exp (-x) with hu
  have hu0 : 0 < u := by rw [hu]; exact Real.exp_pos (-x)
  have hu1 : u ≤ 1 := by rw [hu]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hu_sq : u ^ 2 = Real.exp (-(2*x)) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hphi : phi x = 2*x*(14 - 5*u^2) - 9*(5-3*u)*(1-u) := by
    rw [phi, ← hu, ← hu_sq]; ring
  rw [hphi]
  have hbound : 2 * (1 - u) / (1 + u) ≤ x := by
    have h := log_le_two_mul_sub_div_add hu0 hu1
    have hlogu : Real.log u = -x := by rw [hu, Real.log_exp]
    rw [hlogu] at h
    have he : -(2 * (u - 1) / (u + 1)) = 2 * (1 - u) / (1 + u) := by ring
    linarith [h, he]
  have hpos : 0 < 1 + u := by linarith [hu0]
  have hmul : 2*(1-u) ≤ x*(1+u) := by
    have hh := mul_le_mul_of_nonneg_right hbound hpos.le
    rwa [div_mul_cancel₀ _ hpos.ne'] at hh
  have hu2le : u^2 ≤ 1 := by
    nlinarith [mul_nonneg (by linarith [hu1] : (0:ℝ) ≤ 1-u) (by linarith [hu0] : (0:ℝ) ≤ 1+u)]
  have h14 : 0 ≤ 14 - 5*u^2 := by nlinarith [hu2le]
  have hp1 : 2*(1-u)*(14 - 5*u^2) ≤ x*(1+u)*(14 - 5*u^2) :=
    mul_le_mul_of_nonneg_right hmul h14
  have hmain : 0 ≤ 4*(1-u)*(14-5*u^2) - 9*(1+u)*(5-3*u)*(1-u) := by
    have hfac2 : 0 ≤ (1-u)^2*(11-7*u) := mul_nonneg (sq_nonneg _) (by linarith [hu1])
    have hident : 4*(1-u)*(14-5*u^2) - 9*(1+u)*(5-3*u)*(1-u) = (1-u)^2*(11-7*u) := by ring
    linarith [hfac2, hident]
  have hkey : 0 ≤ (2*x*(14-5*u^2) - 9*(5-3*u)*(1-u)) * (1+u) := by
    nlinarith [hp1, hmain]
  exact nonneg_of_mul_nonneg_left hkey hpos

/-- The "core" real inequality, valid for `x ≥ 0`. -/
private theorem core {x : ℝ} (hx : 0 ≤ x) :
    2 * (1 - Real.exp (-x)) ^ 2
      ≤ (5/9)*x*(1 - Real.exp (-(2*x))) + (1/2)*(2*x - 1 + Real.exp (-(2*x))) := by
  have hφ := phi_nonneg hx
  have hkey : 18 * ((5/9)*x*(1 - Real.exp (-(2*x))) + (1/2)*(2*x - 1 + Real.exp (-(2*x)))
      - 2*(1 - Real.exp (-x))^2) = phi x := by
    rw [phi, exp_neg_two_mul]; ring
  nlinarith [hφ, hkey]

theorem smul_F2K2_le_bfun {c p : ℝ} (hp : 0 < p) (hc0 : 0 ≤ c) (hc2 : c ≤ 2) :
    c * (((1 - Real.exp (-((3:ℝ)/10 * p))) / p) ^ 2 / ((9:ℝ)/100))
      ≤ (1 - Real.exp (-((3:ℝ)/5 * p)))/(6*((9:ℝ)/100)*p)
        + (2*((3:ℝ)/10)*p - 1 + Real.exp (-((3:ℝ)/5 * p)))/(2*((9:ℝ)/100)*p^2) := by
  set x : ℝ := (3:ℝ)/10 * p with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have h2x : 2*((3:ℝ)/10)*p = 2*x := by rw [hx]; ring
  rw [show -((3:ℝ)/10 * p) = -x from by rw [hx],
      show -((3:ℝ)/5 * p) = -(2*x) from by rw [hx]; ring,
      h2x]
  have hid1 : ((100:ℝ)/9)/p^2*(2*(1 - Real.exp (-x))^2)
      = 2*(((1 - Real.exp (-x))/p)^2/((9:ℝ)/100)) := by
    field_simp
  have hid2 : ((100:ℝ)/9)/p^2*((5/9)*x*(1 - Real.exp (-(2*x))) + (1/2)*(2*x - 1 + Real.exp (-(2*x))))
      = (1 - Real.exp (-(2*x)))/(6*((9:ℝ)/100)*p)
        + (2*x - 1 + Real.exp (-(2*x)))/(2*((9:ℝ)/100)*p^2) := by
    rw [hx]; field_simp; ring
  have hfac : 0 ≤ ((100:ℝ)/9)/p^2 := by positivity
  have hm := mul_le_mul_of_nonneg_left (core hx0) hfac
  rw [hid1, hid2] at hm
  have hM : 0 ≤ ((1 - Real.exp (-x))/p)^2/((9:ℝ)/100) := by positivity
  exact le_trans (mul_le_mul_of_nonneg_right hc2 hM) hm

end Work.A7
