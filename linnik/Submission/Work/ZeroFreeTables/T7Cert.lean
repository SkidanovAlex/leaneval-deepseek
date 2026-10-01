/-
# ZeroFreeTables — T7Cert

The analytic and numerical machinery for Heath-Brown's Table 7 certificates
(`table7_rows_cert`).

`tfShape`/`tfF` are defined in `HBTable7_defs`.  Here we

* evaluate `tfF`: `tfF lam 0 = (π/2 - 2)²` and `tfF lam (-m) = phiNeg (m/lam)`,
  where `phiNeg` is the explicit closed form obtained from the five elementary
  integrals of `exp`, `exp·cos`, `exp·sin`, `u·exp`, `u·exp·cos` over `[0, π/2]`;
* strip the denominators of `phiNeg` (`PhiS`/`PhiD`), reducing each Table 7 row to
  a *linear* inequality in the atoms `π/2`, `π-3`, `(π/2-2)²`,
  `exp((c/λ)(π/2))`, `exp(((c-b)/λ)(π/2))` (`CertRow_of_PhiS`);
* provide the two-sided rational Taylor bounds `exp_upper`, `exp_lower` on `Real.exp`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBTable7_defs

open scoped Real BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-! ## The closed form of `tfF` on negative arguments -/

/-- Clearing the denominators of `phiNeg`. -/
def PhiK (m : ℝ) : ℝ := -m^2*(1+m^2) + 2*m^3 + 2*m^3*(1+m^2) - 2*m*(1+m^2)^2 + (1+m^2)^2
def PhiA (m : ℝ) : ℝ := m*(1+m^2)*(1+2*m^2)
def PhiC (m : ℝ) : ℝ := m^3*(1+m^2) + (m^2 - m^4) + 2*m^2*(1+m^2) + 2*m*(1+m^2)^2 - (1+m^2)^2
def PhiD (m : ℝ) : ℝ := m^2*(1+m^2)^2
def PhiS (m : ℝ) : ℝ := Real.exp (m*(Real.pi/2))*PhiK m - (Real.pi/2)*PhiA m + PhiC m

/-- The closed form of `tfF lam (-m)` (valid for `m/lam ≠ 0`). -/
def phiNeg (m : ℝ) : ℝ :=
  2 * ((Real.pi/2 - 1) * ((Real.exp (m*(Real.pi/2)) - m)/(1+m^2))
     - ((Real.exp (m*(Real.pi/2)) * ((Real.pi/2)*(1+m^2) - 2*m))/(1+m^2)^2 - (1-m^2)/(1+m^2)^2)
     + 2 * ((1 + m*Real.exp (m*(Real.pi/2)))/(1+m^2))
     + (Real.pi/2 - 2) * ((Real.exp (m*(Real.pi/2)) - 1)/m)
     - ((1 - Real.exp (m*(Real.pi/2)))/m^2 + Real.exp (m*(Real.pi/2))*(Real.pi/2)/m))

/-! ## The five elementary integrals over `[0, π/2]` -/

private lemma ci {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    IntervalIntegrable f MeasureTheory.volume a b := hf.intervalIntegrable a b

lemma integral_exp_mul (w : ℝ) (hw : w ≠ 0) :
    ∫ u in (0:ℝ)..(Real.pi/2), Real.exp (w*u) = (Real.exp (w*(Real.pi/2)) - 1)/w := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (Real.pi/2),
      HasDerivAt (fun u : ℝ => Real.exp (w*u)/w) (Real.exp (w*x)) x := by
    intro x hx
    have h0 : HasDerivAt (fun u : ℝ => w * u) w x := by
      simpa using (hasDerivAt_id x).const_mul w
    have h1 := h0.exp
    refine (h1.div_const w).congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun u : ℝ => Real.exp (w*u)) MeasureTheory.volume (0:ℝ) (Real.pi/2) :=
    ci (by fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [mul_zero, Real.exp_zero, one_mul, mul_one, sub_self, zero_sub, zero_mul]
  field_simp
  try ring

lemma integral_u_exp_mul (w : ℝ) (hw : w ≠ 0) :
    ∫ u in (0:ℝ)..(Real.pi/2), u * Real.exp (w*u)
      = Real.exp (w*(Real.pi/2))*((Real.pi/2)/w - 1/w^2) + 1/w^2 := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (Real.pi/2),
      HasDerivAt (fun u : ℝ => Real.exp (w*u)*(u/w - 1/w^2)) (x * Real.exp (w*x)) x := by
    intro x hx
    have h0 : HasDerivAt (fun u : ℝ => w * u) w x := by
      simpa using (hasDerivAt_id x).const_mul w
    have h1 := h0.exp
    have h2 : HasDerivAt (fun u : ℝ => u/w - 1/w^2) (1/w) x := by
      simpa using ((hasDerivAt_id x).div_const w).sub_const (1/w^2)
    refine (h1.mul h2).congr_deriv ?_
    field_simp
    try ring
  have hint : IntervalIntegrable (fun u : ℝ => u * Real.exp (w*u)) MeasureTheory.volume (0:ℝ) (Real.pi/2) :=
    ci (by fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [mul_zero, Real.exp_zero, zero_div, sub_zero, mul_one, one_mul, zero_mul]
  field_simp
  try ring

lemma integral_exp_mul_cos (w : ℝ) :
    ∫ u in (0:ℝ)..(Real.pi/2), Real.exp (w*u) * Real.cos u
      = (Real.exp (w*(Real.pi/2)) - w)/(1+w^2) := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (Real.pi/2),
      HasDerivAt (fun u : ℝ => Real.exp (w*u) * (w * Real.cos u + Real.sin u) / (1+w^2))
        (Real.exp (w*x) * Real.cos x) x := by
    intro x hx
    have h0 : HasDerivAt (fun u : ℝ => w * u) w x := by
      simpa using (hasDerivAt_id x).const_mul w
    have h1 := h0.exp
    have h2 : HasDerivAt (fun u : ℝ => w * Real.cos u + Real.sin u) (w * (-Real.sin x) + Real.cos x) x :=
      ((Real.hasDerivAt_cos x).const_mul w).add (Real.hasDerivAt_sin x)
    refine ((h1.mul h2).div_const (1+w^2)).congr_deriv ?_
    have h3 : (1:ℝ)+w^2 ≠ 0 := by positivity
    field_simp
    try ring
  have hint : IntervalIntegrable (fun u : ℝ => Real.exp (w*u) * Real.cos u) MeasureTheory.volume (0:ℝ) (Real.pi/2) :=
    ci (by fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero, mul_one, mul_zero,
    Real.exp_zero, one_mul]
  field_simp
  try ring

lemma integral_exp_mul_sin (w : ℝ) :
    ∫ u in (0:ℝ)..(Real.pi/2), Real.exp (w*u) * Real.sin u
      = (w * Real.exp (w*(Real.pi/2)) + 1)/(1+w^2) := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (Real.pi/2),
      HasDerivAt (fun u : ℝ => Real.exp (w*u) * (w * Real.sin u - Real.cos u) / (1+w^2))
        (Real.exp (w*x) * Real.sin x) x := by
    intro x hx
    have h0 : HasDerivAt (fun u : ℝ => w * u) w x := by
      simpa using (hasDerivAt_id x).const_mul w
    have h1 := h0.exp
    have h2 : HasDerivAt (fun u : ℝ => w * Real.sin u - Real.cos u) (w * Real.cos x - (-Real.sin x)) x :=
      ((Real.hasDerivAt_sin x).const_mul w).sub (Real.hasDerivAt_cos x)
    refine ((h1.mul h2).div_const (1+w^2)).congr_deriv ?_
    have h3 : (1:ℝ)+w^2 ≠ 0 := by positivity
    field_simp
    try ring
  have hint : IntervalIntegrable (fun u : ℝ => Real.exp (w*u) * Real.sin u) MeasureTheory.volume (0:ℝ) (Real.pi/2) :=
    ci (by fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero, mul_one, mul_zero,
    sub_zero, zero_sub, Real.exp_zero, one_mul]
  field_simp
  try ring

lemma integral_u_exp_mul_cos (w : ℝ) :
    ∫ u in (0:ℝ)..(Real.pi/2), u * Real.exp (w*u) * Real.cos u
      = Real.exp (w*(Real.pi/2))*((Real.pi/2)*(1+w^2) - 2*w)/(1+w^2)^2 + (w^2-1)/(1+w^2)^2 := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (Real.pi/2),
      HasDerivAt (fun u : ℝ => u * (Real.exp (w*u) * (w * Real.cos u + Real.sin u) / (1+w^2))
          - Real.exp (w*u)*((w^2-1)*Real.cos u + 2*w*Real.sin u)/(1+w^2)^2)
        (x * Real.exp (w*x) * Real.cos x) x := by
    intro x hx
    have h0 : HasDerivAt (fun u : ℝ => w * u) w x := by
      simpa using (hasDerivAt_id x).const_mul w
    have h1 := h0.exp
    have h2 : HasDerivAt (fun u : ℝ => w * Real.cos u + Real.sin u) (w * (-Real.sin x) + Real.cos x) x :=
      ((Real.hasDerivAt_cos x).const_mul w).add (Real.hasDerivAt_sin x)
    have h3 : HasDerivAt (fun u : ℝ => Real.exp (w*u) * (w * Real.cos u + Real.sin u) / (1+w^2))
        (Real.exp (w*x) * Real.cos x) x := by
      refine ((h1.mul h2).div_const (1+w^2)).congr_deriv ?_
      have h4 : (1:ℝ)+w^2 ≠ 0 := by positivity
      field_simp
      ring
    have h4 : HasDerivAt (fun u : ℝ => (w^2-1)*Real.cos u + 2*w*Real.sin u)
        ((w^2-1)*(-Real.sin x) + 2*w*Real.cos x) x :=
      (((Real.hasDerivAt_cos x).const_mul (w^2-1)).add ((Real.hasDerivAt_sin x).const_mul (2*w)))
    have h5 : HasDerivAt
        (fun u : ℝ => Real.exp (w*u)*((w^2-1)*Real.cos u + 2*w*Real.sin u)/(1+w^2)^2)
        ((Real.exp (w*x)*w * ((w^2-1)*Real.cos x + 2*w*Real.sin x)
          + Real.exp (w*x)*((w^2-1)*(-Real.sin x) + 2*w*Real.cos x))/(1+w^2)^2) x :=
      (h1.mul h4).div_const ((1+w^2)^2)
    have hid : HasDerivAt (fun u : ℝ => u) 1 x := hasDerivAt_id x
    refine ((hid.mul h3).sub h5).congr_deriv ?_
    have h6 : (1:ℝ)+w^2 ≠ 0 := by positivity
    field_simp
    try ring
  have hint : IntervalIntegrable (fun u : ℝ => u * Real.exp (w*u) * Real.cos u) MeasureTheory.volume (0:ℝ) (Real.pi/2) :=
    ci (by fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero, mul_one, mul_zero,
    add_zero, zero_mul, sub_zero, mul_eq_zero, Real.exp_zero, id_eq, one_mul]
  field_simp
  try ring

/-! ## `tfF` at its arguments -/

/-- The value of `tfF` at `0` (independent of the parameter). -/
lemma integral_tfShape_zero : ∫ u in (0:ℝ)..(Real.pi/2), tfShape u = (Real.pi/2 - 2)^2 := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (Real.pi/2),
      HasDerivAt (fun u : ℝ => 2*((Real.pi/2 - 1)*Real.sin u - (Real.cos u + u*Real.sin u)
          + 2*(-Real.cos u) + (Real.pi/2 - 2)*u - u^2/2)) (tfShape x) x := by
    intro x hx
    have hs : HasDerivAt Real.sin (Real.cos x) x := Real.hasDerivAt_sin x
    have hc : HasDerivAt Real.cos (-Real.sin x) x := Real.hasDerivAt_cos x
    have hid : HasDerivAt (fun u : ℝ => u) 1 x := hasDerivAt_id x
    have h1 : HasDerivAt (fun u : ℝ => (Real.pi/2 - 1)*Real.sin u) ((Real.pi/2-1)*Real.cos x) x :=
      hs.const_mul _
    have h3 : HasDerivAt (fun u : ℝ => u*Real.sin u) (1*Real.sin x + x*Real.cos x) x := hid.mul hs
    have h4 : HasDerivAt (fun u : ℝ => Real.cos u + u*Real.sin u)
        (-Real.sin x + (1*Real.sin x + x*Real.cos x)) x := hc.add h3
    have h5 : HasDerivAt (fun u : ℝ => -Real.cos u) (-(-Real.sin x)) x := hc.neg
    have h6 : HasDerivAt (fun u : ℝ => 2*(-Real.cos u)) (2*(-(-Real.sin x))) x := h5.const_mul 2
    have h7 : HasDerivAt (fun u : ℝ => (Real.pi/2 - 2)*u) ((Real.pi/2-2)*1) x := hid.const_mul _
    have h8 : HasDerivAt (fun u : ℝ => u^2/2) x x := by
      have := ((hasDerivAt_id x).pow 2).div_const 2
      simpa using this
    have h9 : HasDerivAt (fun u : ℝ => ((Real.pi/2 - 1)*Real.sin u - (Real.cos u + u*Real.sin u))
        + 2*(-Real.cos u) + (Real.pi/2 - 2)*u - u^2/2)
        ((((Real.pi/2-1)*Real.cos x) - (-Real.sin x + (1*Real.sin x + x*Real.cos x))) + (2*(-(-Real.sin x)))
          + ((Real.pi/2-2)*1) - x) x := ((h1.sub h4).add h6).add h7 |>.sub h8
    refine (h9.const_mul 2).congr_deriv ?_
    unfold tfShape
    ring
  have hint : IntervalIntegrable tfShape MeasureTheory.volume (0:ℝ) (Real.pi/2) :=
    ci (by unfold tfShape; fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero, mul_one, mul_zero,
    add_zero, zero_mul, zero_div, sub_zero, mul_neg, neg_zero, sub_neg_eq_add, one_mul]
  ring

theorem tfF_zero (lam : ℝ) : tfF lam 0 = (Real.pi/2 - 2)^2 := by
  unfold tfF
  have h : (fun u : ℝ => Real.exp (-(0/lam)*u) * tfShape u) = tfShape := by
    funext u; simp
  rw [h]
  exact integral_tfShape_zero

/-- The closed form of `tfF` on negative arguments. -/
theorem tfF_neg (lam m : ℝ) (hl : lam ≠ 0) (hm : m ≠ 0) : tfF lam (-m) = phiNeg (m/lam) := by
  have hw : m/lam ≠ 0 := div_ne_zero hm hl
  have key : ∫ u in (0:ℝ)..(Real.pi/2), Real.exp ((m/lam)*u) * tfShape u = phiNeg (m/lam) := by
    rw [show (fun u : ℝ => Real.exp ((m/lam)*u) * tfShape u)
        = (fun u : ℝ => 2 * ((Real.pi/2-1)*(Real.exp ((m/lam)*u)*Real.cos u)
            - u*Real.exp ((m/lam)*u)*Real.cos u + 2*(Real.exp ((m/lam)*u)*Real.sin u)
            + (Real.pi/2-2)*Real.exp ((m/lam)*u) - u*Real.exp ((m/lam)*u))) from by
      funext u; unfold tfShape; ring]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_sub (ci (by fun_prop) _ _) (ci (by fun_prop) _ _)]
    rw [intervalIntegral.integral_add (ci (by fun_prop) _ _) (ci (by fun_prop) _ _)]
    rw [intervalIntegral.integral_add (ci (by fun_prop) _ _) (ci (by fun_prop) _ _)]
    rw [intervalIntegral.integral_sub (ci (by fun_prop) _ _) (ci (by fun_prop) _ _)]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    rw [integral_exp_mul_cos, integral_exp_mul_sin, integral_exp_mul _ hw,
        integral_u_exp_mul _ hw, integral_u_exp_mul_cos]
    unfold phiNeg
    field_simp
    try ring
  unfold tfF
  have harg : ∀ u : ℝ, -((-m)/lam)*u = (m/lam)*u := by
    intro u; field_simp; try ring
  simp only [harg]
  exact key

/-! ## Algebra: clearing the denominators of `phiNeg` -/

lemma phiNeg_eq {m : ℝ} (hm : m ≠ 0) : phiNeg m = 2*PhiS m/PhiD m := by
  unfold phiNeg PhiS PhiK PhiA PhiC PhiD
  have h1 : (1:ℝ)+m^2 ≠ 0 := by positivity
  field_simp
  try ring

/-! ## Reduction of a row to a linear inequality -/

/-- A Table 7 row with `b < c` reduces to a linear inequality in
`π/2`, `π-3`, `(π/2-2)²` and the two exponentials. -/
lemma CertRow_of_PhiS {b c k l : ℝ} (hk : 0 ≤ k) (hl : 0 < l) (hbc : b < c) (hb0 : 0 ≤ b)
    (h : (k^2+1/2)*(PhiS (c/l) * PhiD ((c-b)/l) - PhiS ((c-b)/l) * PhiD (c/l))
        - k * (PhiD (c/l) * PhiD ((c-b)/l)) * (Real.pi/2 - 2)^2
        + l * (Real.pi - 3) * psi87 k * (PhiD (c/l) * PhiD ((c-b)/l)) < 0) :
    CertRow b c k l 0 := by
  have hc : 0 < c := by linarith
  have hlne : l ≠ 0 := ne_of_gt hl
  have hm1 : c/l ≠ 0 := div_ne_zero (ne_of_gt hc) hlne
  have hcb : 0 < c-b := by linarith
  have hm2 : (c-b)/l ≠ 0 := div_ne_zero (ne_of_gt hcb) hlne
  have hbc' : b - c = -(c-b) := by ring
  unfold CertRow
  refine ⟨hl, hk, ?_⟩
  rw [tfF_neg l c hlne (ne_of_gt hc), hbc', tfF_neg l (c-b) hlne (ne_of_gt hcb), tfF_zero,
      phiNeg_eq hm1, phiNeg_eq hm2]
  simp only [tfSlack, mul_zero, add_zero]
  have hD1 : PhiD (c/l) ≠ 0 := by unfold PhiD; positivity
  have hD2 : PhiD ((c-b)/l) ≠ 0 := by unfold PhiD; positivity
  have hr : 0 < PhiD (c/l)*PhiD ((c-b)/l)/2 := by unfold PhiD; positivity
  have hprod : ((k^2+1/2)*(2*PhiS (c/l)/PhiD (c/l) - 2*PhiS ((c-b)/l)/PhiD ((c-b)/l))
      - 2*k*(Real.pi/2-2)^2 + 2*l*(Real.pi-3)*psi87 k) * (PhiD (c/l)*PhiD ((c-b)/l)/2) < 0 := by
    convert h using 1
    field_simp
    try ring
  by_contra hcon
  push_neg at hcon
  have h2 := mul_nonneg hcon (le_of_lt hr)
  linarith

/-- The diagonal Table 7 row (`b = c`): `tfF l (b-c) = tfF l 0`. -/
lemma CertRow_eq_of_PhiS {c k l : ℝ} (hk : 0 ≤ k) (hl : 0 < l) (hc : 0 < c)
    (h : (k^2+1/2)*(PhiS (c/l) - PhiD (c/l)*(Real.pi/2 - 2)^2/2)
        - k*PhiD (c/l)*(Real.pi/2 - 2)^2
        + l*(Real.pi - 3)*psi87 k*PhiD (c/l) < 0) :
    CertRow c c k l 0 := by
  have hlne : l ≠ 0 := ne_of_gt hl
  have hm1 : c/l ≠ 0 := div_ne_zero (ne_of_gt hc) hlne
  unfold CertRow
  refine ⟨hl, hk, ?_⟩
  rw [show c - c = (0:ℝ) by ring, tfF_neg l c hlne (ne_of_gt hc), tfF_zero, phiNeg_eq hm1]
  simp only [tfSlack, mul_zero, add_zero]
  have hD1 : PhiD (c/l) ≠ 0 := by unfold PhiD; positivity
  have hr : 0 < PhiD (c/l)/2 := by unfold PhiD; positivity
  have hprod : ((k^2+1/2)*(2*PhiS (c/l)/PhiD (c/l) - (Real.pi/2-2)^2)
      - 2*k*(Real.pi/2-2)^2 + 2*l*(Real.pi-3)*psi87 k) * (PhiD (c/l)/2) < 0 := by
    convert h using 1
    field_simp
    try ring
  by_contra hcon
  push_neg at hcon
  have h2 := mul_nonneg hcon (le_of_lt hr)
  linarith

/-! ## Rational bounds on `π` and the exponential atoms -/

lemma pi_div_two_bounds :
    (157079632679489661922/100000000000000000000 : ℝ) < Real.pi/2 ∧
    Real.pi/2 < (157079632679489661924/100000000000000000000 : ℝ) := by
  constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]

lemma pi_sub_three_bounds :
    (14159265358979323846/100000000000000000000 : ℝ) < Real.pi - 3 ∧
    Real.pi - 3 < (14159265358979323847/100000000000000000000 : ℝ) := by
  constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]

lemma s_bounds :
    (18421579/100000000 : ℝ) < (Real.pi/2 - 2)^2 ∧
    (Real.pi/2 - 2)^2 < (18421580/100000000 : ℝ) := by
  constructor <;> nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

/-- Two-sided upper Taylor bound for `Real.exp` (12 terms at `q/8`, raised to the 8th). -/
lemma exp_upper (q hi : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 8)
    (h : ((∑ m ∈ Finset.range 12, (q/8)^m/(Nat.factorial m : ℝ))
        + (q/8)^12 * ((12:ℝ)+1)/((Nat.factorial 12 : ℝ) * (12:ℝ)))^8 ≤ hi) :
    Real.exp q ≤ hi := by
  have hb := Real.exp_bound' (x := q/8) (n := 12) (show (0:ℝ) ≤ q/8 by positivity)
    (show q/8 ≤ 1 by linarith) (by norm_num)
  have key2 : (q/8)^12 * (↑(12:ℕ) + 1) / (↑(Nat.factorial 12) * ↑(12:ℕ))
      = (q/8)^12 * ((12:ℝ)+1)/((Nat.factorial 12 : ℝ) * (12:ℝ)) := by norm_num
  rw [key2] at hb
  have h2 : Real.exp q = Real.exp (q/8)^8 := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [h2]
  exact le_trans (pow_le_pow_left₀ (Real.exp_pos _).le hb 8) h

/-- Two-sided lower Taylor bound for `Real.exp`. -/
lemma exp_lower (q lo : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 8)
    (hpos : 0 ≤ (∑ m ∈ Finset.range 12, (q/8)^m/(Nat.factorial m : ℝ))
        - (q/8)^12 * ((12:ℝ)+1)/((Nat.factorial 12 : ℝ) * (12:ℝ)))
    (h : lo ≤ ((∑ m ∈ Finset.range 12, (q/8)^m/(Nat.factorial m : ℝ))
        - (q/8)^12 * ((12:ℝ)+1)/((Nat.factorial 12 : ℝ) * (12:ℝ)))^8) :
    lo ≤ Real.exp q := by
  have hb := Real.exp_bound (x := q/8) (n := 12)
    (show |q/8| ≤ 1 by rw [abs_of_nonneg (by positivity)]; linarith) (by norm_num)
  have key2 : |q/8| ^ 12 * (↑(Nat.succ 12) / (↑(Nat.factorial 12) * ↑(12:ℕ)))
      = (q/8)^12 * ((12:ℝ)+1)/((Nat.factorial 12 : ℝ) * (12:ℝ)) := by
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ q/8)]
    rw [mul_div_assoc]
    norm_num
  rw [key2] at hb
  have h2 : (∑ m ∈ Finset.range 12, (q/8)^m/(Nat.factorial m : ℝ))
      - (q/8)^12 * ((12:ℝ)+1)/((Nat.factorial 12 : ℝ) * (12:ℝ)) ≤ Real.exp (q/8) := by
    have := (abs_le.mp hb).1; linarith
  have h3 : Real.exp q = Real.exp (q/8)^8 := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [h3]
  exact le_trans h (pow_le_pow_left₀ hpos h2 8)


/-
## Recipe for a Table 7 row (`T7Row01` … `T7Row17`)

Every row is proved by exactly the same three steps; see
`Submission/Work/ZeroFreeTables/T7Row01.lean` for the complete worked example
(`CertRow (10/100) (276/100) (965/1000) (9758/10000) 0`) and `T7Row17.lean` for
the diagonal case (`b = c`, use `CertRow_eq_of_PhiS` instead of
`CertRow_of_PhiS`).

1. `apply CertRow_of_PhiS (by norm_num) (by norm_num) (by norm_num) (by norm_num)`
   (for `b = c`: `apply CertRow_eq_of_PhiS (by norm_num) (by norm_num) (by norm_num)`).
   This leaves the *linear* inequality in the atoms `Real.pi/2`, `Real.pi - 3`,
   `(Real.pi/2 - 2)^2`, `Real.exp ((c/λ)*(π/2))`, `Real.exp (((c-b)/λ)*(π/2))`.
2. Supply the interval bounds:
   * `pi_div_two_bounds`, `pi_sub_three_bounds`, `s_bounds` (constants, above);
   * `q1lo ≤ (c/λ)*(π/2) ≤ q1hi` etc. by `nlinarith [Real.pi_gt_d20]` /
     `nlinarith [Real.pi_lt_d20]` (with `c/λ`, `(c-b)/λ` written as the reduced
     fractions below);
   * `lo ≤ Real.exp (m*(π/2))` from `exp_lower q m lo hq0 hq hpos h` composed with
     `Real.exp_le_exp.mpr hq`, and `Real.exp (m*(π/2)) ≤ hi` from
     `Real.exp_le_exp.mpr hq` composed with `exp_upper q hi hq0 hq h`.
     Here `q` is a *rational numeral* so that the hypotheses of `exp_lower` /
     `exp_upper` close by `norm_num [Finset.sum_range_succ]`.
3. `unfold PhiS PhiK PhiA PhiC PhiD psi87; norm_num; linarith`.

### Data (b, c, k, λ and the rational bounds; π-bounds abbreviated)

`Pl = 157079632679489661922/10^20`, `Ph = 157079632679489661924/10^20` for `π/2`;
`π-3` bounds `(14159265358979323846/10^20, 14159265358979323847/10^20)`;
`(π/2-2)^2` bounds `(18421579/10^8, 18421580/10^8)`.

| row | b | c | k | λ | m1 | q1lo | q1hi | lo1 | hi1 | m2 | q2lo | q2hi | lo2 | hi2 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 02 | 12/100 | 256/100 | 962/1000 | 9624/10000 | 3200/1203 | 208917217/50000000 | 83566887/20000000 | 815721489/12500000 | 3262885989/50000000 | 3050/1203 | 79649689/20000000 | 199124223/50000000 | 670626999/12500000 | 5365016047/100000000 |
| 03 | 14/100 | 239/100 | 959/1000 | 9497/10000 | 23900/9497 | 395304119/100000000 | 9882603/2500000 | 651169407/12500000 | 5209355309/100000000 | 22500/9497 | 372148229/100000000 | 37214823/10000000 | 2066280263/50000000 | 516570071/12500000 |
| 04 | 16/100 | 225/100 | 956/1000 | 9395/10000 | 4500/1879 | 188094291/50000000 | 376188583/100000000 | 4302949539/100000000 | 4302949583/100000000 | 4180/1879 | 174718697/50000000 | 69887479/20000000 | 658593311/20000000 | 3292966589/100000000 |
| 05 | 18/100 | 212/100 | 953/1000 | 9281/10000 | 21200/9281 | 44850881/12500000 | 358807049/100000000 | 723284579/20000000 | 3616422933/100000000 | 19400/9281 | 164171149/50000000 | 328342299/100000000 | 266668969/10000000 | 1333344859/50000000 |
| 06 | 20/100 | 201/100 | 950/1000 | 9187/10000 | 20100/9187 | 34367047/10000000 | 343670471/100000000 | 777108923/25000000 | 777108931/25000000 | 18100/9187 | 77368601/25000000 | 61894881/20000000 | 2208158581/100000000 | 552039651/25000000 |
| 07 | 25/100 | 177/100 | 9425/10000 | 8942/10000 | 8850/4471 | 310927029/100000000 | 31092703/10000000 | 44809379/2000000 | 1120234487/50000000 | 7600/4471 | 133505391/50000000 | 267010783/100000000 | 1444152619/100000000 | 722076317/50000000 |
| 08 | 30/100 | 158/100 | 935/1000 | 8725/10000 | 632/349 | 284453661/100000000 | 142226831/50000000 | 429839737/25000000 | 859679483/50000000 | 512/349 | 14402717/6250000 | 230443473/100000000 | 500925669/50000000 | 1001851349/100000000 |
| 09 | 35/100 | 142/100 | 9275/10000 | 8514/10000 | 7100/4257 | 261983883/100000000 | 65495971/25000000 | 1373350997/100000000 | 343337753/25000000 | 5350/4257 | 197410391/100000000 | 24676299/12500000 | 180004119/25000000 | 180004121/25000000 |
| 10 | 40/100 | 129/100 | 92/100 | 8331/10000 | 4300/2777 | 1945819/800000 | 15201711/6250000 | 71154617/6250000 | 284618471/25000000 | 8900/8331 | 167808033/100000000 | 83904017/50000000 | 21421063/4000000 | 535526581/100000000 |
| 11 | 45/100 | 118/100 | 9125/10000 | 8164/10000 | 2950/2041 | 9081527/4000000 | 7094943/3125000 | 968309663/100000000 | 968309673/100000000 | 1825/2041 | 7022791/5000000 | 140455821/100000000 | 407372657/100000000 | 203686331/50000000 |
| 12 | 50/100 | 108/100 | 905/1000 | 7988/10000 | 2700/1997 | 53094017/25000000 | 212376069/100000000 | 836252721/100000000 | 83625273/10000000 | 1450/1997 | 57026907/50000000 | 22810763/20000000 | 62569029/20000000 | 312845149/100000000 |
| 13 | 55/100 | 100/100 | 8975/10000 | 7848/10000 | 1250/981 | 200152437/100000000 | 100076219/50000000 | 370016417/50000000 | 370016421/50000000 | 125/218 | 22517149/25000000 | 90068597/100000000 | 246129087/100000000 | 246129091/100000000 |
| 14 | 60/100 | 92/100 | 89/100 | 7677/10000 | 9200/7677 | 188241841/100000000 | 94120921/50000000 | 65693731/10000000 | 656937317/100000000 | 3200/7677 | 65475423/100000000 | 2046107/3125000 | 192466943/100000000 | 96233473/50000000 |
| 15 | 65/100 | 85/100 | 8825/10000 | 7516/10000 | 2125/1879 | 2775697/1562500 | 177644609/100000000 | 295440979/50000000 | 118176393/20000000 | 500/1879 | 41798731/100000000 | 10449683/25000000 | 151890139/100000000 | 75945071/50000000 |
| 16 | 70/100 | 79/100 | 875/1000 | 7371/10000 | 7900/7371 | 84176441/50000000 | 168352883/100000000 | 538452349/100000000 | 134613089/25000000 | 100/819 | 9589721/50000000 | 19179443/100000000 | 946423/781250 | 60571073/50000000 |

(For every row `λ ≠ 0`, so `m1 = c/λ`, `m2 = (c-b)/λ` are the reduced fractions
shown; the `q`-bounds are the interval `(m·(π/2) rounded down/up to 8 decimals)`,
the `lo`/`hi` are 8-decimal rationals enclosing `exp` of those.)

Row `01` is `T7Row01.lean`, row `17` is `T7Row17.lean` (diagonal, `b = c = 745/1000`,
`k = 8682/10000`, `λ = 726/1000`, `m1 = 745/726`, `q1lo = 40297633/25000000`,
`q1hi = 161190533/100000000`, `lo1 = 501235227/100000000`, `hi1 = 501235233/100000000`).
-/

end Work.ZeroFreeTables
