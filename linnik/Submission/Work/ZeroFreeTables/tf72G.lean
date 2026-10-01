/-
# ZeroFreeTables — `tf72G`: the closed form of the Laplace transform of HB's
test function of Lemma 7.2

Heath-Brown (1992), Lemma 7.2: the optimal test function `f = g ∗ g` of the
variational problem of §7 has Laplace transform `F z = ∫₀^{2/λ} e^{-zt} f(t) dt`.
The tables of §6/§8/§9 need `F` at *real* arguments other than the tabulated
`0` and `-λ`, and this module evaluates `F` in closed form at every `z ≠ 0`.

Writing `u = λ t` one has `F_λ z = G (z/λ)` with the λ-independent

  `G w = ∫₀² e^{-wu} P u du`,  `P u = (1/30)(2-u)³(4+6u+u²) = (1/30)(32 - 40u² + 20u³ - u⁵)`,

whose elementary closed form is

  `G w = tf72A w + e^{-2w} · tf72B w`,   `tf72A w = (1/30)(32/w - 80/w³ + 120/w⁴ - 120/w⁶)`,
  `tf72B w = (1/30)(120/w⁴ + 240/w⁵ + 120/w⁶) = 4(w+1)²/w⁶`                       (`w ≠ 0`).

The proof is the antiderivative `u ↦ e^{-wu} q_w(u)` with `q_w` the (unique)
degree-five polynomial solving `q_w' - w q_w = P`; in the original variable `t`
the same antiderivative is `t ↦ e^{-zt} tf72Q λ z t`, which is what
`tf72T_F_eq` uses.

Both `tf72A` and `tf72B` carry large denominators and cancel against each other
badly at small `|w|`, so the closed form is used only in *exact* rational
arithmetic: the certificate `lam0_cert_rows` is, per row, a rational inequality
in `tf72A (-a), tf72B (-a), tf72A (-b), tf72B (-b)` plus two decimal bounds
`α ≥ exp (2a)`, `β ≤ exp (2b)` obtained from Taylor polynomials for `exp`
(`exp_upper12`, `exp_lower12` below).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.tf72Tzero
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral

open scoped Real BigOperators
namespace Work.ZeroFreeTables
noncomputable section

/-! ## The closed form -/

/-- The non-exponential part `A w` of the closed form of `G`. -/
def tf72A (w : ℝ) : ℝ := (1/30)*(32/w - 80/w^3 + 120/w^4 - 120/w^6)

/-- The coefficient `B w` of the exponential part of the closed form of `G`. -/
def tf72B (w : ℝ) : ℝ := (1/30)*(120/w^4 + 240/w^5 + 120/w^6)

/-- The closed form of the Laplace transform, as a function of `w = z/λ`. -/
def G72r (w : ℝ) : ℝ := tf72A w + Real.exp (-2*w) * tf72B w

/-- `B` at a negative argument is a square: `B (-a) = 4(a-1)²/a⁶`. -/
lemma tf72B_neg_eq {a : ℝ} (ha : a ≠ 0) : tf72B (-a) = 4*(a-1)^2/a^6 := by
  unfold tf72B
  field_simp
  ring

/-- `tf72B` at a negative argument is non-negative. -/
lemma tf72B_neg_nonneg {a : ℝ} (ha : a ≠ 0) : 0 ≤ tf72B (-a) := by
  rw [tf72B_neg_eq ha]; positivity

/-- `tf72B` at a negative argument is positive unless `a = 1`. -/
lemma tf72B_neg_pos {a : ℝ} (ha : a ≠ 0) (h1 : a ≠ 1) : 0 < tf72B (-a) := by
  rw [tf72B_neg_eq ha]
  have : (a-1)^2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr h1)
  positivity

/-- `A` at a negative argument, with the signs made explicit. -/
lemma tf72A_neg {a : ℝ} (ha : a ≠ 0) :
    tf72A (-a) = (1/30)*(-32/a + 80/a^3 + 120/a^4 - 120/a^6) := by
  unfold tf72A
  field_simp
  ring

/-- `G` at a negative argument: `G (-a) = A (-a) + e^{2a} B (-a)`. -/
lemma G72_neg (a : ℝ) : G72r (-a) = tf72A (-a) + Real.exp (2*a) * tf72B (-a) := by
  unfold G72r
  rw [show -2*(-a) = 2*a by ring]

/-! ## The antiderivative -/

/-- Coefficients of the antiderivative polynomial `q_z` (see `tf72Q`): the
`t⁰` coefficient. -/
def tf72q0 (lam z : ℝ) : ℝ := 4*lam^6/z^6 - 4*lam^4/z^4 + 8*lam^3/(3*z^3) - 32*lam/(30*z)
/-- The `t¹` coefficient of `q_z`. -/
def tf72q1 (lam z : ℝ) : ℝ := 4*lam^6/z^5 - 4*lam^4/z^3 + 8*lam^3/(3*z^2)
/-- The `t²` coefficient of `q_z`. -/
def tf72q2 (lam z : ℝ) : ℝ := 2*lam^6/z^4 - 2*lam^4/z^2 + 4*lam^3/(3*z)
/-- The `t³` coefficient of `q_z`. -/
def tf72q3 (lam z : ℝ) : ℝ := 2*lam^6/(3*z^3) - 2*lam^4/(3*z)
/-- The `t⁴` coefficient of `q_z`. -/
def tf72q4 (lam z : ℝ) : ℝ := lam^6/(6*z^2)
/-- The `t⁵` coefficient of `q_z`. -/
def tf72q5 (lam z : ℝ) : ℝ := lam^6/(30*z)

/-- The antiderivative polynomial: `q_z'(t) - z q_z(t) = (λ/30)(2-λt)³(4+6λt+λ²t²)`,
so that `d/dt (e^{-zt} q_z(t)) = e^{-zt} f(t)` for HB's Lemma 7.2 test function.
Its value at `t = 0` is `-A (z/λ)` and at `t = 2/λ` it is `B (z/λ)`. -/
def tf72Qz (lam z t : ℝ) : ℝ :=
  tf72q0 lam z + tf72q1 lam z * t + tf72q2 lam z * t^2 + tf72q3 lam z * t^3
    + tf72q4 lam z * t^4 + tf72q5 lam z * t^5

lemma tf72Qz_eq_poly (lam z s : ℝ) :
    tf72Qz lam z s = tf72q0 lam z + tf72q1 lam z * s + tf72q2 lam z * s^2
      + tf72q3 lam z * s^3 + tf72q4 lam z * s^4 + tf72q5 lam z * s^5 := rfl

/-- Derivative of a degree-`5` polynomial. -/
lemma hasDerivAt_poly6 (c0 c1 c2 c3 c4 c5 t : ℝ) :
    HasDerivAt (fun s : ℝ => c0 + c1*s + c2*s^2 + c3*s^3 + c4*s^4 + c5*s^5)
      (c1 + c2*(2*t) + c3*(3*t^2) + c4*(4*t^3) + c5*(5*t^4)) t := by
  have h0 : HasDerivAt (fun _ : ℝ => c0) 0 t := hasDerivAt_const t c0
  have h1 : HasDerivAt (fun s : ℝ => c1*s) c1 t := by
    simpa using (hasDerivAt_id t).const_mul c1
  have h2 : HasDerivAt (fun s : ℝ => c2*s^2) (c2*(2*t)) t := by
    simpa using ((hasDerivAt_pow 2 t).const_mul c2)
  have h3 : HasDerivAt (fun s : ℝ => c3*s^3) (c3*(3*t^2)) t := by
    simpa using ((hasDerivAt_pow 3 t).const_mul c3)
  have h4 : HasDerivAt (fun s : ℝ => c4*s^4) (c4*(4*t^3)) t := by
    simpa using ((hasDerivAt_pow 4 t).const_mul c4)
  have h5 : HasDerivAt (fun s : ℝ => c5*s^5) (c5*(5*t^4)) t := by
    simpa using ((hasDerivAt_pow 5 t).const_mul c5)
  have h := ((((h0.add h1).add h2).add h3).add h4).add h5
  exact h.congr_deriv (by ring)

/-- Derivative of `e^{-zt}` times a degree-`5` polynomial. -/
lemma hasDerivAt_exp_poly6 (z c0 c1 c2 c3 c4 c5 t : ℝ) :
    HasDerivAt
      (fun s : ℝ => Real.exp (-(z*s)) * (c0 + c1*s + c2*s^2 + c3*s^3 + c4*s^4 + c5*s^5))
      (Real.exp (-(z*t)) * ((c1 + c2*(2*t) + c3*(3*t^2) + c4*(4*t^3) + c5*(5*t^4))
        - z*(c0 + c1*t + c2*t^2 + c3*t^3 + c4*t^4 + c5*t^5))) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-(z*s))) (Real.exp (-(z*t)) * (-z)) t := by
    have h4 : HasDerivAt (fun s : ℝ => (-z)*s) (-z) t := by
      simpa using (hasDerivAt_id t).const_mul (-z)
    have h2 : HasDerivAt (fun s : ℝ => -(z*s)) (-z) t := by
      rwa [show (fun s : ℝ => (-z)*s) = (fun s : ℝ => -(z*s)) from by funext s; ring] at h4
    simpa using h2.exp
  have hp := hasDerivAt_poly6 c0 c1 c2 c3 c4 c5 t
  have hm := he.mul hp
  refine hm.congr_deriv ?_
  ring

/-- The antiderivative of the integrand `e^{-zt}(λ/30)(2-λt)³(4+6λt+λ²t²)`. -/
lemma hasDerivAt_exp_tf72Qz (lam z t : ℝ) (hz : z ≠ 0) :
    HasDerivAt (fun s : ℝ => Real.exp (-(z*s)) * tf72Qz lam z s)
      (Real.exp (-(z*t)) * ((lam/30)*(2-lam*t)^3*(4+6*lam*t+lam^2*t^2))) t := by
  have hfun : tf72Qz lam z
      = fun s : ℝ => tf72q0 lam z + tf72q1 lam z * s + tf72q2 lam z * s^2
          + tf72q3 lam z * s^3 + tf72q4 lam z * s^4 + tf72q5 lam z * s^5 := by
    funext s; rw [tf72Qz_eq_poly]
  rw [hfun]
  refine (hasDerivAt_exp_poly6 z (tf72q0 lam z) (tf72q1 lam z) (tf72q2 lam z)
    (tf72q3 lam z) (tf72q4 lam z) (tf72q5 lam z) t).congr_deriv ?_
  unfold tf72q0 tf72q1 tf72q2 tf72q3 tf72q4 tf72q5
  field_simp
  ring

/-! ## The value of `F` in closed form -/

/-- **The closed form of the Laplace transform of HB Lemma 7.2's test function.**
For `lam > 0` and real `z ≠ 0`, `F_λ z = G (z/λ)`. -/
theorem tf72T_F_eq (lam : ℝ) (hlam : 0 < lam) (z : ℝ) (hz : z ≠ 0) :
    (tf72T lam hlam).F z = G72r (z/lam) := by
  have hX : (0:ℝ) < 2/lam := by positivity
  have hlamne : lam ≠ 0 := hlam.ne'
  have h1 : (tf72T lam hlam).F z
      = ∫ t in (0:ℝ)..(2/lam), Real.exp (-(z*t)) * tf72f lam t := by
    rw [TestFn_F_eq_integral]
    rfl
  have h2 : (∫ t in (0:ℝ)..(2/lam), Real.exp (-(z*t)) * tf72f lam t)
      = ∫ t in (0:ℝ)..(2/lam),
          Real.exp (-(z*t)) * ((lam/30)*(2-lam*t)^3*(4+6*lam*t+lam^2*t^2)) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hX.le] at ht
    rw [tf72f_eq_poly lam hlam t ht]
  rw [h1, h2]
  have hcont : ContinuousOn (fun s : ℝ => Real.exp (-(z*s)) * tf72Qz lam z s)
      (Set.Icc (0:ℝ) (2/lam)) :=
    Continuous.continuousOn (by unfold tf72Qz; fun_prop)
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) (2/lam),
      HasDerivAt (fun s : ℝ => Real.exp (-(z*s)) * tf72Qz lam z s)
        (Real.exp (-(z*x)) * ((lam/30)*(2-lam*x)^3*(4+6*lam*x+lam^2*x^2))) x :=
    fun x _ => hasDerivAt_exp_tf72Qz lam z x hz
  have hint : IntervalIntegrable
      (fun t : ℝ => Real.exp (-(z*t)) * ((lam/30)*(2-lam*t)^3*(4+6*lam*t+lam^2*t^2)))
      MeasureTheory.volume (0:ℝ) (2/lam) :=
    (by fun_prop : Continuous fun t : ℝ =>
      Real.exp (-(z*t)) * ((lam/30)*(2-lam*t)^3*(4+6*lam*t+lam^2*t^2))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hX.le hcont hderiv hint]
  rw [show -(z*0) = 0 by ring, Real.exp_zero, one_mul]
  rw [show -(z*(2/lam)) = -2*(z/lam) by ring]
  rw [show tf72Qz lam z (2/lam) = tf72q0 lam z + tf72q1 lam z * (2/lam)
      + tf72q2 lam z * (2/lam)^2 + tf72q3 lam z * (2/lam)^3 + tf72q4 lam z * (2/lam)^4
      + tf72q5 lam z * (2/lam)^5 from rfl]
  rw [show tf72Qz lam z 0 = tf72q0 lam z from by rw [tf72Qz_eq_poly]; ring]
  unfold G72r tf72A tf72B tf72q0 tf72q1 tf72q2 tf72q3 tf72q4 tf72q5
  field_simp
  ring

/-! ## Taylor bounds for `exp` at rational arguments -/

/-- Upper Taylor bound for `Real.exp` at `q ∈ [0,8]`: `12` terms at `q/8`, raised
to the `8`-th power. -/
lemma exp_upper12 (q hi : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 8)
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

/-- Lower Taylor bound for `Real.exp` at `q ∈ [0,8]`. -/
lemma exp_lower12 (q lo : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 8)
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

/-! ## The generic reduction of one `λ₀`-certificate row -/

/-- **One row of the `λ₀` table, reduced to rational arithmetic.**  With
`a = 20 λ₀/37` and `b = 20 (λ₀-λ₁)/37` (so that `G72r (-a)` is `F (-λ₀)` and
`G72r (-b)` is `F (λ₁-λ₀)` for `λ = 37/20`), two rational two-sided bounds
`α ≥ e^{2a}`, `β ≤ e^{2b}` and the *rational* inequality `hnum` (checked by
`norm_num`) give the certificate inequality.

NB: `G72r 0` is *not* `8/9` — the closed form has a pole at `w = 0`; the value
`F 0 = 8/9` is the separate lemma `tf72T_F_zero`. -/
theorem lam0_row_aux {a b α β : ℝ} (hB1 : 0 ≤ tf72B (-a)) (hB2 : 0 ≤ tf72B (-b))
    (hα : Real.exp (2 * a) ≤ α) (hβ : β ≤ Real.exp (2 * b))
    (hnum : 2 * (tf72A (-a) + α * tf72B (-a) - (tf72A (-b) + β * tf72B (-b)))
      < 8 / 9 - (148 / 75) * ((1 / 4 : ℝ) + 4 * (1 / 4000))) :
    2 * (G72r (-a) - G72r (-b)) < 8 / 9 - (148 / 75) * ((1 / 4 : ℝ) + 4 * (1 / 4000)) := by
  rw [G72_neg, G72_neg]
  have h1 : Real.exp (2*a) * tf72B (-a) ≤ α * tf72B (-a) := mul_le_mul_of_nonneg_right hα hB1
  have h2 : β * tf72B (-b) ≤ Real.exp (2*b) * tf72B (-b) := mul_le_mul_of_nonneg_right hβ hB2
  linarith


/-
## Recipe for the rows of `lam0_cert_rows`

`lam0_cert_rows` is the `∀ p ∈ [(λ₁,λ₀), …]` statement of the strict failure of
HB's §6 inequality at the fourteen tabulated pairs, for the Lemma 7.2 test
function with `λ = 37/20`:

  `2 * (F (-λ₀) - F (λ₁ - λ₀)) < F 0 - f 0 * (1/4 + 4/4000)`.

By `tf72T_F_eq` (above) `F z = G72r (z/(37/20))` for `z ≠ 0`, and `G72r (-a) = A (-a) + e^{2a} B (-a)`
(`G72_neg`).  For each row put

  `a = 20 λ₀/37`  (so `G72r (-a) = F (-λ₀)`),   `b = 20 (λ₀-λ₁)/37`  (so `G72r (-b) = F (λ₁-λ₀)`),

then `lam0_row_aux` reduces the row to the *rational* inequality `hnum`.  The
following table gives, for each row, the rationals `a, b`, a bound `α ≥ e^{2a}`
and a bound `β ≤ e^{2b}` that make `hnum` true (these are the decimal expansions
of `e^{2a}`/`e^{2b}` rounded outwards; the true margin `RHS - hnum` is listed;
`exp_upper12`/`exp_lower12` at these `α`, `β` have their hypotheses verified by
`norm_num [Finset.sum_range_succ]`):

| λ₁ | λ₀ | a | b | α | β | margin |
|----|----|---|---|---|---|---|
| 12/100 | 256/100 | 256/185 | 244/185 | 159198628841/10000000000 | 139829375209/10000000000 | 0.2008 |
| 14/100 | 239/100 | 239/185 | 45/37 | 66235839341/5000000000 | 711659089/62500000 | 0.1888 |
| 16/100 | 225/100 | 45/37 | 209/185 | 56932727121/5000000000 | 47889552591/5000000000 | 0.1768 |
| 18/100 | 212/100 | 212/185 | 194/185 | 49468188397/5000000000 | 40720644907/5000000000 | 0.1664 |
| 20/100 | 201/100 | 201/185 | 181/185 | 87843609263/10000000000 | 70763395177/10000000000 | 0.1558 |
| 25/100 | 177/100 | 177/185 | 152/185 | 67768575989/10000000000 | 12929790307/2500000000 | 0.1328 |
| 30/100 | 158/100 | 158/185 | 128/185 | 6898138961/1250000000 | 1994985143/500000000 | 0.1114 |
| 35/100 | 142/100 | 142/185 | 107/185 | 9283905557/2000000000 | 7949010763/2500000000 | 0.0920 |
| 40/100 | 129/100 | 129/185 | 89/185 | 40333391037/10000000000 | 26173494937/10000000000 | 0.0729 |
| 45/100 | 118/100 | 118/185 | 73/185 | 35811202687/10000000000 | 176128849/80000000 | 0.0544 |
| 50/100 | 108/100 | 108/185 | 58/185 | 32141648833/10000000000 | 18720367831/10000000000 | 0.0375 |
| 55/100 | 1 | 20/37 | 9/37 | 29478647099/10000000000 | 8132955591/5000000000 | 0.0198 |
| 60/100 | 92/100 | 92/185 | 32/185 | 27036280537/10000000000 | 441664443/312500000 | 0.0044 |
| 10/100 | 276/100 | 276/185 | 266/185 | 39524904399/2000000000 | 177374048063/10000000000 | 0.2141 |

The last row is the worked example `Submission.Work.ZeroFreeTables.lam0_row01`
(a good model to copy: same proof, other numbers).  Its text is:

```
import Submission.Work.ZeroFreeTables.tf72G

open scoped Real BigOperators
namespace Work.ZeroFreeTables
noncomputable section

theorem lam0_row01 :
    2 * ((tf72T (37/20) (by norm_num)).F (-(276/100))
          - (tf72T (37/20) (by norm_num)).F ((1/10) - (276/100)))
      < (tf72T (37/20) (by norm_num)).F 0
        - (tf72T (37/20) (by norm_num)).f 0 * ((1/4 : ℝ) + 4 * (1/4000)) := by
  have h1 : (tf72T (37/20) (by norm_num)).F (-(276/100)) = G72r (-(276/185)) := by
    rw [tf72T_F_eq (37/20) (by norm_num) (-(276/100)) (by norm_num)]
    norm_num
  have h2 : (tf72T (37/20) (by norm_num)).F ((1/10) - (276/100)) = G72r (-(266/185)) := by
    rw [tf72T_F_eq (37/20) (by norm_num) ((1/10) - (276/100)) (by norm_num)]
    norm_num
  rw [h1, h2, tf72T_F_zero (37/20) (by norm_num), tf72T_f_zero (37/20) (by norm_num)]
  have hR : (8:ℝ)/9 - (16*(37/20)/15) * ((1/4 : ℝ) + 4 * (1/4000))
      = 8/9 - (148/75) * ((1/4 : ℝ) + 4 * (1/4000)) := by norm_num
  rw [hR]
  refine lam0_row_aux (a := 276/185) (b := 266/185)
    (α := 39524904399/2000000000)
    (β := 177374048063/10000000000) ?_ ?_ ?_ ?_ ?_
  · rw [tf72B_neg_eq (by norm_num : (276/185 : ℝ) ≠ 0)]; positivity
  · rw [tf72B_neg_eq (by norm_num : (266/185 : ℝ) ≠ 0)]; positivity
  · exact exp_upper12 (2*(276/185)) (39524904399/2000000000)
      (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
  · exact exp_lower12 (2*(266/185)) (177374048063/10000000000)
      (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
      (by norm_num [Finset.sum_range_succ])
  · norm_num [tf72A, tf72B]

end
end Work.ZeroFreeTables
```

Row 13 (`λ₁ = 55/100`, `λ₀ = 1`) has `F (-(1))` and `F ((55/100) - (1))`; its
`b = 9/37` and `β = 8132955591/5000000000`.  Note `e^{2b}` for row 14 is only
about `1.4133` while `tf72B (-b) ≈ 102148`, so a *low-precision* bound `β` would
lose the row: the outward-rounded bounds above are the ones to use (they have
about `1e-10` of slack in the safe direction; the Taylor hypotheses of
`exp_upper12`/`exp_lower12` need slack of about `1e-12`, so do not tighten them).
-/

end
end Work.ZeroFreeTables
