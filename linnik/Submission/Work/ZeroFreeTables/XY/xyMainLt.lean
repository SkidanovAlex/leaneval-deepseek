/-
# ZeroFreeTables — xyMainLt

**The numerical core of the order-2 `λ₁`-estimate** (Xylouris's `λ₁`-estimate in the
`ord χ₁ = 2` case, HB (9.16) at `λ* = 1`): for every `λ₁ ≤ 0.628`,

  `xyMain λ₁ + 240 = 14379·F(-1) - 24480·F(λ₁-1) + 3810·f(0) + 240 < 0`

for HB Lemma 7.2's test function with `λ = 4/3` (the `TestFn` `xyT`), i.e. the
`F`-method inequality of HB §9 is violated at `β = β*`, which is what forces
`λ₁ > 0.628`.

## Argument

`xyF` is antitone (`TestFn_F_antitone`), so `λ₁ ≤ 628/1000` gives
`λ₁ - 1 ≤ -372/1000` and hence `F(λ₁-1) ≥ F(-372/1000)`; with `f 0 = 64/45`
(`tf72f_at_zero`) it therefore suffices to bound

* `F(-1) ≤ 13616/10000`  (an *upper* bound: the hardest side), and
* `F(-372/1000) ≥ 10314/10000`,

since `14379·(13616/10000) - 24480·(10314/10000) + 3810·(64/45) + 240 = -11.5589 < 0`.

Both are obtained from `TestFn_F_eq_integral` (which identifies `F x` with
`∫_0^{3/2} e^{-xt} f(t) dt`) and `tf72f_eq_poly`, which gives the *polynomial*

  `xyP t = 64/45 - 256/81·t² + 512/243·t³ - 2048/10935·t⁵`
  `      = (λ/30)(2-λt)³(4+6λt+λ²t²)`  (λ = 4/3)

for `f` on its support `[0,3/2]`, together with Taylor bounds for `exp` on `[0,3/2]`:

* for the upper bound at `x = -1`: `e^t ≤ Σ_{j<13} t^j/j! + 2 t^13/13!`, so that
  `F(-1) ≤ Σ_{j<13} xyM j/j! + 2·xyM 13/13! = 1.3613849… ≤ 1.3616`
  (the `t^13` tail is invisible because `xyP` vanishes to third order at `3/2`);
* for the lower bound at `x = -372/1000`: `e^{0.372 t} ≥ Σ_{j<13} (0.372 t)^j/j!`, so that
  `F(-372/1000) ≥ Σ_{j<13} (0.372)^j·xyM j/j! = 1.0315946… ≥ 1.0314`.

Here `xyM j = ∫_0^{3/2} t^j xyP t` (`xyPolyDefs`, `xyP_moment`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XYDefs
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.TestFn_F_antitone
import Submission.Work.ZeroFreeTables.XY.xyPolyDefs

open MeasureTheory intervalIntegral Finset
noncomputable section

namespace Work.ZeroFreeTables.XY

/-- `xyP` in the factored form of HB Lemma 7.2 (`λ = 4/3`). -/
lemma xyP_factored (t : ℝ) :
    xyP t = (4/3/30)*(2-(4/3)*t)^3*(4+6*(4/3)*t+(4/3)^2*t^2) := by
  unfold xyP; ring

/-- `xyP` is non-negative on the support `[0, 3/2]`. -/
lemma xyP_nonneg (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 3/2) : 0 ≤ xyP t := by
  rw [xyP_factored]
  have h2 : 0 ≤ 2 - (4/3)*t := by linarith
  have h3 : 0 ≤ 4 + 6*(4/3)*t + (4/3)^2*t^2 := by nlinarith [h0, sq_nonneg ((4/3)*t)]
  exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h2 3)) h3

/-- On its support, the test function `xyT.f = tf72f (4/3)` is the polynomial `xyP`. -/
lemma tf72f43_eq (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) (3/2)) : tf72f (4/3) t = xyP t := by
  rw [xyP_factored]
  exact tf72f_eq_poly (4/3) (by norm_num) t (by
    have h : (2:ℝ)/(4/3) = 3/2 := by norm_num
    simpa [h] using ht)

/-- **`xyF` as a real integral**: `xyF x = ∫_0^{3/2} e^{-xt} xyP t dt`. -/
lemma xyF_eq_int (x : ℝ) :
    xyF x = ∫ t in (0:ℝ)..(3/2), Real.exp (-(x*t)) * xyP t := by
  rw [xyF, TestFn_F_eq_integral]
  rw [show xyT.x₀ = 3/2 by norm_num [xyT, tf72T]]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (0:ℝ) (3/2) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3/2)] at ht
    exact ht
  simp only [xyT, tf72T]
  rw [tf72f43_eq t ht']

/-- **The moments of `xyP`**: `∫_0^{3/2} t^j xyP t = xyM j` for every `j`, obtained by
expanding `t^j · xyP t` and integrating term by term (`integral_pow`). -/
lemma xyP_moment (j : ℕ) : ∫ t in (0:ℝ)..(3/2), t^j * xyP t = xyM j := by
  have key : ∀ t : ℝ, t^j * xyP t = (64/45)*t^j - (256/81)*t^(j+2)
      + (512/243)*t^(j+3) - (2048/10935)*t^(j+5) := by
    intro t; unfold xyP; ring
  rw [show (∫ t in (0:ℝ)..(3/2), t^j * xyP t)
      = ∫ t in (0:ℝ)..(3/2), ((64/45)*t^j - (256/81)*t^(j+2)
          + (512/243)*t^(j+3) - (2048/10935)*t^(j+5)) from by
    apply intervalIntegral.integral_congr; intro t ht; exact key t]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add, intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [integral_pow, integral_pow, integral_pow, integral_pow]
    unfold xyM; simp; ring
  all_goals exact Continuous.intervalIntegrable (by continuity) 0 (3/2)

/-- **Taylor bound for `exp` on `[0,3/2]`**: twelve exact terms plus the geometric
remainder `2 t^13/13!` (from `Complex.exp_bound'`, whose hypothesis
`‖x‖/n.succ ≤ 1/2` holds since `(3/2)/14 ≤ 1/2`). -/
lemma exp_le_taylor13 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 3/2) :
    Real.exp t ≤ (∑ j ∈ Finset.range 13, t^j/(j.factorial:ℝ)) + 2*t^13/(13:ℕ).factorial := by
  have ht : ‖(t:ℂ)‖ = t := by simp [abs_of_nonneg h0]
  have hnorm : ‖(t:ℂ)‖ / (13:ℕ).succ ≤ 1/2 := by
    rw [ht]; norm_num; linarith
  have hb := Complex.exp_bound' (x := (t:ℂ)) (n := 13) hnorm
  have hre := le_trans (Complex.re_le_norm _) hb
  have h1' : (Complex.exp (t:ℂ)).re = Real.exp t := by
    rw [← Complex.ofReal_exp, Complex.ofReal_re]
  have h2' : ∀ m ∈ Finset.range 13, ((t:ℂ)^m/(m.factorial:ℂ)).re = t^m/(m.factorial:ℝ) := by
    intro m hm
    rw [← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
  have hrw : (Complex.exp (t:ℂ) - ∑ m ∈ Finset.range 13, (t:ℂ)^m/(m.factorial:ℂ)).re
      = Real.exp t - ∑ m ∈ Finset.range 13, t^m/(m.factorial:ℝ) := by
    rw [Complex.sub_re, h1', Complex.re_sum]
    exact congrArg (fun z => Real.exp t - z) (Finset.sum_congr rfl h2')
  have hrw2 : ‖(t:ℂ)‖^13/((13:ℕ).factorial:ℝ)*2 = 2*t^13/(13:ℕ).factorial := by
    rw [ht]; ring
  rw [hrw, hrw2] at hre
  linarith

/-- The partial Taylor sum of `exp` used for the upper bound at `x = -1`:
`Σ_{j<13} t^j/j! + 2 t^13/13!`. -/
def xyPS (t : ℝ) : ℝ := (∑ j ∈ Finset.range 13, t^j/(j.factorial:ℝ)) + 2*t^13/(13:ℕ).factorial

/-- Integral of the partial Taylor polynomial of `exp` against `xyP`, evaluated in
terms of the moments `xyM j`. -/
lemma xyIntPS : ∫ t in (0:ℝ)..(3/2), xyPS t * xyP t
    = (∑ j ∈ Finset.range 13, xyM j / (j.factorial:ℝ)) + 2*xyM 13/(13:ℕ).factorial := by
  have h1 : ∀ i ∈ Finset.range 13,
      IntervalIntegrable (fun t : ℝ => t^i/(i.factorial:ℝ) * xyP t) volume (0:ℝ) (3/2) :=
    fun i _ => Continuous.intervalIntegrable (by simp only [xyP]; fun_prop) 0 (3/2)
  have h2 : IntervalIntegrable (fun t : ℝ => 2*t^13/(13:ℕ).factorial * xyP t)
      volume (0:ℝ) (3/2) :=
    Continuous.intervalIntegrable (by simp only [xyP]; fun_prop) 0 (3/2)
  have hsum : IntervalIntegrable
      (fun t : ℝ => ∑ i ∈ Finset.range 13, t^i/(i.factorial:ℝ) * xyP t) volume (0:ℝ) (3/2) :=
    Continuous.intervalIntegrable (by simp only [xyP]; fun_prop) 0 (3/2)
  rw [show (∫ t in (0:ℝ)..(3/2), xyPS t * xyP t)
      = ∫ t in (0:ℝ)..(3/2), (∑ i ∈ Finset.range 13, t^i/(i.factorial:ℝ) * xyP t)
          + 2*t^13/(13:ℕ).factorial * xyP t from by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [xyPS, add_mul, Finset.sum_mul]]
  rw [intervalIntegral.integral_add hsum h2]
  congr 1
  · rw [intervalIntegral.integral_finsetSum h1]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [show (∫ t in (0:ℝ)..(3/2), t^i/(i.factorial:ℝ) * xyP t)
        = ∫ t in (0:ℝ)..(3/2), (1/(i.factorial:ℝ)) * (t^i * xyP t) from by
      apply intervalIntegral.integral_congr; intro t ht; ring]
    rw [intervalIntegral.integral_const_mul, xyP_moment]
    ring
  · rw [show (∫ t in (0:ℝ)..(3/2), 2*t^13/(13:ℕ).factorial * xyP t)
        = ∫ t in (0:ℝ)..(3/2), (1/((13:ℕ).factorial:ℝ)) * (2 * (t^13 * xyP t)) from by
      apply intervalIntegral.integral_congr; intro t ht; ring]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, xyP_moment 13]
    ring

/-- **Upper bound at `x = -1`**: `F(-1) ≤ 1.3616`. -/
lemma xyF_neg_one_le : xyF (-1) ≤ 13616/10000 := by
  rw [xyF_eq_int]
  have hstep : ∫ t in (0:ℝ)..(3/2), Real.exp (-((-1:ℝ)*t)) * xyP t
      = ∫ t in (0:ℝ)..(3/2), Real.exp t * xyP t := by
    apply intervalIntegral.integral_congr; intro t ht; norm_num
  rw [hstep]
  have hf : IntervalIntegrable (fun t : ℝ => Real.exp t * xyP t) volume (0:ℝ) (3/2) :=
    Continuous.intervalIntegrable (by simp only [xyP]; fun_prop) 0 (3/2)
  have hg : IntervalIntegrable (fun t : ℝ => xyPS t * xyP t) volume (0:ℝ) (3/2) :=
    Continuous.intervalIntegrable (by simp only [xyPS, xyP]; fun_prop) 0 (3/2)
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) (3/2), Real.exp t * xyP t ≤ xyPS t * xyP t := by
    intro t ht
    have h := exp_le_taylor13 t ht.1 ht.2
    have hp := xyP_nonneg t ht.1 ht.2
    unfold xyPS
    exact mul_le_mul_of_nonneg_right h hp
  calc ∫ t in (0:ℝ)..(3/2), Real.exp t * xyP t
      ≤ ∫ t in (0:ℝ)..(3/2), xyPS t * xyP t :=
        intervalIntegral.integral_mono_on (by norm_num) hf hg hpt
    _ = (∑ j ∈ Finset.range 13, xyM j / (j.factorial:ℝ)) + 2*xyM 13/(13:ℕ).factorial := xyIntPS
    _ ≤ 13616/10000 := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero]
        norm_num [xyM]

/-- **Lower bound at `x = -372/1000`**: `F(-372/1000) ≥ 1.0314`. -/
lemma xyF_neg372_ge : 10314/10000 ≤ xyF (-372/1000) := by
  rw [xyF_eq_int]
  have hstep : ∫ t in (0:ℝ)..(3/2), Real.exp (-((-372/1000:ℝ)*t)) * xyP t
      = ∫ t in (0:ℝ)..(3/2), Real.exp ((372/1000:ℝ)*t) * xyP t := by
    apply intervalIntegral.integral_congr; intro t ht; norm_num
  rw [hstep]
  have hg : IntervalIntegrable (fun t : ℝ => Real.exp ((372/1000:ℝ)*t) * xyP t)
      volume (0:ℝ) (3/2) :=
    Continuous.intervalIntegrable (by simp only [xyP]; fun_prop) 0 (3/2)
  have hf : IntervalIntegrable
      (fun t : ℝ => (∑ j ∈ Finset.range 13, ((372/1000:ℝ)*t)^j/(j.factorial:ℝ)) * xyP t)
      volume (0:ℝ) (3/2) :=
    Continuous.intervalIntegrable (by simp only [xyP]; fun_prop) 0 (3/2)
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) (3/2),
      (∑ j ∈ Finset.range 13, ((372/1000:ℝ)*t)^j/(j.factorial:ℝ)) * xyP t
        ≤ Real.exp ((372/1000:ℝ)*t) * xyP t := by
    intro t ht
    have h := Real.sum_le_exp_of_nonneg
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 372/1000) ht.1) 13
    have hp := xyP_nonneg t ht.1 ht.2
    exact mul_le_mul_of_nonneg_right h hp
  have hint : ∫ t in (0:ℝ)..(3/2),
      (∑ j ∈ Finset.range 13, ((372/1000:ℝ)*t)^j/(j.factorial:ℝ)) * xyP t
      = ∑ j ∈ Finset.range 13, (372/1000:ℝ)^j * xyM j / (j.factorial:ℝ) := by
    have h1 : ∀ i ∈ Finset.range 13,
        IntervalIntegrable (fun t : ℝ => ((372/1000:ℝ)*t)^i/(i.factorial:ℝ) * xyP t)
          volume (0:ℝ) (3/2) :=
      fun i _ => Continuous.intervalIntegrable (by simp only [xyP]; fun_prop) 0 (3/2)
    rw [show (∫ t in (0:ℝ)..(3/2),
          (∑ j ∈ Finset.range 13, ((372/1000:ℝ)*t)^j/(j.factorial:ℝ)) * xyP t)
        = ∫ t in (0:ℝ)..(3/2),
          ∑ i ∈ Finset.range 13, ((372/1000:ℝ)*t)^i/(i.factorial:ℝ) * xyP t from by
      apply intervalIntegral.integral_congr; intro t ht; simp only [Finset.sum_mul]]
    rw [intervalIntegral.integral_finsetSum h1]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [show (∫ t in (0:ℝ)..(3/2), ((372/1000:ℝ)*t)^i/(i.factorial:ℝ) * xyP t)
        = ∫ t in (0:ℝ)..(3/2), ((372/1000:ℝ)^i/(i.factorial:ℝ)) * (t^i * xyP t) from by
      apply intervalIntegral.integral_congr; intro t ht; ring]
    rw [intervalIntegral.integral_const_mul, xyP_moment]
    ring
  calc (10314/10000 : ℝ)
      ≤ ∑ j ∈ Finset.range 13, (372/1000:ℝ)^j * xyM j / (j.factorial:ℝ) := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero]
        norm_num [xyM]
    _ = ∫ t in (0:ℝ)..(3/2),
        (∑ j ∈ Finset.range 13, ((372/1000:ℝ)*t)^j/(j.factorial:ℝ)) * xyP t := hint.symm
    _ ≤ ∫ t in (0:ℝ)..(3/2), Real.exp ((372/1000:ℝ)*t) * xyP t :=
        intervalIntegral.integral_mono_on (by norm_num) hf hg hpt

/-- **The numerical core** of the order-2 `λ₁`-estimate: for every `λ₁ ≤ 628/1000`,
`xyMain λ₁ + 240 < 0`, i.e. `14379·F(-1) - 24480·F(λ₁-1) + 3810·f(0) + 240 < 0`
for HB Lemma 7.2's test function with `λ = 4/3` (`xyT`).

Roadmap. `xyF` is antitone (`TestFn_F_antitone`), so `λ₁ ≤ 628/1000` gives
`λ₁ - 1 ≤ -0.372` and hence `F(λ₁-1) ≥ F(-0.372)`; with `f 0 = 64/45`
(`tf72f_at_zero`) it suffices to show `F(-1) ≤ 1.3616` and `F(-0.372) ≥ 1.0314`,
since `24480·(1.0314) - 14379·(1.3616) = 5670.2 > 5658.67 = 3810·(64/45) + 240`.
Both bounds follow from `TestFn_F_eq_integral` and `tf72f_eq_poly`
(`f(t) = (λ/30)(2-λt)³(4+6λt+λ²t²)` on `[0,3/2]`, `λ = 4/3`) together with the exact
moments `∫_0^{3/2} t^k f = 8/9, 12/35, 1/5, 1/7, 81/700, 9/88, 27/280` (`k = 0,…,6`, and the
general term is a rational you may recompute from `tf72f_eq_poly`) and the Taylor bounds
`Σ_{k≤N} x^k/k! ≤ e^x` (`Real.sum_le_exp_of_nonneg`) and
`e^x ≤ (Σ_{k≤N} x^k/k!)/(1 - x^{N+1}/(N+1)!)` for `0 ≤ x ≤ 3/2`; `N = 12` is more than enough
for the `4·10⁻⁴` accuracy required above. -/
theorem xyMainLt : ∀ lam₁ : ℝ, lam₁ ≤ 628/1000 → Work.ZeroFreeTables.xyMain lam₁ + 240 < 0 := by
  intro lam₁ hlam
  have hlt : lam₁ - 1 ≤ -372/1000 := by linarith
  have hmono : xyF (-372/1000) ≤ xyF (lam₁ - 1) := Work.ZeroFreeTables.TestFn_F_antitone xyT hlt
  have hlow : (10314/10000 : ℝ) ≤ xyF (lam₁ - 1) := le_trans xyF_neg372_ge hmono
  have hup : xyF (-1) ≤ 13616/10000 := xyF_neg_one_le
  have hf0 : xyT.f 0 = 64/45 := by
    show tf72f (4/3) 0 = 64/45
    rw [tf72f_at_zero (4/3) (by norm_num)]; norm_num
  unfold Work.ZeroFreeTables.xyMain
  rw [hf0]
  nlinarith [hup, hlow]

end Work.ZeroFreeTables.XY
