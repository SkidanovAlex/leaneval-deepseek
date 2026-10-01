import Mathlib
import Submission.Work.ZeroFreeTables.XYDefs
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.testFn72_defs

namespace Work.ZeroFreeTables.XY

open Work.ZeroFreeTables
open Polynomial
open scoped BigOperators

noncomputable section

/-! ## The Laplace transform of `xyT` at `-1` as a real integral -/

lemma xyT_x₀ : xyT.x₀ = 3 / 2 := by
  show (2 : ℝ) / (4 / 3) = 3 / 2
  norm_num

lemma xyT_f : xyT.f = tf72f (4 / 3) := rfl

/-- `F(-1)` for the test function `xyT` is the explicit real integral `∫₀^{3/2} e^t f(t) dt`. -/
lemma xyF_neg_one : xyF (-1) = ∫ t in (0 : ℝ)..(3 / 2), Real.exp t * tf72f (4 / 3) t := by
  rw [xyF, TestFn_F_eq_integral]
  rw [xyT_x₀]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [neg_mul, one_mul, neg_neg, xyT_f]

/-! ## The numerical computation -/

/-- Fundamental theorem of calculus for a polynomial: the interval integral of the
evaluation of the derivative is the difference of the evaluations. -/
lemma integral_derivative_eval (p : ℝ[X]) (a b : ℝ) :
    (∫ t in a..b, (Polynomial.derivative p).eval t) = p.eval b - p.eval a := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => p.hasDerivAt x) ?_
  exact (Polynomial.continuous (Polynomial.derivative p)).intervalIntegrable a b

/-- The Taylor polynomial `Σ_{k ≤ 5} t^k/k!` of `exp`, as a polynomial over `ℝ`. -/
def xyTay : ℝ[X] :=
  Polynomial.C 1 + Polynomial.C 1 * Polynomial.X + Polynomial.C (1/2) * Polynomial.X^2
    + Polynomial.C (1/6) * Polynomial.X^3 + Polynomial.C (1/24) * Polynomial.X^4
    + Polynomial.C (1/120) * Polynomial.X^5

/-- HB Lemma 7.2's function `f` with `λ = 4/3` on its support `[0, 3/2]`, as a polynomial
(`tf72f (4/3) t = 64/45 - (256/81)t² + (512/243)t³ - (2048/10935)t⁵` there). -/
def xyfP : ℝ[X] :=
  Polynomial.C (64/45) + Polynomial.C (-256/81) * Polynomial.X^2
    + Polynomial.C (512/243) * Polynomial.X^3 + Polynomial.C (-2048/10935) * Polynomial.X^5

/-- An explicit antiderivative of the polynomial `xyTay * xyfP`. -/
def xyFP : ℝ[X] :=
  Polynomial.C (64/45) * Polynomial.X + Polynomial.C (32/45) * Polynomial.X^2
    + Polynomial.C (-992/1215) * Polynomial.X^3 + Polynomial.C (-248/1215) * Polynomial.X^4
    + Polynomial.C (712/6075) * Polynomial.X^5 + Polynomial.C (9604/164025) * Polynomial.X^6
    + Polynomial.C (352/76545) * Polynomial.X^7 + Polynomial.C (-44/10935) * Polynomial.X^8
    + Polynomial.C (-448/295245) * Polynomial.X^9 + Polynomial.C (-128/164025) * Polynomial.X^10
    + Polynomial.C (-256/1804275) * Polynomial.X^11

/-- `xyFP` is an antiderivative of `xyTay * xyfP`. -/
lemma xyFP_deriv (x : ℝ) :
    (Polynomial.derivative xyFP).eval x = (xyTay * xyfP).eval x := by
  simp only [xyFP, xyTay, xyfP, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one]
  ring_nf

/-- The evaluation of `xyFP` at the endpoints. -/
lemma xyFP_eval : xyFP.eval (3/2) - xyFP.eval 0 = 1509331 / 1108800 := by
  simp only [xyFP, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  norm_num

/-- `Σ_{k ≤ 5} t^k/k!` as an explicit polynomial in `t`. -/
lemma taylor5_eq (t : ℝ) :
    (∑ k ∈ Finset.range 6, t ^ k / ((k.factorial : ℕ) : ℝ))
      = 1 + t + t^2/2 + t^3/6 + t^4/24 + t^5/120 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero]

/-- On the support of `f`, the integrand `(Σ_{k ≤ 5} t^k/k!)·f(t)` is the polynomial
`xyTay * xyfP`. -/
lemma xy_integrand_eq (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (3 / 2)) :
    (∑ k ∈ Finset.range 6, t ^ k / ((k.factorial : ℕ) : ℝ)) * tf72f (4 / 3) t
      = (xyTay * xyfP).eval t := by
  have ht' : t ∈ Set.Icc (0 : ℝ) (2 / (4 / 3)) := by
    rw [show (2 : ℝ) / (4 / 3) = 3 / 2 by norm_num]; exact ht
  rw [tf72f_eq_poly (4 / 3) (by norm_num) t ht', taylor5_eq]
  simp only [xyTay, xyfP, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  ring_nf

/-- Numerical core (Taylor-truncation part) of the order-2 `λ₁`-estimate for the
test function `tf72f (4/3)`: the integral of `(Σ_{k≤5} t^k/k!)·f` over the support `[0,3/2]`. -/
lemma xyTaylorIntegral :
    (∫ t in (0 : ℝ)..(3 / 2),
        (∑ k ∈ Finset.range 6, t ^ k / ((k.factorial : ℕ) : ℝ)) * tf72f (4 / 3) t)
      = 1509331 / 1108800 := by
  have h1 : (∫ t in (0 : ℝ)..(3 / 2),
        (∑ k ∈ Finset.range 6, t ^ k / ((k.factorial : ℕ) : ℝ)) * tf72f (4 / 3) t)
      = ∫ t in (0 : ℝ)..(3 / 2), (xyTay * xyfP).eval t := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact xy_integrand_eq t (by simpa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3/2)] using ht)
  rw [h1]
  have h2 : (∫ t in (0 : ℝ)..(3 / 2), (xyTay * xyfP).eval t)
      = ∫ t in (0 : ℝ)..(3 / 2), (Polynomial.derivative xyFP).eval t := by
    apply intervalIntegral.integral_congr
    intro t _
    exact (xyFP_deriv t).symm
  rw [h2, integral_derivative_eval xyFP 0 (3/2), xyFP_eval]

/-- The numerical core of the order-2 `λ₁`-estimate: for the test function `xyT`
(HB Lemma 7.2 with `λ = 4/3`), `F(-1) = ∫_0^{3/2} e^t f(t) dt ≥ 1.35`.

Proof route: `TestFn_F_eq_integral` identifies `xyF (-1)` with `∫_0^{3/2} e^t·f(t)`;
`tf72f_eq_poly` gives the polynomial form `f(t) = (λ/30)(2-λt)³(4+6λt+λ²t²)` on `[0,3/2]`;
`Real.sum_le_exp_of_nonneg` gives `e^t ≥ Σ_{k≤5} t^k/k!` for `t ≥ 0`; the moments are
`∫ f = 8/9`, `∫ t f = 12/35`, `∫ t²f = 1/5`, `∫ t³f = 1/7`, `∫ t⁴f = 81/700`, `∫ t⁵f = 9/88`,
and `Σ_{k≤5} (1/k!)∫t^k f = 1509331/1108800 = 1.3612… ≥ 1.35`. -/
theorem xyFNegLamGe : 135/100 ≤ Work.ZeroFreeTables.xyF (-1) := by
  rw [xyF_neg_one]
  have hle : (∫ t in (0 : ℝ)..(3 / 2),
        (∑ k ∈ Finset.range 6, t ^ k / ((k.factorial : ℕ) : ℝ)) * tf72f (4 / 3) t)
      ≤ ∫ t in (0 : ℝ)..(3 / 2), Real.exp t * tf72f (4 / 3) t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · refine ContinuousOn.intervalIntegrable_of_Icc (by norm_num) ?_
      have hpoly : Continuous
          (fun t : ℝ => ∑ k ∈ Finset.range 6, t ^ k / ((k.factorial : ℕ) : ℝ)) :=
        continuous_finsetSum _ (fun k _ => (continuous_id.pow k).div_const _)
      exact hpoly.continuousOn.mul
        ((tf72f_cont (4 / 3) (by norm_num)).mono Set.Icc_subset_Ici_self)
    · refine ContinuousOn.intervalIntegrable_of_Icc (by norm_num) ?_
      have he : ContinuousOn (fun t : ℝ => Real.exp t) (Set.Icc (0 : ℝ) (3 / 2)) :=
        Real.continuous_exp.continuousOn
      exact he.mul ((tf72f_cont (4 / 3) (by norm_num)).mono Set.Icc_subset_Ici_self)
    · intro x hx
      exact mul_le_mul_of_nonneg_right (Real.sum_le_exp_of_nonneg hx.1 6)
        (tf72f_nonneg (4 / 3) (by norm_num) x)
  rw [xyTaylorIntegral] at hle
  have hc : (135 : ℝ) / 100 ≤ 1509331 / 1108800 := by norm_num
  linarith

end

end Work.ZeroFreeTables.XY
