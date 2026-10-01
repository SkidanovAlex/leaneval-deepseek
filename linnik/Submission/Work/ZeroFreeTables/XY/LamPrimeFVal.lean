/-
# ZeroFreeTables/XY/LamPrimeFVal

Numerical values of the Laplace transform `xyF` of the order-2 test function
`xyT = tf72T (4/3)` (HB Lemma 7.2 with `λ = 4/3`), used by the order-2 `λ'`-estimate
`Work.ZeroFreeTables.XY.LamPrimeLower`:

  `xyF (-628/1000) ≤ 116/100`,  `xyF (372/1000) ≥ 77/100`,
  `xyF 0 = 8/9`,  `xyT.f 0 = 64/45`.

## Method

On its support `[0,3/2]`, `tf72f (4/3)` is the polynomial
`xyfP t = 64/45 - (256/81) t² + (512/243) t³ - (2048/10935) t⁵`, so for `a ∈ ℝ`

  `xyF (-a) = ∫₀^{3/2} e^{a t}·xyfP(t) dt`.

For `a = 628/1000` (resp. `a = -372/1000`) we exhibit an explicit rational polynomial
`Q` with `Q' + a·Q = xyfP`; the fundamental theorem of calculus then gives the exact
identity

  `∫₀^{3/2} e^{a t}·xyfP = e^{3a/2}·Q(3/2) - Q(0)`,

and the two inequalities follow from rational upper bounds on `Real.exp (942/1000)`
and `Real.exp (558/1000)` obtained from the Taylor bound `Real.exp_bound`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XY.LamPrimeDefs
import Submission.Work.ZeroFreeTables.XY.XYEngineDefs
import Submission.Work.ZeroFreeTables.XY.xyFNegLamGe

open Work.ZeroFreeTables Work.ZeroFreeTables.XY
open Polynomial
open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.XY

/-! ## `tf72f (4/3)` is the polynomial `xyfP` on `[0, 3/2]` -/

lemma LamFVal_tf72f43_eq_poly (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) (3/2)) :
    tf72f (4/3) t = xyfP.eval t := by
  rw [tf72f_eq_poly (4/3) (by norm_num) t (by
        rw [show (2:ℝ)/(4/3) = 3/2 by norm_num]; exact ht)]
  simp only [xyfP, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

/-! ## Two rational upper bounds for `Real.exp` -/

lemma LamFVal_exp_942_le : Real.exp (942/1000) ≤ 6413/2500 := by
  have h := (abs_le.mp (Real.exp_bound (x := (942/1000:ℝ)) (by norm_num) (n := 8) (by norm_num))).2
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (942:ℝ)/1000)] at h
  have hsum : (∑ m ∈ Finset.range 8, (942/1000:ℝ)^m / (m.factorial:ℝ))
      + (942/1000:ℝ)^8 * ((9:ℝ)/(40320*8)) ≤ 6413/2500 := by
    norm_num [Finset.sum_range_succ]
  have hh : (942/1000:ℝ)^8 * ((8:ℕ).succ / ((8:ℕ).factorial * (8:ℕ)))
      = (942/1000:ℝ)^8 * ((9:ℝ)/(40320*8)) := by norm_num
  linarith [h, hsum, hh.le]

lemma LamFVal_exp_558_le : Real.exp (558/1000) ≤ 1747175/1000000 := by
  have h := (abs_le.mp (Real.exp_bound (x := (558/1000:ℝ)) (by norm_num) (n := 10) (by norm_num))).2
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (558:ℝ)/1000)] at h
  have hsum : (∑ m ∈ Finset.range 10, (558/1000:ℝ)^m / (m.factorial:ℝ))
      + (558/1000:ℝ)^10 * ((11:ℝ)/(3628800*10)) ≤ 1747175/1000000 := by
    norm_num [Finset.sum_range_succ]
  have hh : (558/1000:ℝ)^10 * ((10:ℕ).succ / ((10:ℕ).factorial * (10:ℕ)))
      = (558/1000:ℝ)^10 * ((11:ℝ)/(3628800*10)) := by norm_num
  linarith [h, hsum, hh.le]

/-! ## The two rational antiderivatives -/

/-- `Q₁' + (628/1000)·Q₁ = xyfP`. -/
def LamFValQ1 : ℝ[X] :=
  C (2858728530870774400/10917556365126321) + C (-11336014816000000/69538575574053) * X
  + C (22672029632000/442920863529) * X^2 + C (-99604352000/8463455991) * X^3
  + C (128000000/53907363) * X^4 + C (-102400/343359) * X^5

/-- `Q₂' - (372/1000)·Q₂ = xyfP`. -/
def LamFValQ2 : ℝ[X] :=
  C (3744746479746774400/471655843734321) + C (14986198816000000/5071568212197) * X
  + C (29972397632000/54532991529) * X^2 + C (118036352000/1759128759) * X^3
  + C (128000000/18915363) * X^4 + C (102400/203391) * X^5

lemma LamFValQ1_deriv (t : ℝ) :
    LamFValQ1.derivative.eval t + (628/1000) * LamFValQ1.eval t = xyfP.eval t := by
  simp only [LamFValQ1, xyfP, Polynomial.derivative_add, Polynomial.derivative_C,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  ring

lemma LamFValQ2_deriv (t : ℝ) :
    LamFValQ2.derivative.eval t + (-(372/1000)) * LamFValQ2.eval t = xyfP.eval t := by
  simp only [LamFValQ2, xyfP, Polynomial.derivative_add, Polynomial.derivative_C,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero]
  ring

lemma LamFValQ1_eval_32 : LamFValQ1.eval (3/2) = 1119364000000000000/10917556365126321 := by
  simp only [LamFValQ1, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  norm_num

lemma LamFValQ1_eval_0 : LamFValQ1.eval 0 = 2858728530870774400/10917556365126321 := by
  simp only [LamFValQ1, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  norm_num

lemma LamFValQ2_eval_32 : LamFValQ2.eval (3/2) = 6543364000000000000/471655843734321 := by
  simp only [LamFValQ2, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  norm_num

lemma LamFValQ2_eval_0 : LamFValQ2.eval 0 = 3744746479746774400/471655843734321 := by
  simp only [LamFValQ2, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  norm_num

/-! ## The two exact integral evaluations -/

lemma LamFVal_integral_Q1 :
    (∫ t in (0:ℝ)..(3/2), Real.exp ((628/1000) * t) * xyfP.eval t)
      = Real.exp (942/1000) * LamFValQ1.eval (3/2) - LamFValQ1.eval 0 := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) (3/2),
      HasDerivAt (fun s => Real.exp ((628/1000)*s) * LamFValQ1.eval s)
        (Real.exp ((628/1000)*t)
          * (LamFValQ1.derivative.eval t + (628/1000) * LamFValQ1.eval t)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => Real.exp ((628/1000)*s))
        (Real.exp ((628/1000)*t) * (628/1000)) t :=
      by simpa using (((hasDerivAt_id t).const_mul ((628/1000:ℝ))).exp)
    have h2 : HasDerivAt (fun s : ℝ => LamFValQ1.eval s)
        (LamFValQ1.derivative.eval t) t := LamFValQ1.hasDerivAt t
    have h := h1.mul h2
    have heq : (Real.exp ((628/1000)*t) * (628/1000)) * LamFValQ1.eval t
        + Real.exp ((628/1000)*t) * LamFValQ1.derivative.eval t
        = Real.exp ((628/1000)*t)
          * (LamFValQ1.derivative.eval t + (628/1000) * LamFValQ1.eval t) := by ring
    rw [heq] at h
    exact h
  have hint : IntervalIntegrable (fun t => Real.exp ((628/1000)*t)
      * (LamFValQ1.derivative.eval t + (628/1000) * LamFValQ1.eval t))
      MeasureTheory.volume (0:ℝ) (3/2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hcongr : (∫ t in (0:ℝ)..(3/2), Real.exp ((628/1000) * t) * xyfP.eval t)
      = ∫ t in (0:ℝ)..(3/2), Real.exp ((628/1000)*t)
          * (LamFValQ1.derivative.eval t + (628/1000) * LamFValQ1.eval t) := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only []
    rw [LamFValQ1_deriv t]
  rw [hcongr, h]
  simp only [mul_zero, Real.exp_zero, one_mul]
  rw [show (628/1000)*(3/2 : ℝ) = 942/1000 by norm_num]

lemma LamFVal_integral_Q2 :
    (∫ t in (0:ℝ)..(3/2), Real.exp ((-(372/1000)) * t) * xyfP.eval t)
      = Real.exp (-(558/1000)) * LamFValQ2.eval (3/2) - LamFValQ2.eval 0 := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) (3/2),
      HasDerivAt (fun s => Real.exp ((-(372/1000))*s) * LamFValQ2.eval s)
        (Real.exp ((-(372/1000))*t)
          * (LamFValQ2.derivative.eval t + (-(372/1000)) * LamFValQ2.eval t)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => Real.exp ((-(372/1000))*s))
        (Real.exp ((-(372/1000))*t) * (-(372/1000))) t :=
      by simpa using (((hasDerivAt_id t).const_mul ((-(372/1000):ℝ))).exp)
    have h2 : HasDerivAt (fun s : ℝ => LamFValQ2.eval s)
        (LamFValQ2.derivative.eval t) t := LamFValQ2.hasDerivAt t
    have h := h1.mul h2
    have heq : (Real.exp ((-(372/1000))*t) * (-(372/1000))) * LamFValQ2.eval t
        + Real.exp ((-(372/1000))*t) * LamFValQ2.derivative.eval t
        = Real.exp ((-(372/1000))*t)
          * (LamFValQ2.derivative.eval t + (-(372/1000)) * LamFValQ2.eval t) := by ring
    rw [heq] at h
    exact h
  have hint : IntervalIntegrable (fun t => Real.exp ((-(372/1000))*t)
      * (LamFValQ2.derivative.eval t + (-(372/1000)) * LamFValQ2.eval t))
      MeasureTheory.volume (0:ℝ) (3/2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hcongr : (∫ t in (0:ℝ)..(3/2), Real.exp ((-(372/1000)) * t) * xyfP.eval t)
      = ∫ t in (0:ℝ)..(3/2), Real.exp ((-(372/1000))*t)
          * (LamFValQ2.derivative.eval t + (-(372/1000)) * LamFValQ2.eval t) := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only []
    rw [LamFValQ2_deriv t]
  rw [hcongr, h]
  simp only [mul_zero, Real.exp_zero, one_mul]
  rw [show (-(372/1000))*(3/2 : ℝ) = -(558/1000) by norm_num]

/-! ## The main statement -/

theorem LamPrimeFVal :
    xyF (-(628/1000)) ≤ 116/100 ∧ 77/100 ≤ xyF (372/1000) ∧ xyF 0 = 8/9 ∧ xyT.f 0 = 64/45 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hxy : xyF (-(628/1000))
        = ∫ u in (0:ℝ)..(3/2), Real.exp ((628/1000)*u) * xyfP.eval u := by
      rw [xyF_eq_integral]
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Set.Icc (0:ℝ) (3/2) := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3/2)] at hu; exact hu
      dsimp only []
      rw [xyT_f, LamFVal_tf72f43_eq_poly u hu']
      congr 1
      ring_nf
    rw [hxy, LamFVal_integral_Q1]
    have he : Real.exp (942/1000) ≤ 6413/2500 := LamFVal_exp_942_le
    have hA : 0 ≤ LamFValQ1.eval (3/2) := by rw [LamFValQ1_eval_32]; norm_num
    have hfin : (6413/2500:ℝ)*LamFValQ1.eval (3/2) - LamFValQ1.eval 0 ≤ 116/100 := by
      rw [LamFValQ1_eval_32, LamFValQ1_eval_0]; norm_num
    have hmul := mul_le_mul_of_nonneg_right he hA
    linarith
  · have hxy : xyF (372/1000)
        = ∫ u in (0:ℝ)..(3/2), Real.exp ((-(372/1000))*u) * xyfP.eval u := by
      rw [xyF_eq_integral]
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Set.Icc (0:ℝ) (3/2) := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 3/2)] at hu; exact hu
      dsimp only []
      rw [xyT_f, LamFVal_tf72f43_eq_poly u hu']
      congr 1
      ring_nf
    rw [hxy, LamFVal_integral_Q2]
    have hV : Real.exp (558/1000) ≤ 1747175/1000000 := LamFVal_exp_558_le
    have hinv : (1747175/1000000:ℝ)⁻¹ ≤ Real.exp (-(558/1000)) := by
      rw [Real.exp_neg]
      simpa [one_div] using one_div_le_one_div_of_le (Real.exp_pos (558/1000)) hV
    have hA : 0 ≤ LamFValQ2.eval (3/2) := by rw [LamFValQ2_eval_32]; norm_num
    have hfin : 77/100 ≤ (1747175/1000000:ℝ)⁻¹*LamFValQ2.eval (3/2) - LamFValQ2.eval 0 := by
      rw [LamFValQ2_eval_32, LamFValQ2_eval_0]; norm_num
    have hmul := mul_le_mul_of_nonneg_right hinv hA
    linarith
  · show (tf72Fc (4/3) (((0:ℝ)) : ℂ)).re = 8/9
    rw [show (((0:ℝ)):ℂ) = 0 from by norm_num]
    exact tf72Fc_zero_re (4/3) (by norm_num)
  · show tf72f (4/3) 0 = 64/45
    rw [tf72f_at_zero (4/3) (by norm_num)]
    norm_num

end Work.ZeroFreeTables.XY
