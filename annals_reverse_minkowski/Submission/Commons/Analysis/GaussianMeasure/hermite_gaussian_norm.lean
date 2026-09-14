import Mathlib.Algebra.Polynomial.Eval.SMul
import Submission.Commons.Analysis.GaussianMeasure.ou_semigroup_contDiff_bounded

namespace Commons.Analysis.GaussianMeasure

open Polynomial MeasureTheory Filter
open scoped Real

noncomputable section

/-- `derivative (hermite n) = n • hermite (n - 1)` over `ℤ` (equivalently `Hₙ' = n Hₙ₋₁`). -/
private lemma hermite_derivative_int (n : ℕ) :
    Polynomial.derivative (Polynomial.hermite n) = n • Polynomial.hermite (n - 1) := by
  set L : ℤ[X] → ℤ[X] := fun p => X * p - Polynomial.derivative p with hL
  have hLderiv : ∀ p, Polynomial.derivative (L p) = L (Polynomial.derivative p) + p := by
    intro p
    simp only [hL]
    rw [Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_X]
    ring
  have hLnsmul : ∀ (m : ℕ) (p : ℤ[X]), L (m • p) = m • L p := by
    intro m p
    simp only [hL]
    rw [Polynomial.derivative_smul, nsmul_eq_mul]
    ring
  have hiter : ∀ n, Polynomial.hermite n = (L^[n]) 1 := by
    intro n
    rw [Polynomial.hermite_eq_iterate, hL]
  have key : ∀ n, Polynomial.derivative ((L^[n+1]) 1) = (n+1) • (L^[n]) 1 := by
    intro n
    induction n with
    | zero =>
      rw [show (L^[0+1]) (1 : ℤ[X]) = X by
        rw [Function.iterate_succ_apply']
        simp [hL]]
      simp [Polynomial.derivative_X]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      rw [hLderiv, ih, hLnsmul]
      rw [show L ((L^[k]) 1) = (L^[k+1]) 1 from (Function.iterate_succ_apply' L k 1).symm]
      rw [show (k + 1 + 1) • ((L^[k+1]) 1) = (k+1) • ((L^[k+1]) 1) + (L^[k+1]) 1
            from succ_nsmul ((L^[k+1]) 1) (k+1)]
  match n with
  | 0 => simp [Polynomial.hermite_zero]
  | (k+1) =>
    rw [hiter (k+1), key k]
    simp only [Nat.add_sub_cancel]
    rw [hiter k]

/-- The real (probabilists') Hermite polynomial `Hₙ`. -/
private noncomputable def hermiteR (n : ℕ) : ℝ[X] := (Polynomial.hermite n).map (algebraMap ℤ ℝ)

private lemma hermiteR_zero : hermiteR 0 = 1 := by simp [hermiteR]

private lemma hermiteR_succ (n : ℕ) :
    hermiteR (n + 1) = X * hermiteR n - Polynomial.derivative (hermiteR n) := by
  have h := congrArg (fun p : ℤ[X] => p.map (algebraMap ℤ ℝ)) (Polynomial.hermite_succ n)
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X] at h
  simp only [hermiteR, Polynomial.derivative_map] at h ⊢
  exact h

private lemma derivative_hermiteR_succ (n : ℕ) :
    Polynomial.derivative (hermiteR (n+1)) = (n+1) • hermiteR n := by
  have h := congrArg (fun p : ℤ[X] => p.map (algebraMap ℤ ℝ)) (hermite_derivative_int (n+1))
  rw [← Polynomial.derivative_map] at h
  rw [show (n + 1 - 1 : ℕ) = n from Nat.add_sub_cancel n 1] at h
  have hmap : Polynomial.map (algebraMap ℤ ℝ) ((n + 1) • Polynomial.hermite n)
      = (n + 1) • Polynomial.map (algebraMap ℤ ℝ) (Polynomial.hermite n) :=
    map_nsmul (Polynomial.mapRingHom (algebraMap ℤ ℝ)) (n + 1) (Polynomial.hermite n)
  rw [hmap] at h
  simpa [hermiteR] using h

private lemma hermiteR_aeval_eq (n : ℕ) (x : ℝ) :
    Polynomial.aeval x (Polynomial.hermite n) = (hermiteR n).eval x := by
  simpa [hermiteR] using aeval_hermite_eq_eval_map n x

private lemma hasDerivAt_gaussian (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) (-x * Real.exp (-(x ^ 2 / 2))) x := by
  have h0 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  have hinner : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-x) x :=
    ((h0.div_const 2).neg).congr_deriv (by ring)
  exact (hinner.exp).congr_deriv (by ring)

private lemma hasDerivAt_hermiteR_mul_gaussian (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (hermiteR n).eval y * Real.exp (-(y ^ 2 / 2)))
      (-((hermiteR (n + 1)).eval x) * Real.exp (-(x ^ 2 / 2))) x := by
  have h := ((hermiteR n).hasDerivAt x).mul (hasDerivAt_gaussian x)
  refine h.congr_deriv ?_
  rw [hermiteR_succ n]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
  ring

private lemma integral_exp_neg_half_sq :
    (∫ x : ℝ, Real.exp (-(x ^ 2 / 2))) = Real.sqrt (2 * Real.pi) := by
  have h1 : (∫ x : ℝ, Real.exp (-(x ^ 2 / 2)))
      = ∫ x : ℝ, Real.exp (-(1/2 : ℝ) * x ^ 2) := by
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    ring
  rw [h1, integral_gaussian]
  rw [show Real.pi / (1/2 : ℝ) = 2 * Real.pi by ring]

private lemma hermite_gaussian_recursion (n : ℕ) :
    (∫ x : ℝ, (hermiteR (n + 1)).eval x ^ 2 * Real.exp (-(x ^ 2 / 2)))
      = (n + 1) * (∫ x : ℝ, (hermiteR n).eval x ^ 2 * Real.exp (-(x ^ 2 / 2))) := by
  have hIBP := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => (hermiteR (n + 1)).eval x)
    (u' := fun x : ℝ => (Polynomial.derivative (hermiteR (n + 1))).eval x)
    (v := fun x : ℝ => (hermiteR n).eval x * Real.exp (-(x ^ 2 / 2)))
    (v' := fun x : ℝ => -((hermiteR (n + 1)).eval x) * Real.exp (-(x ^ 2 / 2)))
    (fun x _ => (hermiteR (n + 1)).hasDerivAt x)
    (fun x _ => hasDerivAt_hermiteR_mul_gaussian n x)
    (by
      refine (integrable_polynomial_mul_gaussian (-(hermiteR (n+1) * hermiteR (n+1)))).congr ?_
      filter_upwards with x
      simp only [Pi.mul_apply, Polynomial.eval_neg, Polynomial.eval_mul]
      ring)
    (by
      refine (integrable_polynomial_mul_gaussian
        (Polynomial.C ((n+1 : ℝ)) * (hermiteR n * hermiteR n))).congr ?_
      filter_upwards with x
      simp only [Pi.mul_apply]
      rw [derivative_hermiteR_succ, Polynomial.eval_smul]
      simp only [Polynomial.eval_C, Polynomial.eval_mul, nsmul_eq_mul]
      push_cast
      ring)
    (by
      refine (integrable_polynomial_mul_gaussian (hermiteR (n+1) * hermiteR n)).congr ?_
      filter_upwards with x
      simp only [Pi.mul_apply, Polynomial.eval_mul]
      ring)
  have hL : (∫ x : ℝ, (fun x : ℝ => (hermiteR (n + 1)).eval x) x
        * (fun x : ℝ => -((hermiteR (n + 1)).eval x) * Real.exp (-(x ^ 2 / 2))) x)
      = -(∫ x : ℝ, (hermiteR (n + 1)).eval x ^ 2 * Real.exp (-(x ^ 2 / 2))) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    show (hermiteR (n + 1)).eval x * (-((hermiteR (n + 1)).eval x) * Real.exp (-(x ^ 2 / 2)))
        = -((hermiteR (n + 1)).eval x ^ 2 * Real.exp (-(x ^ 2 / 2)))
    ring
  have hR : (∫ x : ℝ, (fun x : ℝ => (Polynomial.derivative (hermiteR (n + 1))).eval x) x
        * (fun x : ℝ => (hermiteR n).eval x * Real.exp (-(x ^ 2 / 2))) x)
      = (n + 1) * (∫ x : ℝ, (hermiteR n).eval x ^ 2 * Real.exp (-(x ^ 2 / 2))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    show (Polynomial.derivative (hermiteR (n+1))).eval x * ((hermiteR n).eval x * Real.exp (-(x ^ 2 / 2)))
        = (n + 1) * ((hermiteR n).eval x ^ 2 * Real.exp (-(x ^ 2 / 2)))
    rw [derivative_hermiteR_succ, Polynomial.eval_smul, nsmul_eq_mul]
    push_cast
    ring
  rw [hL, hR] at hIBP
  exact neg_inj.mp hIBP

theorem hermite_gaussian_norm (n : ℕ) :
    (∫ x : ℝ, (Polynomial.aeval x (Polynomial.hermite n)) ^ 2 * Real.exp (-(x ^ 2 / 2)))
      = (n.factorial : ℝ) * Real.sqrt (2 * Real.pi) := by
  simp_rw [hermiteR_aeval_eq]
  induction n with
  | zero =>
    rw [hermiteR_zero]
    simp only [Polynomial.eval_one, one_pow, one_mul, Nat.factorial_zero, Nat.cast_one, one_mul]
    exact integral_exp_neg_half_sq
  | succ n ih =>
    rw [hermite_gaussian_recursion n, ih, Nat.factorial_succ]
    push_cast
    ring

end

end Commons.Analysis.GaussianMeasure