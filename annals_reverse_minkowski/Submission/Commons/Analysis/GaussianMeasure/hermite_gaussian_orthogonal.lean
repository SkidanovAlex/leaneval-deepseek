import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.ou_semigroup_contDiff_bounded

namespace Commons.Analysis.GaussianMeasure

open Polynomial MeasureTheory

noncomputable section

/-- The standard Gaussian weight `x ↦ exp (-x²/2)`. -/
private abbrev gauss : ℝ → ℝ := fun x => Real.exp (-(x ^ 2 / 2))

/-- The `n`-th probabilists' Hermite polynomial evaluated at `x`. -/
private abbrev Hh (n : ℕ) : ℝ → ℝ := fun x => Polynomial.aeval x (Polynomial.hermite n)

/-- The derivative of the `n`-th Hermite polynomial is `n` times the `(n-1)`-th one. -/
private theorem hermite_derivative (n : ℕ) :
    (Polynomial.hermite n).derivative = (n : ℤ) • Polynomial.hermite (n - 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp
    | 1 => rw [Polynomial.hermite_one, Polynomial.hermite_zero]; simp
    | (k + 2) =>
      have h1 : (Polynomial.hermite (k + 1)).derivative
          = (k + 1 : ℤ) • Polynomial.hermite k := by
        have := ih (k + 1) (by omega)
        simpa using this
      have h0 : (Polynomial.hermite k).derivative
          = (k : ℤ) • Polynomial.hermite (k - 1) := ih k (by omega)
      rw [show k + 2 = k + 1 + 1 by omega, Polynomial.hermite_succ (k + 1)]
      rw [Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_X]
      simp only [one_mul]
      rw [h1, Polynomial.derivative_smul, h0]
      rw [Polynomial.hermite_succ k, h0]
      rw [show (k + 1 + 1 - 1) = k + 1 by omega]
      rw [Polynomial.hermite_succ k, h0]
      simp only [mul_smul_comm, smul_sub, smul_smul]
      push_cast
      module

private lemma aeval_eq_eval_map (P : Polynomial ℤ) (x : ℝ) :
    Polynomial.aeval x P = (P.map (algebraMap ℤ ℝ)).eval x := by
  rw [Polynomial.aeval_def, Polynomial.eval_map]

/-- Analytic derivative of the Hermite polynomials (as functions of `x`). -/
private lemma hasDerivAt_Hh (m : ℕ) (x : ℝ) :
    HasDerivAt (Hh (m + 1)) ((m + 1 : ℝ) * Hh m x) x := by
  have h := Polynomial.hasDerivAt_aeval (Polynomial.hermite (m + 1)) x
  have key : Polynomial.aeval x ((Polynomial.hermite (m + 1)).derivative)
      = (m + 1 : ℝ) * Polynomial.aeval x (Polynomial.hermite m) := by
    rw [hermite_derivative (m + 1), Nat.add_sub_cancel, map_smul]
    simp
  rw [← key]
  exact h

/-- `(-1)^n * (-1)^n = 1`. -/
private lemma neg_one_pow_mul_self (n : ℕ) : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
  rcases Nat.even_or_odd n with h | h
  · simp [h.neg_one_pow]
  · simp [h.neg_one_pow]

/-- The `n`-th derivative of the Gaussian is `(-1)^n He_n g`. -/
private lemma iteratedDeriv_gauss (n : ℕ) :
    iteratedDeriv n gauss = fun z : ℝ => (-1 : ℝ) ^ n * Hh n z * gauss z := by
  rw [iteratedDeriv_exp_neg_sq_eq]
  funext z
  simp only [Hh, aeval_hermite_eq_eval_map]

private lemma integrable_aeval_mul_gauss (P : Polynomial ℤ) :
    Integrable (fun x : ℝ => Polynomial.aeval x P * gauss x) := by
  have h := integrable_polynomial_mul_gaussian (P.map (algebraMap ℤ ℝ))
  simpa only [aeval_eq_eval_map] using h

private lemma integrable_HH_mul_HH_mul_gauss (a b : ℕ) :
    Integrable (fun x : ℝ => Hh a x * Hh b x * gauss x) := by
  have h := integrable_aeval_mul_gauss (Polynomial.hermite a * Polynomial.hermite b)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Hh, Polynomial.aeval_mul, mul_assoc]

private lemma integrable_HH_iteratedDeriv (a k : ℕ) :
    Integrable (fun x : ℝ => Hh a x * iteratedDeriv k gauss x) := by
  have h := integrable_HH_mul_HH_mul_gauss a k
  refine (h.const_mul ((-1 : ℝ) ^ k)).congr (Filter.Eventually.of_forall fun x => ?_)
  rw [iteratedDeriv_gauss k]
  ring

private lemma hasDerivAt_iteratedDeriv_gauss (n : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv n gauss) (iteratedDeriv (n + 1) gauss x) x := by
  have hdiff : Differentiable ℝ (iteratedDeriv n gauss) :=
    (show ContDiff ℝ (n + 1 : ℕ) gauss from by unfold gauss; fun_prop).differentiable_iteratedDeriv
      n (Nat.cast_lt.mpr (Nat.lt_succ_self n))
  have h := (hdiff x).hasDerivAt
  rw [← iteratedDeriv_succ] at h
  exact h

/-- The bilinear form `B m n = ∫ He_m (z) · g⁽ⁿ⁾(z) dz`. -/
private def B (m n : ℕ) : ℝ := ∫ x, Hh m x * iteratedDeriv n gauss x

/-- The symmetric bilinear form `A m n = ∫ He_m · He_n · g`. -/
private def A (m n : ℕ) : ℝ := ∫ x, Hh m x * Hh n x * gauss x

private lemma B_zero_right (n : ℕ) (hn : 1 ≤ n) : B 0 n = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  unfold B
  have h := integral_eq_zero_of_hasDerivAt_of_integrable
      (f := iteratedDeriv k gauss) (f' := iteratedDeriv (k + 1) gauss)
      (fun x => hasDerivAt_iteratedDeriv_gauss k x)
      (integrable_iteratedDeriv_exp_neg_sq (k + 1))
      (integrable_iteratedDeriv_exp_neg_sq k)
  simpa [Hh] using h

private lemma B_succ_succ (m n : ℕ) :
    B (m + 1) (n + 1) = -((m + 1 : ℝ)) * B m n := by
  have hu'v : Integrable (fun x : ℝ => ((m + 1 : ℝ) * Hh m x) * iteratedDeriv n gauss x) :=
    ((integrable_HH_iteratedDeriv m n).const_mul (m + 1 : ℝ)).congr
      (Filter.Eventually.of_forall fun x => by ring)
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := Hh (m + 1)) (u' := fun x : ℝ => (m + 1 : ℝ) * Hh m x)
      (v := iteratedDeriv n gauss) (v' := iteratedDeriv (n + 1) gauss)
      (fun x _ => hasDerivAt_Hh m x)
      (fun x _ => hasDerivAt_iteratedDeriv_gauss n x)
      (integrable_HH_iteratedDeriv (m + 1) (n + 1))
      hu'v
      (integrable_HH_iteratedDeriv (m + 1) n)
  unfold B
  rw [h]
  have hcong : (∫ x : ℝ, ((m + 1 : ℝ) * Hh m x) * iteratedDeriv n gauss x)
      = ∫ x : ℝ, (m + 1 : ℝ) * (Hh m x * iteratedDeriv n gauss x) := by
    congr 1
    funext x
    ring
  rw [hcong, integral_const_mul]
  ring

private lemma B_eq_zero_of_lt (m n : ℕ) (hmn : m < n) : B m n = 0 := by
  induction m generalizing n with
  | zero => exact B_zero_right n (by omega)
  | succ m ih =>
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [B_succ_succ, ih n' (by omega), mul_zero]

private lemma A_eq (m n : ℕ) : A m n = (-1 : ℝ) ^ n * B m n := by
  unfold A B
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [iteratedDeriv_gauss n]
  have e : (-1 : ℝ) ^ n * (Hh m x * ((-1 : ℝ) ^ n * Hh n x * gauss x))
      = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) * (Hh m x * Hh n x * gauss x) := by ring
  rw [e, neg_one_pow_mul_self, one_mul]

theorem hermite_gaussian_orthogonal {m n : ℕ} (hmn : m ≠ n) :
    (∫ x : ℝ, (Polynomial.aeval x (Polynomial.hermite m))
        * (Polynomial.aeval x (Polynomial.hermite n)) * Real.exp (-(x ^ 2 / 2))) = 0 := by
  show A m n = 0
  rcases lt_or_gt_of_ne hmn with h | h
  · rw [A_eq, B_eq_zero_of_lt m n h, mul_zero]
  · have hsym : A m n = A n m := by
      unfold A
      congr 1
      funext x
      ring
    rw [hsym, A_eq, B_eq_zero_of_lt n m h, mul_zero]

end

end Commons.Analysis.GaussianMeasure
