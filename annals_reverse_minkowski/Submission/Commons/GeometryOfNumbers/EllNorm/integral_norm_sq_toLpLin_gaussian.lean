import Mathlib
import Submission.Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq
import Submission.Commons.Analysis.GaussianMeasure.gaussian_second_moment_matrix

open MeasureTheory
open scoped BigOperators
open Finset

namespace Commons.GeometryOfNumbers.EllNorm

/-!
# The Gaussian second moment of `‖B x‖²`

For the standard Gaussian density `x ↦ exp (-π‖x‖²)` on `EuclideanSpace ℝ (Fin m)`
(of total mass `1`), whose second-moment matrix is `(1 / (2π)) • 1`
(see `Commons.Analysis.GaussianMeasure.gaussian_second_moment_matrix`), we compute the
second moment of `‖B x‖²` for a matrix `B`:

`∫ x, ‖B x‖² exp (-π‖x‖²) = (1 / (2π)) ∑ᵢ ∑ⱼ (B i j)²`.

This is the squared Hilbert–Schmidt norm of `B` scaled by `1 / (2π)`.
-/

/-- Coordinate monomials are integrable against the standard Gaussian density:
`∫ |xᵢ xⱼ| exp (-π‖x‖²) < ∞`. -/
private lemma integrable_monomial_gaussian {n : ℕ} (j k : Fin n) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      x j * x k * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
  have hbase : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖x‖) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) :=
    Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq Real.pi Real.pi_pos 2
  refine Integrable.mono' hbase ?_ ?_
  · fun_prop
  · filter_upwards with x
    have hxj : |x j| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x j
    have hxk : |x k| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x k
    have hEpos : 0 < Real.exp (-Real.pi * ‖x‖ ^ 2) := Real.exp_pos _
    have hnorm0 : 0 ≤ ‖x‖ := norm_nonneg x
    calc ‖x j * x k * Real.exp (-Real.pi * ‖x‖ ^ 2)‖
        = |x j| * |x k| * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hEpos]
      _ ≤ ‖x‖ * ‖x‖ * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hEpos)
            exact mul_le_mul hxj hxk (abs_nonneg _) hnorm0
      _ ≤ (1 + ‖x‖) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hEpos)
            nlinarith [hnorm0]

/-- The square of a linear form is integrable against the standard Gaussian density. -/
private lemma integrable_sq_linear_gaussian {n : ℕ} (c : Fin n → ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (∑ j, c j * x j) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
  have hbase : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖x‖) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) :=
    Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq Real.pi Real.pi_pos 2
  set S : ℝ := ∑ j, |c j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  refine Integrable.mono' (hbase.const_mul (S ^ 2)) ?_ ?_
  · fun_prop
  · filter_upwards with x
    have hnorm0 : 0 ≤ ‖x‖ := norm_nonneg x
    have hlin : |∑ j, c j * x j| ≤ S * ‖x‖ := by
      calc |∑ j, c j * x j| ≤ ∑ j, |c j * x j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |c j| * |x j| := by simp [abs_mul]
        _ ≤ ∑ j, |c j| * ‖x‖ := by
              refine Finset.sum_le_sum (fun j _ => ?_)
              exact mul_le_mul_of_nonneg_left (by simpa using PiLp.norm_apply_le x j) (abs_nonneg _)
        _ = S * ‖x‖ := by rw [Finset.sum_mul]
    have hsq : (∑ j, c j * x j) ^ 2 ≤ S ^ 2 * (1 + ‖x‖) ^ 2 := by
      rw [show (∑ j, c j * x j) ^ 2 = |∑ j, c j * x j| ^ 2 from (sq_abs _).symm]
      calc |∑ j, c j * x j| ^ 2 ≤ (S * ‖x‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hlin 2
        _ = S ^ 2 * ‖x‖ ^ 2 := by ring
        _ ≤ S ^ 2 * (1 + ‖x‖) ^ 2 := by
              apply mul_le_mul_of_nonneg_left _ (sq_nonneg S)
              nlinarith [norm_nonneg x]
    have hEpos : 0 < Real.exp (-Real.pi * ‖x‖ ^ 2) := Real.exp_pos _
    calc ‖(∑ j, c j * x j) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)‖
        = (∑ j, c j * x j) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt hEpos))]
      _ ≤ (S ^ 2 * (1 + ‖x‖) ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hsq (le_of_lt hEpos)
      _ = S ^ 2 * ((1 + ‖x‖) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by ring

/-- The Gaussian second moment of the square of a linear form, evaluated through
the second-moment matrix of the standard Gaussian: only diagonal terms survive. -/
private lemma integral_sq_linear_gaussian {n : ℕ} (c : Fin n → ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin n),
        (∑ j, c j * x j) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = ∑ j : Fin n, ∑ k : Fin n,
          c j * c k * (if j = k then 1 / (2 * Real.pi) else 0) := by
  have hpoint : (fun x : EuclideanSpace ℝ (Fin n) =>
        (∑ j, c j * x j) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = fun x => ∑ j : Fin n, ∑ k : Fin n,
          (c j * c k) * (x j * x k * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
    funext x
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [hpoint]
  have hterm : ∀ a b : Fin n, Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (c a * c b) * (x a * x b * Real.exp (-Real.pi * ‖x‖ ^ 2))) :=
    fun a b => (integrable_monomial_gaussian a b).const_mul (c a * c b)
  rw [integral_finsetSum Finset.univ
        (fun j _ => integrable_finsetSum Finset.univ (fun k _ => hterm j k))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_finsetSum Finset.univ (fun k _ => hterm j k)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_const_mul, Commons.Analysis.GaussianMeasure.gaussian_second_moment_matrix j k]

/-- The Gaussian second moment of `‖B x‖²` is `(1 / (2π))` times the sum of the
squares of the entries of `B`. -/
theorem integral_norm_sq_toLpLin_gaussian {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin m),
        ‖Matrix.toLpLin 2 2 B x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = (1 / (2 * Real.pi)) * ∑ i : Fin m, ∑ j : Fin m, (B i j) ^ 2 := by
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin m),
      ‖Matrix.toLpLin 2 2 B x‖ ^ 2 = ∑ i, (∑ j, B i j * x j) ^ 2 := by
    intro x
    rw [Matrix.toLpLin_apply, EuclideanSpace.real_norm_sq_eq]
    simp [Matrix.mulVec, dotProduct]
  have hfun : (fun x : EuclideanSpace ℝ (Fin m) =>
        ‖Matrix.toLpLin 2 2 B x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = fun x => ∑ i : Fin m, ((∑ j, B i j * x j) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
    funext x
    rw [hnorm x, Finset.sum_mul]
  rw [hfun]
  calc (∫ x : EuclideanSpace ℝ (Fin m),
          ∑ i : Fin m, ((∑ j, B i j * x j) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)))
      = ∑ i : Fin m, ∫ x : EuclideanSpace ℝ (Fin m),
          (∑ j, B i j * x j) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
          rw [integral_finsetSum Finset.univ
                (fun i _ => integrable_sq_linear_gaussian (fun j => B i j))]
    _ = ∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m,
          B i j * B i k * (if j = k then 1 / (2 * Real.pi) else 0) := by
          refine Finset.sum_congr rfl (fun i _ => integral_sq_linear_gaussian (fun j => B i j))
    _ = ∑ i : Fin m, (1 / (2 * Real.pi)) * ∑ j : Fin m, (B i j) ^ 2 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have hinner : ∀ j : Fin m,
              (∑ k : Fin m, B i j * B i k * (if j = k then 1 / (2 * Real.pi) else 0))
                = (1 / (2 * Real.pi)) * (B i j) ^ 2 := by
            intro j
            have hik : ∀ k : Fin m, B i j * B i k * (if j = k then 1 / (2 * Real.pi) else 0)
                = (if j = k then B i j * B i k * (1 / (2 * Real.pi)) else 0) := by
              intro k
              by_cases h : j = k <;> simp [h]
            simp_rw [hik]
            rw [Finset.sum_ite_eq]
            simp only [Finset.mem_univ, if_true]
            ring
          rw [Finset.sum_congr rfl (fun j _ => hinner j)]
          exact (Finset.mul_sum Finset.univ (fun j => (B i j) ^ 2) (1 / (2 * Real.pi))).symm
    _ = (1 / (2 * Real.pi)) * ∑ i : Fin m, ∑ j : Fin m, (B i j) ^ 2 :=
          (Finset.mul_sum Finset.univ (fun i => ∑ j : Fin m, (B i j) ^ 2) (1 / (2 * Real.pi))).symm

end Commons.GeometryOfNumbers.EllNorm
