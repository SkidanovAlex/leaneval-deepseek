import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.ou_multivariate_hermite_eigenfunction_gen
import Submission.Commons.Analysis.GaussianMeasure.ou_semigroup_contDiff_bounded
import Submission.Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq

open MeasureTheory Polynomial
open scoped BigOperators

namespace Commons.Analysis.GaussianMeasure

noncomputable section

private lemma abs_aeval_hermite_le (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ,
      |Polynomial.aeval t (Polynomial.hermite n)| ≤ M * (1 + |t|) ^ n := by
  refine ⟨∑ k ∈ Finset.range (n + 1),
      |(((Polynomial.hermite n).map (algebraMap ℤ ℝ)).coeff k)|, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun k _ => abs_nonneg _)
  · intro t
    rw [aeval_hermite_eq_eval_map]
    set q : ℝ[X] := (Polynomial.hermite n).map (algebraMap ℤ ℝ) with hq
    have hdeg : q.natDegree ≤ n := by
      rw [hq]
      calc ((Polynomial.hermite n).map (algebraMap ℤ ℝ)).natDegree
          ≤ (Polynomial.hermite n).natDegree := Polynomial.natDegree_map_le
        _ = n := Polynomial.natDegree_hermite
    have hpow : ∀ i : ℕ, i ≤ n → |t| ^ i ≤ (1 + |t|) ^ n := by
      intro i hi
      calc |t| ^ i ≤ (1 + |t|) ^ i := pow_le_pow_left₀ (abs_nonneg t) (by linarith [abs_nonneg t]) i
        _ ≤ (1 + |t|) ^ n := pow_le_pow_right₀ (by linarith [abs_nonneg t]) hi
    calc |Polynomial.eval t q|
        = |∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * t ^ i| := by
            rw [Polynomial.eval_eq_sum_range]
      _ ≤ ∑ i ∈ Finset.range (q.natDegree + 1), |q.coeff i * t ^ i| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range (q.natDegree + 1), |q.coeff i| * |t| ^ i := by
            apply Finset.sum_congr rfl; intro i _; rw [abs_mul, abs_pow]
      _ ≤ ∑ i ∈ Finset.range (q.natDegree + 1), |q.coeff i| * (1 + |t|) ^ n := by
            apply Finset.sum_le_sum; intro i hi
            have hi' : i ≤ n := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hdeg
            exact mul_le_mul_of_nonneg_left (hpow i hi') (abs_nonneg _)
      _ = (∑ i ∈ Finset.range (q.natDegree + 1), |q.coeff i|) * (1 + |t|) ^ n := by
            rw [Finset.sum_mul]
      _ ≤ (∑ k ∈ Finset.range (n + 1),
              |(((Polynomial.hermite n).map (algebraMap ℤ ℝ)).coeff k)|) * (1 + |t|) ^ n := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) _)
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.range_subset_range.mpr (by omega)
            · intro k _ _; exact abs_nonneg _

private lemma abs_prod_aeval_hermite_le {N : ℕ} (α : Fin N → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : EuclideanSpace ℝ (Fin N),
      |∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))|
        ≤ C * (1 + ‖y‖) ^ (∑ i, α i) := by
  choose M hM0 hM using abs_aeval_hermite_le
  refine ⟨∏ i, M (α i), ?_, ?_⟩
  · exact Finset.prod_nonneg (fun i _ => hM0 (α i))
  · intro y
    rw [Finset.abs_prod]
    calc ∏ i, |Polynomial.aeval (y i) (Polynomial.hermite (α i))|
        ≤ ∏ i, (M (α i) * (1 + |y i|) ^ (α i)) := by
          apply Finset.prod_le_prod
          · intro i _; exact abs_nonneg _
          · intro i _; exact hM (α i) (y i)
      _ = (∏ i, M (α i)) * ∏ i, (1 + |y i|) ^ (α i) := Finset.prod_mul_distrib
      _ ≤ (∏ i, M (α i)) * ∏ i, (1 + ‖y‖) ^ (α i) := by
          apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun i _ => hM0 (α i)))
          apply Finset.prod_le_prod
          · intro i _; positivity
          · intro i _
            have h : |y i| ≤ ‖y‖ := by
              have := PiLp.norm_apply_le (p := 2) y i
              simpa [Real.norm_eq_abs] using this
            exact pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = (∏ i, M (α i)) * (1 + ‖y‖) ^ (∑ i, α i) := by
          rw [Finset.prod_pow_eq_pow_sum]

private lemma norm_sq_half_sub_le_norm_sq_sub {N : ℕ} (y c : EuclideanSpace ℝ (Fin N)) :
    ‖y‖ ^ 2 / 2 - ‖c‖ ^ 2 ≤ ‖y - c‖ ^ 2 := by
  have h1 : |‖y‖ - ‖c‖| ≤ ‖y - c‖ := abs_norm_sub_norm_le y c
  have h2 : (‖y‖ - ‖c‖) ^ 2 ≤ ‖y - c‖ ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg (‖y‖ - ‖c‖)) h1 2
    simpa [sq_abs] using this
  nlinarith [h2, sq_nonneg (‖y‖ - 2 * ‖c‖)]

private lemma exp_neg_mul_norm_sq_sub_le {N : ℕ} (a : ℝ) (ha : 0 < a)
    (c y : EuclideanSpace ℝ (Fin N)) :
    Real.exp (-a * ‖y - c‖ ^ 2) ≤ Real.exp (a * ‖c‖ ^ 2) * Real.exp (-(a / 2) * ‖y‖ ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [norm_sq_half_sub_le_norm_sq_sub y c, ha]

private lemma integrable_exp_neg_sq_mul_hermite {N : ℕ} (α : Fin N → ℕ) (a : ℝ) (ha : 0 < a)
    (c : EuclideanSpace ℝ (Fin N)) :
    Integrable (fun y : EuclideanSpace ℝ (Fin N) =>
      Real.exp (-a * ‖y - c‖ ^ 2) *
        ∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) volume := by
  obtain ⟨C, hC0, hC⟩ := abs_prod_aeval_hermite_le α
  set K : ℝ := Real.exp (a * ‖c‖ ^ 2) * C with hK
  have hbc : Integrable (fun y : EuclideanSpace ℝ (Fin N) =>
      (1 + ‖y‖) ^ (∑ i, α i) * Real.exp (-(a / 2) * ‖y‖ ^ 2)) :=
    Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq (a / 2) (by linarith) (∑ i, α i)
  have hg : Integrable (fun y : EuclideanSpace ℝ (Fin N) =>
      K * ((1 + ‖y‖) ^ (∑ i, α i) * Real.exp (-(a / 2) * ‖y‖ ^ 2))) :=
    hbc.const_mul K
  refine hg.mono' ?meas ?bound
  · have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin N) =>
        Real.exp (-a * ‖y - c‖ ^ 2) * ∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-a * ‖y - c‖ ^ 2) * |∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))|
        ≤ Real.exp (-a * ‖y - c‖ ^ 2) * (C * (1 + ‖y‖) ^ (∑ i, α i)) :=
          mul_le_mul_of_nonneg_left (hC y) (Real.exp_pos _).le
      _ = (Real.exp (-a * ‖y - c‖ ^ 2) * C) * (1 + ‖y‖) ^ (∑ i, α i) := by ring
      _ ≤ (Real.exp (a * ‖c‖ ^ 2) * Real.exp (-(a / 2) * ‖y‖ ^ 2) * C)
            * (1 + ‖y‖) ^ (∑ i, α i) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) _)
          exact mul_le_mul_of_nonneg_right (exp_neg_mul_norm_sq_sub_le a ha c y) hC0
      _ = K * ((1 + ‖y‖) ^ (∑ i, α i) * Real.exp (-(a / 2) * ‖y‖ ^ 2)) := by rw [hK]; ring

private lemma integrable_mehler_scalar {N : ℕ} (α : Fin N → ℕ) (ρ : ℝ) (hρ : ρ ^ 2 < 1)
    (x : EuclideanSpace ℝ (Fin N)) :
    Integrable (fun y : EuclideanSpace ℝ (Fin N) =>
      Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) *
        ∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) volume := by
  have h1ρ : 0 < 1 - ρ ^ 2 := by linarith
  have h := integrable_exp_neg_sq_mul_hermite α (1 / (2 * (1 - ρ ^ 2))) (by positivity) (ρ • x)
  refine h.congr ?_
  filter_upwards with y
  have harg : -(1 / (2 * (1 - ρ ^ 2))) * ‖y - ρ • x‖ ^ 2
      = -‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [harg]

theorem mehler_hermite_sum {n N : ℕ} (s : Finset (Fin N → ℕ))
    (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hρ : ρ ^ 2 < 1)
    (x : EuclideanSpace ℝ (Fin N)) :
    (2 * Real.pi * (1 - ρ ^ 2)) ^ (-(N : ℝ) / 2) •
        (∫ y, (Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) : ℝ) •
          (∑ α ∈ s, ((∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) • C α))
          ∂MeasureTheory.volume)
      = ∑ α ∈ s, ((ρ ^ (∑ i, α i) * (∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i)))) • C α) := by
  have h1ρ : 0 < 1 - ρ ^ 2 := by linarith
  set a : ℝ := 2 * Real.pi * (1 - ρ ^ 2) with ha
  have hapos : 0 < a := by rw [ha]; positivity
  have haN : a ^ ((N : ℝ) / 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hapos _)
  have hstep : (∫ y, (Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) : ℝ) •
          (∑ α ∈ s, ((∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) • C α))
          ∂MeasureTheory.volume)
      = ∑ α ∈ s, ((∫ y, Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) *
            (∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) ∂MeasureTheory.volume) • C α) := by
    have hint : ∀ α ∈ s, Integrable (fun y : EuclideanSpace ℝ (Fin N) =>
        (Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) *
          (∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i)))) • C α) MeasureTheory.volume := by
      intro α _
      exact (integrable_mehler_scalar α ρ hρ x).smul_const (C α)
    have hpoint : ∀ y, (Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) : ℝ) •
          (∑ α ∈ s, ((∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) • C α))
        = ∑ α ∈ s, (Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) *
            (∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i)))) • C α := by
      intro y
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro α _
      rw [smul_smul]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint),
      MeasureTheory.integral_finsetSum s hint]
    apply Finset.sum_congr rfl
    intro α _
    exact integral_smul_const _ _
  have hval : ∀ α : Fin N → ℕ,
      (∫ y, Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) *
            (∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) ∂MeasureTheory.volume)
        = a ^ ((N : ℝ) / 2) * (ρ ^ (∑ i, α i) *
            (∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i)))) := by
    intro α
    have hcm := ou_multivariate_hermite_eigenfunction_gen α ρ hρ x
    rw [← ha] at hcm
    have hcm' : (1 / a ^ ((N : ℝ) / 2)) *
          (∫ y, Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) *
            (∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) ∂MeasureTheory.volume)
        = ρ ^ (∑ i, α i) * (∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))) := by
      rw [← hcm, ← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      ring
    have hmul : a ^ ((N : ℝ) / 2) * (1 / a ^ ((N : ℝ) / 2)) = 1 := by
      rw [mul_one_div, div_self haN]
    calc (∫ y, Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) *
            (∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) ∂MeasureTheory.volume)
        = 1 * (∫ y, Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) *
            (∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) ∂MeasureTheory.volume) :=
          (one_mul _).symm
      _ = (a ^ ((N : ℝ) / 2) * (1 / a ^ ((N : ℝ) / 2))) *
            (∫ y, Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) *
              (∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) ∂MeasureTheory.volume) := by
          rw [hmul]
      _ = a ^ ((N : ℝ) / 2) * ((1 / a ^ ((N : ℝ) / 2)) *
            (∫ y, Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) *
              (∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) ∂MeasureTheory.volume)) := by
          rw [mul_assoc]
      _ = a ^ ((N : ℝ) / 2) * (ρ ^ (∑ i, α i) *
            (∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i)))) := by rw [hcm']
  have hpow : a ^ (-(N : ℝ) / 2) * a ^ ((N : ℝ) / 2) = 1 := by
    rw [show -(N : ℝ) / 2 = -((N : ℝ) / 2) by ring, Real.rpow_neg hapos.le,
      inv_mul_cancel₀ haN]
  rw [hstep, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [hval α, smul_smul, ← mul_assoc, hpow, one_mul]

end

end Commons.Analysis.GaussianMeasure
