import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.MvPolynomial
import Submission.Commons.Measure.Integral.integrable_pow_mul_exp_neg_norm_sq

namespace Commons.Analysis.GaussianMeasure

open scoped BigOperators ENNReal
open _root_.MeasureTheory

/-- Growth bound: the evaluation of a multivariate polynomial on `EuclideanSpace ℝ (Fin n)` is
bounded by `K * (1 + ‖x‖) ^ N` for suitable `K ≥ 0` and `N`. -/
lemma exists_bound_mvpoly_eval {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, ∀ x : EuclideanSpace ℝ (Fin n),
      |MvPolynomial.eval (fun i => x.ofLp i) P| ≤ K * (1 + ‖x‖) ^ N := by
  refine ⟨∑ d ∈ P.support, |P.coeff d|, ?_, P.totalDegree, ?_⟩
  · exact Finset.sum_nonneg (fun d _ => abs_nonneg _)
  · intro x
    rw [MvPolynomial.eval_eq']
    calc |∑ d ∈ P.support, P.coeff d * ∏ i, x.ofLp i ^ d i|
        ≤ ∑ d ∈ P.support, |P.coeff d * ∏ i, x.ofLp i ^ d i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ d ∈ P.support, |P.coeff d| * |∏ i, x.ofLp i ^ d i| := by
          apply Finset.sum_congr rfl
          intro d _
          rw [abs_mul]
      _ ≤ ∑ d ∈ P.support, |P.coeff d| * (1 + ‖x‖) ^ P.totalDegree := by
          apply Finset.sum_le_sum
          intro d hd
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have habs : |∏ i, x.ofLp i ^ d i| = ∏ i, |x.ofLp i| ^ d i := by
            rw [Finset.abs_prod]
            apply Finset.prod_congr rfl
            intro i _
            rw [abs_pow]
          rw [habs]
          have hdegree : (∑ i, d i) ≤ P.totalDegree := by
            have h := MvPolynomial.le_totalDegree (R := ℝ) hd
            have hsum : (d.sum fun x e => e) = ∑ i, d i :=
              Finsupp.sum_fintype d (fun i e => e) (fun i => rfl)
            rwa [hsum] at h
          calc ∏ i, |x.ofLp i| ^ d i
              ≤ ∏ i, ‖x‖ ^ d i := by
                apply Finset.prod_le_prod
                · intro i _; positivity
                · intro i _
                  exact pow_le_pow_left₀ (abs_nonneg _) (PiLp.norm_apply_le x i) _
            _ = ‖x‖ ^ (∑ i, d i) :=
                Finset.prod_pow_eq_pow_sum Finset.univ (fun i => d i) ‖x‖
            _ ≤ (1 + ‖x‖) ^ (∑ i, d i) :=
                pow_le_pow_left₀ (norm_nonneg x) (by linarith [norm_nonneg x]) _
            _ ≤ (1 + ‖x‖) ^ P.totalDegree :=
                pow_le_pow_right₀ (by linarith [norm_nonneg x]) hdegree
      _ = (∑ d ∈ P.support, |P.coeff d|) * (1 + ‖x‖) ^ P.totalDegree := by
          rw [Finset.sum_mul]

lemma continuous_mvpoly_eval {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x.ofLp i) P) := by
  have h1 : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x.ofLp) :=
    PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)
  exact (MvPolynomial.continuous_eval P).comp h1

theorem memLp_mvpoly_withDensity_exp_neg_sq_half {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    MeasureTheory.MemLp
      (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x.ofLp i) P) 2
      (MeasureTheory.volume.withDensity
        (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))) := by
  obtain ⟨K, hK, N, hbound⟩ := exists_bound_mvpoly_eval P
  set Φ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => MvPolynomial.eval (fun i => x.ofLp i) P with hΦdef
  have hΦcont : Continuous Φ := continuous_mvpoly_eval P
  set dens : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)) with hdensdef
  have hdens_meas : Measurable dens := by
    rw [hdensdef]
    exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp (by fun_prop))
  have hdens_lt_top : ∀ x, dens x < ⊤ := fun x => ENNReal.ofReal_lt_top
  -- an integrable Gaussian majorant on `volume`
  have hb : (0 : ℝ) < 1 / 2 := by norm_num
  have hbase : MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) ^ (2 * N) * Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2))
      MeasureTheory.volume :=
    Commons.Measure.Integral.integrable_pow_mul_exp_neg_norm_sq (1 / 2) hb (2 * N)
  have hbase' : MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) ^ (2 * N) * Real.exp (-‖x‖ ^ 2 / 2))
      MeasureTheory.volume := by
    refine hbase.congr ?_
    filter_upwards with x
    congr 2
    ring
  have hdom : MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => Φ x ^ 2 * Real.exp (-‖x‖ ^ 2 / 2))
      MeasureTheory.volume := by
    refine (hbase'.const_mul (K ^ 2)).mono' ?_ ?_
    · exact ((hΦcont.pow 2).mul (Real.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
      calc Φ x ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)
          = |Φ x| ^ 2 * Real.exp (-‖x‖ ^ 2 / 2) := by rw [sq_abs]
        _ ≤ (K * (1 + ‖x‖) ^ N) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2) := by
              apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
              exact pow_le_pow_left₀ (abs_nonneg _) (hbound x) 2
        _ = K ^ 2 * ((1 + ‖x‖) ^ (2 * N) * Real.exp (-‖x‖ ^ 2 / 2)) := by
              have hpow : ((1 + ‖x‖) ^ N) ^ 2 = (1 + ‖x‖) ^ (2 * N) := by
                rw [← pow_mul, Nat.mul_comm]
              rw [mul_pow, hpow]; ring
  rw [MeasureTheory.memLp_two_iff_integrable_sq hΦcont.aestronglyMeasurable]
  refine (MeasureTheory.integrable_withDensity_iff hdens_meas
    (Filter.Eventually.of_forall hdens_lt_top)).mpr ?_
  refine hdom.congr ?_
  filter_upwards with x
  rw [hdensdef]
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]

end Commons.Analysis.GaussianMeasure