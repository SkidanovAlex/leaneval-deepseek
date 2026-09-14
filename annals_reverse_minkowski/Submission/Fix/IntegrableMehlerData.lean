-- ⚠ IMPORT-CLASH WORKAROUND (session 123): verbatim copy of Submission.Commons.Analysis.GaussianMeasure.integrable_mehler_data
-- with the import chain redirected so that the duplicate constant `toLp_norm_sq` of
-- `…bobkov_strong_nD` is not pulled into the same environment as
-- `…brascamp_lieb_truncated`.  Do not import both this file and the commons original.
import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.integrable_gaussian_smul_of_norm_le
import Submission.Fix.IntegrableGaussianMulGauge
import Submission.Commons.Analysis.GaussianMeasure.ou_semigroup_contDiff_bounded

open MeasureTheory Polynomial
open scoped BigOperators

namespace Commons.Analysis.GaussianMeasure

noncomputable section

/-!
## Integrability of the Mehler data

The Gaussian density `y ↦ exp(-‖y - ρ•x‖²/(2(1-ρ²)))` times (the gauge of) a finite combination of
multivariate Hermite polynomials is integrable on `ℝ^N`.  This is the integrability input for the
Mehler-type manipulations in the reverse Minkowski theorem.

Both components of the statement are obtained from the general lemmas
`integrable_gaussian_smul_of_norm_le` and `integrable_gaussian_mul_gauge_of_norm_le` once we know
that the Hermite sum grows at most polynomially (and is continuous).
-/

/-! ### Growth bounds for Hermite polynomials -/

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

/-- The finite Hermite sum `∑_{α ∈ s} (∏ i, hermite_{α i}(y i)) • C α` grows at most
polynomially. -/
private lemma hermite_sum_norm_bound {n N : ℕ} (s : Finset (Fin N → ℕ))
    (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ D : ℕ, ∀ y : EuclideanSpace ℝ (Fin N),
      ‖∑ α ∈ s, ((∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) • C α)‖
        ≤ A * (1 + ‖y‖) ^ D := by
  classical
  choose cc hcc0 hcc using abs_prod_aeval_hermite_le
  refine ⟨∑ α ∈ s, cc α * ‖C α‖, ?_, ∑ α ∈ s, ∑ i, α i, ?_⟩
  · exact Finset.sum_nonneg (fun α _ => mul_nonneg (hcc0 α) (norm_nonneg _))
  · intro y
    have h1 : (1 : ℝ) ≤ 1 + ‖y‖ := by have := norm_nonneg y; linarith
    calc ‖∑ α ∈ s, ((∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) • C α)‖
        ≤ ∑ α ∈ s, ‖(∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) • C α‖ :=
          norm_sum_le s _
      _ = ∑ α ∈ s, |∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))| * ‖C α‖ := by
          apply Finset.sum_congr rfl; intro α _
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ α ∈ s, (cc α * (1 + ‖y‖) ^ (∑ i, α i)) * ‖C α‖ := by
          apply Finset.sum_le_sum; intro α _
          exact mul_le_mul_of_nonneg_right (hcc α y) (norm_nonneg _)
      _ ≤ ∑ α ∈ s, (cc α * (1 + ‖y‖) ^ (∑ α' ∈ s, ∑ i, α' i)) * ‖C α‖ := by
          apply Finset.sum_le_sum; intro α hα
          have hle : ∑ i, α i ≤ ∑ α' ∈ s, ∑ i, α' i :=
            Finset.single_le_sum (fun b _ => Nat.zero_le _) hα
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hle) (hcc0 α)) (norm_nonneg _)
      _ = (∑ α ∈ s, cc α * ‖C α‖) * (1 + ‖y‖) ^ (∑ α ∈ s, ∑ i, α i) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro α _; ring

/-! ### The main statement -/

theorem integrable_mehler_data {n N : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKcvx : Convex ℝ K) (hK0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ K)
    (hKabs : Absorbent ℝ K) (hKbdd : Bornology.IsVonNBounded ℝ K) (hKbal : Balanced ℝ K)
    (ρ : ℝ) (hρ : ρ ^ 2 < 1) (s : Finset (Fin N → ℕ))
    (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) :
    (∀ x : EuclideanSpace ℝ (Fin N),
        MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin N) =>
          (Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) : ℝ) •
            (∑ α ∈ s, ((∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) • C α)))
          MeasureTheory.volume) ∧
    (∀ x : EuclideanSpace ℝ (Fin N),
        MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin N) =>
          Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) *
            gauge K (∑ α ∈ s, ((∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) • C α)))
          MeasureTheory.volume) := by
  classical
  obtain ⟨A, hA0, D, hΦbound⟩ := hermite_sum_norm_bound s C
  have hΦcont : Continuous (fun y : EuclideanSpace ℝ (Fin N) =>
      ∑ α ∈ s, ((∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) • C α)) := by
    fun_prop
  have ha : 0 < 1 / (2 * (1 - ρ ^ 2)) := by
    have : 0 < 1 - ρ ^ 2 := by linarith
    positivity
  constructor
  · intro x
    refine (integrable_gaussian_smul_of_norm_le
        (Φ := fun y : EuclideanSpace ℝ (Fin N) =>
          ∑ α ∈ s, ((∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) • C α))
        hΦcont hA0 hΦbound (1 / (2 * (1 - ρ ^ 2))) ha (ρ • x)).congr ?_
    filter_upwards with y
    rw [show -(1 / (2 * (1 - ρ ^ 2))) * ‖y - ρ • x‖ ^ 2
          = -‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2)) by ring]
  · intro x
    refine (integrable_gaussian_mul_gauge_of_norm_le K hKcvx hK0 hKabs hKbdd hKbal
        (Φ := fun y : EuclideanSpace ℝ (Fin N) =>
          ∑ α ∈ s, ((∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) • C α))
        hΦcont hA0 hΦbound (1 / (2 * (1 - ρ ^ 2))) ha (ρ • x)).congr ?_
    filter_upwards with y
    rw [show -(1 / (2 * (1 - ρ ^ 2))) * ‖y - ρ • x‖ ^ 2
          = -‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2)) by ring]

end

end Commons.Analysis.GaussianMeasure
