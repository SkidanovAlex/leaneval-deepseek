import Mathlib

open scoped Matrix

namespace Work.Mostow

/-- Operator-norm bound for a real square matrix whose entries are uniformly close to the
identity: if every entry of `M - 1` is bounded by `q ≥ 0` in absolute value, then the operator
norm of `M - 1` acting on Euclidean space is at most `k * q`.

Proof: the operator norm is bounded by the Frobenius norm, and there are `k²` entries each of
size at most `q`, so the Frobenius norm is at most `k * q`. -/
theorem mat_toEuclideanCLM_norm_le {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (q : ℝ) (hq : 0 ≤ q)
    (h : ∀ i j, |M i j - (1 : Matrix (Fin k) (Fin k) ℝ) i j| ≤ q) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (M - 1)‖ ≤ (k : ℝ) * q := by
  set A : Matrix (Fin k) (Fin k) ℝ := M - 1 with hAdef
  -- Entrywise bound `|A i j| ≤ q`.
  have hAq : ∀ i j, |A i j| ≤ q := by
    intro i j
    have h1 : A i j = M i j - (1 : Matrix (Fin k) (Fin k) ℝ) i j := by
      rw [hAdef, Matrix.sub_apply]
    rw [h1]; exact h i j
  -- Squared entrywise bound.
  have hA2 : ∀ i j, (A i j) ^ 2 ≤ q ^ 2 := by
    intro i j
    have h1 : |A i j| ≤ |q| := by rw [abs_of_nonneg hq]; exact hAq i j
    exact (sq_le_sq).mpr h1
  -- It suffices to bound `‖A x‖ ≤ (k * q) * ‖x‖` for every `x`.
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro x
  set v : Fin k → ℝ := x.ofLp
  have hxnorm : ‖x‖ ^ 2 = ∑ j, (v j) ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]
  -- Row-wise Cauchy–Schwarz together with the entrywise bound.
  have hterm : ∀ i, ((A *ᵥ v) i) ^ 2 ≤ ((k : ℝ) * q ^ 2) * (∑ j, (v j) ^ 2) := by
    intro i
    have h1 : ((A *ᵥ v) i) ^ 2 = (∑ j, A i j * v j) ^ 2 := by
      simp [Matrix.mulVec_apply, Matrix.row, dotProduct]
    rw [h1]
    calc (∑ j, A i j * v j) ^ 2
        ≤ (∑ j, (A i j) ^ 2) * (∑ j, (v j) ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ ((k : ℝ) * q ^ 2) * (∑ j, (v j) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc (∑ j, (A i j) ^ 2) ≤ ∑ j, q ^ 2 := Finset.sum_le_sum (fun j _ => hA2 i j)
            _ = (k : ℝ) * q ^ 2 := by simp [Finset.sum_const, Finset.card_univ]
  have key : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) A x‖ ^ 2
      ≤ (((k : ℝ) * q) * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hof : ∀ i,
        ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) A x).ofLp i) = (A *ᵥ v) i := by
      intro i
      rw [Matrix.ofLp_toEuclideanCLM]
    simp only [hof]
    calc (∑ i, ((A *ᵥ v) i) ^ 2) ≤ ∑ i, ((k : ℝ) * q ^ 2) * (∑ j, (v j) ^ 2) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = (((k : ℝ) * q) * ‖x‖) ^ 2 := by
          rw [← hxnorm]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hle : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) A x‖ ≤ ((k : ℝ) * q) * ‖x‖ := by
    have h2 := (sq_le_sq.mp key)
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at h2
  exact hle

end Work.Mostow
