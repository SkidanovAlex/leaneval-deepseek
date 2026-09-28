import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.tau_basic

namespace Work.HP.HP2

/-- The `ℓ¹` norm of a real vector is at most `√(card ι)` times its Euclidean norm `rNorm`:
`Σᵢ |vᵢ| ≤ √(card ι) · rNorm v`.  Cauchy--Schwarz with the all-ones vector:
`(Σᵢ |vᵢ|)² = (Σᵢ 1·|vᵢ|)² ≤ (Σᵢ 1) · (Σᵢ |vᵢ|²) = card ι · (rNorm v)²`
(`Finset.sum_mul_sq_le_sq_mul_sq`), then take square roots
(`Real.sqrt_le_sqrt`, `Real.sqrt_mul`, `Real.sqrt_sq`, `Work.HP.rNorm_sq`). -/
theorem sum_abs_le_sqrt_card_mul {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ∑ i, |v i| ≤ Real.sqrt (Fintype.card ι) * rNorm v := by
  have hnn : 0 ≤ ∑ i, |v i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hrhs : 0 ≤ Real.sqrt (Fintype.card ι) * rNorm v :=
    mul_nonneg (Real.sqrt_nonneg _) (rNorm_nonneg v)
  -- Cauchy--Schwarz with the all-ones vector.
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
    (fun _ => (1 : ℝ)) (fun i => |v i|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  have h2 : (∑ i : ι, |v i| ^ 2) = ∑ i, v i ^ 2 := by
    apply Finset.sum_congr rfl; intro i _; rw [sq_abs]
  rw [h2, ← rNorm_sq v] at hcs
  have hcs2 : (∑ i, |v i|) ^ 2 ≤ (Real.sqrt (Fintype.card ι) * rNorm v) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    exact hcs
  calc ∑ i, |v i| = Real.sqrt ((∑ i, |v i|) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((Real.sqrt (Fintype.card ι) * rNorm v) ^ 2) := Real.sqrt_le_sqrt hcs2
    _ = Real.sqrt (Fintype.card ι) * rNorm v := Real.sqrt_sq hrhs

end Work.HP.HP2
