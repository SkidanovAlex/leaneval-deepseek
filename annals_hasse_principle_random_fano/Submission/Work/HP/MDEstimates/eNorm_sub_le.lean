import Mathlib
import Submission.Work.HP.MinkDefs

namespace Work.HP.MDEstimates

open Finset

/-- Triangle inequality for the Euclidean norm `√(∑ xᵢ²)` on real vectors. -/
lemma sqrt_sum_sq_sub_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    √(∑ i, (x i - y i) ^ 2) ≤ √(∑ i, x i ^ 2) + √(∑ i, y i ^ 2) := by
  set A : ℝ := ∑ i, x i ^ 2 with hA
  set B : ℝ := ∑ i, y i ^ 2 with hB
  have hA0 : 0 ≤ A := by rw [hA]; exact sum_nonneg fun i _ => sq_nonneg (x i)
  have hB0 : 0 ≤ B := by rw [hB]; exact sum_nonneg fun i _ => sq_nonneg (y i)
  have hcsneg : -(∑ i, x i * y i) ≤ √A * √B := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι) (fun i => -x i) y
    simp only [Finset.sum_neg_distrib, neg_mul, neg_sq] at h
    rw [← hA, ← hB] at h
    simpa using h
  have hexp : ∑ i, (x i - y i) ^ 2 = A - 2 * (∑ i, x i * y i) + B := by
    have h1 : ∀ i, (x i - y i) ^ 2 = x i ^ 2 - 2 * (x i * y i) + y i ^ 2 := fun i => by ring
    calc ∑ i, (x i - y i) ^ 2
        = ∑ i, (x i ^ 2 - 2 * (x i * y i) + y i ^ 2) :=
          Finset.sum_congr rfl (fun i _ => h1 i)
      _ = ∑ i, x i ^ 2 - ∑ i, 2 * (x i * y i) + ∑ i, y i ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = A - 2 * (∑ i, x i * y i) + B := by
          rw [hA, hB, ← Finset.mul_sum]
  have hsq : ∑ i, (x i - y i) ^ 2 ≤ (√A + √B) ^ 2 := by
    rw [hexp]
    nlinarith [hcsneg, Real.sq_sqrt hA0, Real.sq_sqrt hB0, Real.sqrt_nonneg A, Real.sqrt_nonneg B]
  have hmain : √(∑ i, (x i - y i) ^ 2) ≤ √A + √B := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B))] at h
  rw [hA, hB] at hmain
  exact hmain

lemma eNorm_sub_le {ι : Type*} [Fintype ι] (v w : ι → ℤ) :
    Work.HP.eNorm (v - w) ≤ Work.HP.eNorm v + Work.HP.eNorm w := by
  have h := sqrt_sum_sq_sub_le (fun i => (v i : ℝ)) (fun i => (w i : ℝ))
  simpa [Work.HP.eNorm, Pi.sub_apply] using h

end Work.HP.MDEstimates
