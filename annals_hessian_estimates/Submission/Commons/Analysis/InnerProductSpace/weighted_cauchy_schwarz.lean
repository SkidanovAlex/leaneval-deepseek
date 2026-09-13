import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.InnerProductSpace

theorem weighted_cauchy_schwarz {n : ℕ} (f x c : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i, f i * x i * c i) ^ 2 ≤ (∑ i, f i * x i ^ 2) * (∑ i, f i * c i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
    (fun i => Real.sqrt (f i) * x i) (fun i => Real.sqrt (f i) * c i)
  have h1 : (∑ i, Real.sqrt (f i) * x i * (Real.sqrt (f i) * c i)) = ∑ i, f i * x i * c i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [show Real.sqrt (f i) * x i * (Real.sqrt (f i) * c i) = Real.sqrt (f i) ^ 2 * x i * c i by ring,
        Real.sq_sqrt (hf i)]
  have h2 : (∑ i, (Real.sqrt (f i) * x i) ^ 2) = ∑ i, f i * x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [show (Real.sqrt (f i) * x i) ^ 2 = Real.sqrt (f i) ^ 2 * x i ^ 2 by ring, Real.sq_sqrt (hf i)]
  have h3 : (∑ i, (Real.sqrt (f i) * c i) ^ 2) = ∑ i, f i * c i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [show (Real.sqrt (f i) * c i) ^ 2 = Real.sqrt (f i) ^ 2 * c i ^ 2 by ring, Real.sq_sqrt (hf i)]
  rw [h1, h2, h3] at h
  exact h

end Commons.Analysis.InnerProductSpace