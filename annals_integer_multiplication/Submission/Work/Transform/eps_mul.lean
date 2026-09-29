import Mathlib

namespace Work.Transform

/-- Lemma 2.9 specialised to pointwise products: if `A ≈ a` with scaled error `< η`, `B ≈ b`
with scaled error `< e` (scaled = multiplied by `2^p`), `‖B i‖ ≤ 1`, `‖a i‖ ≤ 1`, and the
computed product `C` satisfies `2^p ‖C i - A i * B i‖ < 2`, then `2^p‖C i - a i * b i‖ < η+e+2`. -/
theorem eps_mul {ι : Type*} {p : ℕ} (A B C a b : ι → ℂ) (η e : ℝ)
    (hB : ∀ i, ‖B i‖ ≤ 1) (ha : ∀ i, ‖a i‖ ≤ 1)
    (hη : ∀ i, (2 : ℝ) ^ p * ‖A i - a i‖ < η)
    (he : ∀ i, (2 : ℝ) ^ p * ‖B i - b i‖ < e)
    (hm : ∀ i, (2 : ℝ) ^ p * ‖C i - A i * B i‖ < 2) :
    ∀ i, (2 : ℝ) ^ p * ‖C i - a i * b i‖ < η + e + 2 := by
  intro i
  have ht : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have htle : (0 : ℝ) ≤ (2 : ℝ) ^ p := le_of_lt ht
  -- bound on the cross term `(A i - a i) * B i`
  have h2 : (2 : ℝ) ^ p * ‖(A i - a i) * B i‖ ≤ (2 : ℝ) ^ p * ‖A i - a i‖ := by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ htle
    calc ‖A i - a i‖ * ‖B i‖ ≤ ‖A i - a i‖ * 1 :=
          mul_le_mul_of_nonneg_left (hB i) (norm_nonneg _)
      _ = ‖A i - a i‖ := mul_one _
  -- bound on the cross term `a i * (B i - b i)`
  have h3 : (2 : ℝ) ^ p * ‖a i * (B i - b i)‖ ≤ (2 : ℝ) ^ p * ‖B i - b i‖ := by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ htle
    calc ‖a i‖ * ‖B i - b i‖ ≤ 1 * ‖B i - b i‖ :=
          mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _)
      _ = ‖B i - b i‖ := one_mul _
  have h2' : (2 : ℝ) ^ p * ‖(A i - a i) * B i‖ < η := lt_of_le_of_lt h2 (hη i)
  have h3' : (2 : ℝ) ^ p * ‖a i * (B i - b i)‖ < e := lt_of_le_of_lt h3 (he i)
  have hdec : C i - a i * b i
      = (C i - A i * B i) + ((A i - a i) * B i + a i * (B i - b i)) := by ring
  calc (2 : ℝ) ^ p * ‖C i - a i * b i‖
      = (2 : ℝ) ^ p
          * ‖(C i - A i * B i) + ((A i - a i) * B i + a i * (B i - b i))‖ := by rw [hdec]
    _ ≤ (2 : ℝ) ^ p
          * (‖C i - A i * B i‖ + (‖(A i - a i) * B i‖ + ‖a i * (B i - b i)‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ htle
        calc ‖(C i - A i * B i) + ((A i - a i) * B i + a i * (B i - b i))‖
            ≤ ‖C i - A i * B i‖ + ‖(A i - a i) * B i + a i * (B i - b i)‖ :=
              norm_add_le _ _
          _ ≤ ‖C i - A i * B i‖ + (‖(A i - a i) * B i‖ + ‖a i * (B i - b i)‖) := by
              have := norm_add_le ((A i - a i) * B i) (a i * (B i - b i))
              linarith
    _ = (2 : ℝ) ^ p * ‖C i - A i * B i‖ + (2 : ℝ) ^ p * ‖(A i - a i) * B i‖
          + (2 : ℝ) ^ p * ‖a i * (B i - b i)‖ := by ring
    _ < η + e + 2 := by linarith [hm i, h2', h3']

end Work.Transform
