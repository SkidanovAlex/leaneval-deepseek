import Mathlib.Analysis.Real.Sqrt
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.RPFresh

/-- Elementary square-root comparison: if `x² ≤ K(A² + B² + C²)` and all the quantities
`x, K, A, B, C` are nonnegative, then `x ≤ √K·(A + B + C)`.

The only content is `A² + B² + C² ≤ (A + B + C)²` (valid because `A, B, C ≥ 0`), which lets
us take square roots after writing `x = √(x²)`. -/
theorem le_sqrt_mul_of_sq_le {x K A B C : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (h : x ^ 2 ≤ K * (A ^ 2 + B ^ 2 + C ^ 2)) :
    x ≤ Real.sqrt K * (A + B + C) := by
  have hsum : 0 ≤ A + B + C := by linarith
  have hsq : A ^ 2 + B ^ 2 + C ^ 2 ≤ (A + B + C) ^ 2 := by
    nlinarith [mul_nonneg hA hB, mul_nonneg hB hC, mul_nonneg hA hC]
  have h1 : x ^ 2 ≤ K * (A + B + C) ^ 2 := le_trans h (mul_le_mul_of_nonneg_left hsq hK)
  calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx).symm
    _ ≤ Real.sqrt (K * (A + B + C) ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt K * (A + B + C) := by rw [Real.sqrt_mul hK, Real.sqrt_sq hsum]

theorem HkNorm_le_of_HkSq_le {α : ℝ} {k : ℕ} {f f₁ f₂ f₃ : ℝ → ℝ → ℝ} {K : ℝ}
    (hK : 0 < K) (hα : 0 ≤ α)
    (h : Work.Spaces.HkSq α k f
      ≤ K * (α ^ 4 * Work.Spaces.HkSq α k f₁ + Work.Spaces.HkSq α k f₂
          + α ^ 2 * Work.Spaces.HkSq α k f₃)) :
    Work.Spaces.HkNorm α k f ≤ Real.sqrt K * (α ^ 2 * Work.Spaces.HkNorm α k f₁
      + Work.Spaces.HkNorm α k f₂ + α * Work.Spaces.HkNorm α k f₃) := by
  -- `HkNorm` is the square root of `HkSq`, which is nonnegative.
  have hx : 0 ≤ Work.Spaces.HkNorm α k f := Work.Spaces.HkNorm_nonneg α k f
  have hA : 0 ≤ α ^ 2 * Work.Spaces.HkNorm α k f₁ :=
    mul_nonneg (pow_nonneg hα 2) (Work.Spaces.HkNorm_nonneg α k f₁)
  have hB : 0 ≤ Work.Spaces.HkNorm α k f₂ := Work.Spaces.HkNorm_nonneg α k f₂
  have hC : 0 ≤ α * Work.Spaces.HkNorm α k f₃ :=
    mul_nonneg hα (Work.Spaces.HkNorm_nonneg α k f₃)
  -- the `HkNorm`s are the square roots of the corresponding `HkSq`s
  have hN0 : (Work.Spaces.HkNorm α k f) ^ 2 = Work.Spaces.HkSq α k f :=
    Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k f)
  have hN1 : (Work.Spaces.HkNorm α k f₁) ^ 2 = Work.Spaces.HkSq α k f₁ :=
    Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k f₁)
  have hN2 : (Work.Spaces.HkNorm α k f₂) ^ 2 = Work.Spaces.HkSq α k f₂ :=
    Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k f₂)
  have hN3 : (Work.Spaces.HkNorm α k f₃) ^ 2 = Work.Spaces.HkSq α k f₃ :=
    Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k f₃)
  -- the two sides of the hypothesis agree after renaming the squared norms
  have heq : K * ((α ^ 2 * Work.Spaces.HkNorm α k f₁) ^ 2 + (Work.Spaces.HkNorm α k f₂) ^ 2
        + (α * Work.Spaces.HkNorm α k f₃) ^ 2)
      = K * (α ^ 4 * Work.Spaces.HkSq α k f₁ + Work.Spaces.HkSq α k f₂
          + α ^ 2 * Work.Spaces.HkSq α k f₃) := by
    rw [mul_pow, mul_pow, hN1, hN2, hN3]
    ring
  refine le_sqrt_mul_of_sq_le hx hA hB hC (le_of_lt hK) ?_
  rw [hN0]
  exact le_trans h (le_of_eq heq.symm)

end Work.FTS.EllipticEst.RPFresh
