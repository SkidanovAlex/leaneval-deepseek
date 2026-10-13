import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

theorem iteratedDeriv_mul_sq_le (m : ℕ) (f g : ℝ → ℝ) (x : ℝ) (B : ℕ → ℝ)
    (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g x)
    (hB : ∀ k, k ≤ m → |iteratedDeriv k g x| ≤ B k) :
    (iteratedDeriv m (f * g) x) ^ 2 ≤
      (∑ j ∈ Finset.range (m + 1), (m.choose j * B (m - j)) ^ 2) *
        ∑ j ∈ Finset.range (m + 1), (iteratedDeriv j f x) ^ 2 := by
  -- From the hypothesis, `B k ≥ 0` on `k ≤ m` (the absolute value it dominates is nonnegative).
  have hBnn : ∀ k, k ≤ m → 0 ≤ B k := fun k hk => (abs_nonneg _).trans (hB k hk)
  -- Leibniz's rule for the `m`-th derivative of a product.
  have hder : iteratedDeriv m (f * g) x =
      ∑ i ∈ Finset.range (m + 1),
        m.choose i * iteratedDeriv i f x * iteratedDeriv (m - i) g x :=
    iteratedDeriv_mul hf hg
  -- Bound the absolute value of the Leibniz sum by the corresponding sum of absolute values.
  have hbd : |iteratedDeriv m (f * g) x| ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i * B (m - i)) * |iteratedDeriv i f x| := by
    rw [hder]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun i hi => ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (m.choose i))]
    have h1 : |iteratedDeriv (m - i) g x| ≤ B (m - i) := hB (m - i) (Nat.sub_le _ _)
    calc (m.choose i : ℝ) * |iteratedDeriv i f x| * |iteratedDeriv (m - i) g x|
        ≤ (m.choose i : ℝ) * |iteratedDeriv i f x| * B (m - i) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
      _ = (m.choose i * B (m - i)) * |iteratedDeriv i f x| := by ring
  -- Square and apply the Cauchy–Schwarz inequality for finsets.
  calc (iteratedDeriv m (f * g) x) ^ 2
      = |iteratedDeriv m (f * g) x| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ i ∈ Finset.range (m + 1), (m.choose i * B (m - i)) * |iteratedDeriv i f x|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hbd 2
    _ ≤ (∑ i ∈ Finset.range (m + 1), (m.choose i * B (m - i)) ^ 2) *
        ∑ i ∈ Finset.range (m + 1), |iteratedDeriv i f x| ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ j ∈ Finset.range (m + 1), (m.choose j * B (m - j)) ^ 2) *
        ∑ j ∈ Finset.range (m + 1), (iteratedDeriv j f x) ^ 2 := by
        simp_rw [sq_abs]

end Work.FTS.EllipticEst.remov
