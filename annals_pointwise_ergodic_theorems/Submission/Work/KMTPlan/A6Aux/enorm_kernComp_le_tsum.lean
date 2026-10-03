import Mathlib
import Submission.Work.KMTAreas.A7.ModelOps

namespace Work.KMTPlan.A6Aux

open scoped ENNReal

/-- The `ℝ≥0∞`-valued triangle inequality for the composed kernel `kernComp`:
`‖kernComp K κ κ' a b‖ₑ ≤ ∑'_{z : ℤ × ℤ} ‖K (a - z.1) (b - z.2)‖ₑ * (‖κ z.1‖ₑ * ‖κ' z.2‖ₑ)`.

No summability hypothesis is needed: the right-hand side is the (always defined) `ℝ≥0∞`-valued
`tsum`, which is the supremum of the finite partial sums, and the inequality is the two-fold
triangle inequality for that `tsum` (`enorm_tsum_le_tsum_enorm`, applied once for each of the two
sums defining `kernComp`), followed by `enorm_mul` and the identification of the iterated sum with
the sum over `ℤ × ℤ` (`ENNReal.tsum_prod'`). -/
theorem enorm_kernComp_le_tsum {K : ℤ → ℤ → ℂ} {κ κ' : ℤ → ℂ} (a b : ℤ) :
    ‖Work.KMTAreas.A7.kernComp K κ κ' a b‖ₑ
      ≤ ∑' z : ℤ × ℤ, ‖K (a - z.1) (b - z.2)‖ₑ * (‖κ z.1‖ₑ * ‖κ' z.2‖ₑ) := by
  rw [Work.KMTAreas.A7.kernComp]
  calc ‖∑' a' : ℤ, ∑' b' : ℤ, K (a - a') (b - b') * κ a' * κ' b'‖ₑ
      ≤ ∑' a' : ℤ, ‖∑' b' : ℤ, K (a - a') (b - b') * κ a' * κ' b'‖ₑ :=
        enorm_tsum_le_tsum_enorm
    _ ≤ ∑' a' : ℤ, ∑' b' : ℤ, ‖K (a - a') (b - b') * κ a' * κ' b'‖ₑ :=
        ENNReal.tsum_le_tsum fun a' => enorm_tsum_le_tsum_enorm
    _ = ∑' a' : ℤ, ∑' b' : ℤ, ‖K (a - a') (b - b')‖ₑ * (‖κ a'‖ₑ * ‖κ' b'‖ₑ) := by
        refine tsum_congr fun a' => tsum_congr fun b' => ?_
        rw [enorm_mul, enorm_mul, mul_assoc]
    _ = ∑' z : ℤ × ℤ, ‖K (a - z.1) (b - z.2)‖ₑ * (‖κ z.1‖ₑ * ‖κ' z.2‖ₑ) :=
        (ENNReal.tsum_prod' (f := fun z : ℤ × ℤ =>
          ‖K (a - z.1) (b - z.2)‖ₑ * (‖κ z.1‖ₑ * ‖κ' z.2‖ₑ))).symm

end Work.KMTPlan.A6Aux
