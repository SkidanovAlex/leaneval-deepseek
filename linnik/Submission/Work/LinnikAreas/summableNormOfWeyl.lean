import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace Work.LinnikAreas

theorem summableNormOfWeyl (z : ℕ → ℂ) (hz : z 0 ≠ 0)
    (hle : ∀ n : ℕ, ‖z n‖ ≤ ‖z 0‖)
    (hsum : Summable fun n : ℕ => ‖z n‖ / (‖z 0‖ + ‖z n‖)) :
    Summable fun n : ℕ => ‖z n‖ := by
  have hc : 0 < ‖z 0‖ := norm_pos_iff.mpr hz
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (hsum.mul_left (2 * ‖z 0‖))
  have hden : 0 < ‖z 0‖ + ‖z n‖ := by positivity
  have hmono : ‖z n‖ / (2 * ‖z 0‖) ≤ ‖z n‖ / (‖z 0‖ + ‖z n‖) :=
    div_le_div_of_nonneg_left (norm_nonneg _) hden (by linarith [hle n])
  calc ‖z n‖ = 2 * ‖z 0‖ * (‖z n‖ / (2 * ‖z 0‖)) := by
        rw [mul_div_cancel₀]; linarith
    _ ≤ 2 * ‖z 0‖ * (‖z n‖ / (‖z 0‖ + ‖z n‖)) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)

end Work.LinnikAreas
