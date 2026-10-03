import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.BoxNorm

theorem sum_pairs_star_eq_normSq {ι : Type*} [Fintype ι] (Φ : ι → ℂ) :
    ∑ a : ι, ∑ b : ι, Φ b * star (Φ a) = ((‖∑ a : ι, Φ a‖ ^ 2 : ℝ) : ℂ) := by
  rw [Finset.sum_comm, ← Finset.sum_mul_sum]
  simp only [Complex.star_def]
  rw [← map_sum (starRingEnd ℂ)]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

end Work.Peluse.BoxNorm
