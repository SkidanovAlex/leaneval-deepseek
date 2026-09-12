import Mathlib

open scoped BigOperators

namespace Submission
namespace EstGeom

/-- Finite geometric tail: for `0 ≤ ρ ≤ 1/2`, `Σ_{k=1}^n ρ^k ≤ 2ρ`. -/
theorem geom_Icc_le_two_mul {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, ρ ^ k) ≤ 2 * ρ := by
  have hρ1 : ρ < 1 := by linarith
  have h1m0 : 0 < 1 - ρ := by linarith
  have hI : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext k
    simp [Nat.succ_le_iff]
  have hsum : (∑ k ∈ Finset.Icc 1 n, ρ ^ k) = (ρ - ρ ^ (n + 1)) / (1 - ρ) := by
    rw [hI]
    rw [geom_sum_Ico' (ne_of_lt hρ1) (by omega : 1 ≤ n + 1)]
    ring_nf
  calc
    (∑ k ∈ Finset.Icc 1 n, ρ ^ k) = (ρ - ρ ^ (n + 1)) / (1 - ρ) := hsum
    _ ≤ ρ / (1 - ρ) := by
      apply div_le_div_of_nonneg_right
      · linarith [pow_nonneg hρ0 (n + 1)]
      · exact h1m0.le
    _ ≤ 2 * ρ := by
      rw [div_le_iff₀ h1m0]
      nlinarith

end EstGeom
end Submission
