import Mathlib
import Submission.Work.BMF.Psi1_local_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `blkCount_mul_blkBound_le`

Chebyshev's bound `blkCount k ≤ Cb * 2^k / k` combined with the explicit pointwise
bound `blkBound α j k` for the block summand collapses to the decaying series term
`serTerm α j k`: the factor `(2^k/k) * (k * log 2) * 2^(-k)` is exactly `log 2`.

Concretely, writing `E = exp (-(log 2)^2 * max 0 (|j - k| - 1)^2)`,

`(Cb * 2^k / k) * blkBound α j k
   = Cb * 2^k / k * (4 * (k * log 2) * 2^(-k) * 2^(-k*α) * E)
   = 4 * Cb * log 2 * (2^k * 2^(-k)) * (k / k) * (2^(-k*α) * E)
   = 4 * Cb * log 2 * serTerm α j k`,

using `2^k * 2^(-k) = 1` (rpow) and `k / k = 1` for `k ≥ 1`.
-/

namespace Work.BMF

open Real

/-- The normalised factor `(2^k / k) * (k * log 2) * 2^(-k)` of the block bound equals `log 2`. -/
lemma two_pow_div_mul_mul_rpow_neg (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) ^ k / (k : ℝ) * ((k : ℝ) * Real.log 2) * (2 : ℝ) ^ (-(k : ℝ)) = Real.log 2 := by
  rw [← Real.rpow_natCast (2 : ℝ) k]
  have hp : (2 : ℝ) ^ (k : ℝ) * 2 ^ (-(k : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring_nf
    simp
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  field_simp
  exact hp

theorem blkCount_mul_blkBound_le (Cb α : ℝ) (hCb : 0 < Cb) (hα0 : 0 < α)
    (hcount : ∀ k : ℕ, 1 ≤ k → Work.BMF.blkCount k ≤ Cb * (2 : ℝ) ^ k / (k : ℝ))
    (j k : ℕ) (hk : 1 ≤ k) :
    Work.BMF.blkCount k * Work.BMF.blkBound α j k ≤
      4 * Cb * Real.log 2 * Work.BMF.serTerm α j k := by
  have _hCb := hCb
  have _hα0 := hα0
  have hBnn : 0 ≤ Work.BMF.blkBound α j k := Work.BMF.blkBound_nonneg α j k
  refine le_trans (mul_le_mul_of_nonneg_right (hcount k hk) hBnn) ?_
  have key : (Cb * (2 : ℝ) ^ k / (k : ℝ)) * Work.BMF.blkBound α j k =
      4 * Cb * Real.log 2 * Work.BMF.serTerm α j k := by
    rw [Work.BMF.blkBound, Work.BMF.serTerm]
    have hp : (2 : ℝ) ^ k / (k : ℝ) * ((k : ℝ) * Real.log 2) * (2 : ℝ) ^ (-(k : ℝ))
        = Real.log 2 := two_pow_div_mul_mul_rpow_neg k hk
    calc (Cb * (2 : ℝ) ^ k / (k : ℝ)) *
          (4 * ((k : ℝ) * Real.log 2) * (2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ (-(k : ℝ) * α) *
            Real.exp (-(Real.log 2) ^ 2 * (max 0 (|(j : ℝ) - (k : ℝ)| - 1)) ^ 2))
        = 4 * Cb *
            ((2 : ℝ) ^ k / (k : ℝ) * ((k : ℝ) * Real.log 2) * (2 : ℝ) ^ (-(k : ℝ))) *
            ((2 : ℝ) ^ (-(k : ℝ) * α) *
              Real.exp (-(Real.log 2) ^ 2 * (max 0 (|(j : ℝ) - (k : ℝ)| - 1)) ^ 2)) := by
          ring
      _ = 4 * Cb * Real.log 2 *
            ((2 : ℝ) ^ (-(k : ℝ) * α) *
              Real.exp (-(Real.log 2) ^ 2 * (max 0 (|(j : ℝ) - (k : ℝ)| - 1)) ^ 2)) := by
          rw [hp]
      _ = 4 * Cb * Real.log 2 *
            (2 ^ (-(k : ℝ) * α) *
              Real.exp (-(Real.log 2) ^ 2 * (max 0 (|(j : ℝ) - (k : ℝ)| - 1)) ^ 2)) := rfl
  rw [key]

end Work.BMF
