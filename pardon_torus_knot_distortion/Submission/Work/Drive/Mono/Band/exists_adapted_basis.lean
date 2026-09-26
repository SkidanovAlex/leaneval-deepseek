import Mathlib
import Submission.Work.Drive.Mono.BoxWidth
import Submission.Work.Drive.Mono.Band.BadFaceDefs

namespace Work.Drive.Mono.Band

open LeanEval.KnotTheory.PardonDistortion
open Work.Drive.Generic

noncomputable section

/-- **The adapted orthonormal basis of `v^⊥`.**  For orthonormal `v, n` there is an orthonormal pair
`a₀, b₀` of `v^⊥` with `n = (√2)⁻¹ • (a₀ + b₀)` — i.e. `n` is the direction of *projective
coordinate* `1` in that basis, so that the parameter `τ = 1` below corresponds to the given good
direction `n`.

Take `w := v ⨯ n` (a unit vector in `v^⊥`, orthogonal to `n`, by `norm_crossE`,
`inner_crossE_left`, `inner_crossE_right` — all in `BadFaceDefs.lean`), then
`a₀ := (√2)⁻¹ • (n + w)`, `b₀ := (√2)⁻¹ • (n - w)`.  Uses `norm_add_sq_real`, `norm_sub_sq_real`,
`inner_add_left`, `inner_add_right`, `inner_sub_left`, `inner_sub_right`, `real_inner_smul_left`,
`real_inner_smul_right`, `real_inner_self_eq_norm_sq`, `Real.sq_sqrt`. -/
theorem exists_adapted_basis {v n : LeanEval.KnotTheory.PardonDistortion.R3}
    (hv : ‖v‖ = 1) (hn : ‖n‖ = 1) (hvn : inner ℝ v n = 0) :
    ∃ a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3,
      ‖a₀‖ = 1 ∧ ‖b₀‖ = 1 ∧ inner ℝ a₀ b₀ = 0 ∧ inner ℝ v a₀ = 0 ∧
      inner ℝ v b₀ = 0 ∧ n = (Real.sqrt 2)⁻¹ • (a₀ + b₀) := by
  set w := crossE v n with hw
  have hwn : ‖w‖ = 1 := by rw [hw]; exact norm_crossE hv hn hvn
  have hv_w : inner ℝ v w = 0 := by rw [hw]; exact inner_crossE_left v n
  have hn_w : inner ℝ n w = 0 := by rw [hw]; exact inner_crossE_right v n
  have hw_n : inner ℝ w n = 0 := by rw [real_inner_comm]; exact hn_w
  have hs2_add : ‖n + w‖ ^ 2 = 2 := by
    rw [norm_add_sq_real, hn, hwn, hn_w]; norm_num
  have hs2_sub : ‖n - w‖ ^ 2 = 2 := by
    rw [norm_sub_sq_real, hn, hwn, hn_w]; norm_num
  have hinner_pm : inner ℝ (n + w) (n - w) = 0 := by
    rw [inner_add_left, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq, hn,
        real_inner_self_eq_norm_sq, hwn, hn_w, hw_n]
    norm_num
  have hnorm_of_nonneg : ‖(Real.sqrt 2)⁻¹‖ = (Real.sqrt 2)⁻¹ := by
    rw [Real.norm_of_nonneg]; positivity
  refine ⟨(Real.sqrt 2)⁻¹ • (n + w), (Real.sqrt 2)⁻¹ • (n - w), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hsq : ‖(Real.sqrt 2)⁻¹ • (n + w)‖ ^ 2 = 1 := by
      rw [norm_smul, hnorm_of_nonneg, mul_pow, inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
        hs2_add]
      norm_num
    rw [← Real.sqrt_sq (norm_nonneg ((Real.sqrt 2)⁻¹ • (n + w))), hsq, Real.sqrt_one]
  · have hsq : ‖(Real.sqrt 2)⁻¹ • (n - w)‖ ^ 2 = 1 := by
      rw [norm_smul, hnorm_of_nonneg, mul_pow, inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
        hs2_sub]
      norm_num
    rw [← Real.sqrt_sq (norm_nonneg ((Real.sqrt 2)⁻¹ • (n - w))), hsq, Real.sqrt_one]
  · rw [real_inner_smul_left, real_inner_smul_right, hinner_pm]; ring
  · rw [real_inner_smul_right, inner_add_right, hvn, hv_w, add_zero, mul_zero]
  · rw [real_inner_smul_right, inner_sub_right, hvn, hv_w, sub_zero, mul_zero]
  · rw [← smul_add, smul_smul]
    have hab : (n + w) + (n - w) = n + n := by abel
    have hcoef : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * 2 = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [hab, ← two_smul ℝ n, smul_smul, hcoef, one_smul]

end

end Work.Drive.Mono.Band
