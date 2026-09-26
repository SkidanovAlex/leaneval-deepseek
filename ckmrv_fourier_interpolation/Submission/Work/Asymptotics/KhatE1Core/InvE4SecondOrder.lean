import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.KPlus24Refs
import Submission.Work.Asymptotics.KhatE1Core.DKPlusBounds
import Submission.Work.Asymptotics.K24FZ

/-!
# `(E₄ z)⁻¹` to second order at the cusp

`(E₄ z)⁻¹ - (1 - 240q + 55440q²) = O(‖q(z)‖³)` on `Im z ≥ 3`, where `q = qParamFun z`.
This is exactly the deviation `dI4z` of `Sm3Split.lean`; the plan and constants are recorded in
`InvE4Plan.lean`.  The proof is the factorisation `E₄⁻¹ - Q = E₄⁻¹(1 - E₄Q)` together with
`1 - E₄Q = (1 - PQ) - dE₄·Q` (`P = E4Ref z`, `Q = 1-240q+55440q²`) and the explicit
`1 - PQ = q³(-12787200 - 119750400q)`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

theorem InvE4SecondOrder :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 3 ≤ UpperHalfPlane.im z →
      ‖(Work.Kernels.E4Fun z)⁻¹ - (1 - 240 * Work.Kernels.qParamFun z
        + 55440 * (Work.Kernels.qParamFun z) ^ 2)‖
        ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C4, hC4, h4⟩ := dE4_bound
  refine ⟨2 * (132537600 + C4 * 55681) + 1, by positivity, fun z hz => ?_⟩
  set q : ℂ := Work.Kernels.qParamFun z with hqdef
  have hqn : ‖q‖ = Real.exp (-(2 * Real.pi * z.im)) := Work.Asymptotics.norm_qParamFun z
  have hz1 : (1 : ℝ) ≤ z.im := by linarith
  have hq1 : ‖q‖ ≤ 1 := by
    rw [hqn, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hz]
  have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg _
  have hq3n : (0 : ℝ) ≤ ‖q‖ ^ 3 := pow_nonneg hq0 3
  have hE4inv : ‖(Work.Kernels.E4Fun z)⁻¹‖ ≤ 2 :=
    Work.Asymptotics.K24F.E4_inv_le_two_three z hz
  have hE4ne : Work.Kernels.E4Fun z ≠ 0 := Work.Asymptotics.K24F.E4_ne_zero_three z hz
  -- the reference polynomial
  have hQ : (1 : ℂ) - 240 * q + 55440 * q ^ 2
      = 1 - 240 * Work.Kernels.qParamFun z + 55440 * Work.Kernels.qParamFun z ^ 2 := by
    rw [hqdef]
  have hQb : ‖(1 : ℂ) - 240 * q + 55440 * q ^ 2‖ ≤ 55681 := by
    have h2 : ‖(55440 : ℂ) * q ^ 2‖ = 55440 * ‖q‖ ^ 2 := by rw [norm_mul, norm_pow]; norm_num
    have h3 : ‖q‖ ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
    calc ‖(1 : ℂ) - 240 * q + 55440 * q ^ 2‖
        ≤ ‖(1 : ℂ) - 240 * q‖ + ‖(55440 : ℂ) * q ^ 2‖ := norm_add_le _ _
      _ ≤ (1 + 240 * ‖q‖) + 55440 * ‖q‖ ^ 2 := by
          rw [h2]
          have h1 : ‖(1 : ℂ) - 240 * q‖ ≤ 1 + 240 * ‖q‖ := by
            refine le_trans (norm_sub_le _ _) (le_of_eq ?_)
            rw [norm_one, norm_mul]
            norm_num
          linarith
      _ ≤ 55681 := by nlinarith [hq0, hq1, h3]
  -- the product identity
  have hprod : ‖(1 : ℂ) - E4Ref z * (1 - 240 * q + 55440 * q ^ 2)‖
      ≤ 132537600 * ‖q‖ ^ 3 := by
    have hid : (1 : ℂ) - E4Ref z * (1 - 240 * q + 55440 * q ^ 2)
        = q ^ 3 * ((-12787200 : ℂ) - 119750400 * q) := by
      simp only [E4Ref, hqdef]
      ring
    rw [hid, norm_mul, norm_pow]
    have hb : ‖(-12787200 : ℂ) - 119750400 * q‖ ≤ 132537600 := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [show ‖(-12787200 : ℂ)‖ = 12787200 from by norm_num, norm_mul,
        show ‖(119750400 : ℂ)‖ = 119750400 from by norm_num]
      nlinarith [hq0, hq1]
    calc ‖q‖ ^ 3 * ‖(-12787200 : ℂ) - 119750400 * q‖
        ≤ ‖q‖ ^ 3 * 132537600 := mul_le_mul_of_nonneg_left hb (pow_nonneg hq0 3)
      _ = 132537600 * ‖q‖ ^ 3 := by ring
  -- the deviation of E₄
  have hd4 : ‖dE4 z‖ ≤ C4 * ‖q‖ ^ 3 := h4 z hz1
  have hdQ : ‖dE4 z * (1 - 240 * q + 55440 * q ^ 2)‖ ≤ C4 * 55681 * ‖q‖ ^ 3 := by
    rw [norm_mul]
    calc ‖dE4 z‖ * ‖(1 : ℂ) - 240 * q + 55440 * q ^ 2‖
        ≤ (C4 * ‖q‖ ^ 3) * 55681 := mul_le_mul hd4 hQb (norm_nonneg _) (by positivity)
      _ = C4 * 55681 * ‖q‖ ^ 3 := by ring
  -- assembly
  have hsplit : (1 : ℂ) - Work.Kernels.E4Fun z * (1 - 240 * q + 55440 * q ^ 2)
      = ((1 : ℂ) - E4Ref z * (1 - 240 * q + 55440 * q ^ 2))
        - dE4 z * (1 - 240 * q + 55440 * q ^ 2) := by
    simp only [dE4, E4Ref]
    ring
  have hfac : (Work.Kernels.E4Fun z)⁻¹ - (1 - 240 * q + 55440 * q ^ 2)
      = (Work.Kernels.E4Fun z)⁻¹
          * ((1 : ℂ) - Work.Kernels.E4Fun z * (1 - 240 * q + 55440 * q ^ 2)) := by
    rw [mul_sub, mul_one, ← mul_assoc, inv_mul_cancel₀ hE4ne, one_mul]
  have hmain : ‖(1 : ℂ) - Work.Kernels.E4Fun z * (1 - 240 * q + 55440 * q ^ 2)‖
      ≤ 132537600 * ‖q‖ ^ 3 + C4 * 55681 * ‖q‖ ^ 3 := by
    rw [hsplit]
    exact le_trans (norm_sub_le _ _) (by linarith [hprod, hdQ])
  rw [show (1 : ℂ) - 240 * Work.Kernels.qParamFun z + 55440 * Work.Kernels.qParamFun z ^ 2
      = (1 : ℂ) - 240 * q + 55440 * q ^ 2 from by rw [hQ]]
  rw [hfac, norm_mul]
  calc ‖(Work.Kernels.E4Fun z)⁻¹‖
        * ‖(1 : ℂ) - Work.Kernels.E4Fun z * (1 - 240 * q + 55440 * q ^ 2)‖
      ≤ 2 * (132537600 * ‖q‖ ^ 3 + C4 * 55681 * ‖q‖ ^ 3) :=
        mul_le_mul hE4inv hmain (norm_nonneg _) (by norm_num)
    _ = 2 * (132537600 + C4 * 55681) * ‖q‖ ^ 3 := by ring
    _ ≤ (2 * (132537600 + C4 * 55681) + 1) * ‖q‖ ^ 3 := by
        nlinarith [hq3n, hC4.le]

end

end Work.Asymptotics.KhatE1Core
