import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.DKPlusBounds
import Submission.Work.Asymptotics.KhatE1Core.JTheta0Bound

/-!
# `dSm5 = O(‖q(τ)‖⁻¹ · E(z)⁶ · scale^N (1+t)^M)`

`dSm5 = -(dDelta·j(τ))·Θ₀`, so `‖dSm5 τ z‖ = ‖dDelta z‖ · ‖j(τ)·Θ₀(τ,z)‖`, and the two factors
are exactly `dDelta_bound` (`O(‖q(z)‖⁴)`) and `JTheta0Bound` (`O(‖q(τ)‖⁻¹ scale^N (1+t)^M)`).
Since `‖q(z)‖ ≤ 1` on `z.im ≥ 3`, `‖q(z)‖⁴ ≤ ‖q(z)‖³`, so the product lands in the
`Bracket24ExpansionHold` remainder shape `‖q(τ)‖⁻¹·‖E(z)‖⁶` (`‖E(z)‖³ = ‖q(z)‖³`) — the right
socket, not merely "small".  In particular `dSm5` contributes nothing at `E²`.

*Tactic notes for reuse.*  (i) `add_le_add_right h c` produces `c + a ≤ c + b`, i.e. it adds on
the **left** despite the name; use `simpa [add_comm] using add_le_add_right h 1` for
`a + 1 ≤ b + 1`.  (ii) In this context `positivity` fails on products carrying
`(1 + t) ^ M` / `‖q(·)‖ ^ 4`, so every nonnegativity here is supplied by hand
(`mul_nonneg`, `Real.rpow_nonneg`, `pow_nonneg`, `inv_nonneg`).
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- **`dSm5` in the `Bracket24ExpansionHold` remainder shape.** -/
theorem dSm5_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ →
        UpperHalfPlane.im τ + 1 ≤ t →
        0 ≤ UpperHalfPlane.re z → UpperHalfPlane.re z ≤ 1 → UpperHalfPlane.im z = t →
        ‖dSm5 τ z‖
          ≤ C * (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Work.Kernels.qParamFun z‖ ^ 3
              * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨Cd, hCd, hd⟩ := dDelta_bound
  obtain ⟨Cj, Nj, Mj, hCj, hNj, hMj, hj⟩ := JTheta0Bound ℓ
  refine ⟨Cd * Cj, Nj, Mj, mul_pos hCd hCj, hNj, hMj,
    fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h2 : (2 : ℝ) ≤ UpperHalfPlane.im τ := hF.2
  have h3 : UpperHalfPlane.im τ + 1 ≤ UpperHalfPlane.im z := by rw [hzim]; exact ht
  have h4 : (2 : ℝ) + 1 ≤ UpperHalfPlane.im τ + 1 := by
    simpa [add_comm] using add_le_add_right h2 1
  have hz3 : (3 : ℝ) ≤ UpperHalfPlane.im z :=
    le_trans (by norm_num : (3 : ℝ) ≤ 2 + 1) (le_trans h4 h3)
  have hd1 : (1 : ℝ) ≤ UpperHalfPlane.im z :=
    le_trans (by norm_num : (1 : ℝ) ≤ 3) hz3
  have ht3 : (3 : ℝ) ≤ t := by rw [← hzim]; exact hz3
  have htm : (0 : ℝ) ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 3) ht3
  have ht0 : (0 : ℝ) ≤ 1 + t := add_nonneg zero_le_one htm
  have hd' := hd z hd1
  have hj' := hj τ z t hF ht hz0 hz1 hzim
  have hqle : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hz3]
  have hq4 : ‖Work.Kernels.qParamFun z‖ ^ 4 ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    have h0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
    have h48 : ‖Work.Kernels.qParamFun z‖ ^ 4
        = ‖Work.Kernels.qParamFun z‖ ^ 3 * ‖Work.Kernels.qParamFun z‖ := by ring
    rw [h48]
    exact mul_le_of_le_one_right (pow_nonneg h0 3) hqle
  have hnorm : ‖dSm5 τ z‖
      = ‖dDelta z‖
          * ‖Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Th0 τ z‖ := by
    simp only [dSm5, norm_mul, norm_neg]
    ring
  rw [hnorm]
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale τ := (Work.Kernels.scale_pos τ).le
  have hq0 : (0 : ℝ) ≤ (‖Work.Kernels.qParamFun τ‖)⁻¹ :=
    inv_nonneg.mpr (norm_nonneg _)
  have hcof : (0 : ℝ) ≤ Cj * (‖Work.Kernels.qParamFun τ‖)⁻¹
      * (Work.Kernels.scale τ) ^ Nj * (1 + t) ^ Mj :=
    mul_nonneg (mul_nonneg (mul_nonneg hCj.le hq0) (Real.rpow_nonneg hs0 _))
      (Real.rpow_nonneg ht0 _)
  have hA : (0 : ℝ) ≤ Cd * ‖Work.Kernels.qParamFun z‖ ^ 4 :=
    mul_nonneg hCd.le (pow_nonneg (norm_nonneg _) 4)
  have hB : (0 : ℝ) ≤ Cd * ‖Work.Kernels.qParamFun z‖ ^ 3 :=
    mul_nonneg hCd.le (pow_nonneg (norm_nonneg _) 3)
  have h1 : ‖dDelta z‖ * ‖Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Th0 τ z‖
      ≤ (Cd * ‖Work.Kernels.qParamFun z‖ ^ 4)
          * (Cj * (‖Work.Kernels.qParamFun τ‖)⁻¹
              * (Work.Kernels.scale τ) ^ Nj * (1 + t) ^ Mj) :=
    mul_le_mul hd' hj' (norm_nonneg _) hA
  have h2' : (Cd * ‖Work.Kernels.qParamFun z‖ ^ 4)
        * (Cj * (‖Work.Kernels.qParamFun τ‖)⁻¹
            * (Work.Kernels.scale τ) ^ Nj * (1 + t) ^ Mj)
      ≤ (Cd * ‖Work.Kernels.qParamFun z‖ ^ 3)
          * (Cj * (‖Work.Kernels.qParamFun τ‖)⁻¹
              * (Work.Kernels.scale τ) ^ Nj * (1 + t) ^ Mj) := by
    have h5 : Cd * ‖Work.Kernels.qParamFun z‖ ^ 4 ≤ Cd * ‖Work.Kernels.qParamFun z‖ ^ 3 :=
      mul_le_mul_of_nonneg_left hq4 hCd.le
    exact mul_le_mul_of_nonneg_right h5 hcof
  calc ‖dDelta z‖ * ‖Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Th0 τ z‖
      ≤ _ := h1
    _ ≤ _ := h2'
    _ = Cd * Cj * (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Work.Kernels.qParamFun z‖ ^ 3
          * (Work.Kernels.scale τ) ^ Nj * (1 + t) ^ Mj := by ring

end

end Work.Asymptotics.KhatE1Core
