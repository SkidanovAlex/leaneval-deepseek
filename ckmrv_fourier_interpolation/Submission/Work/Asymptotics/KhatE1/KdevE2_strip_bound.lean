import Mathlib
import Submission.Work.Asymptotics.KhatE1.KdevE2Defs
import Submission.Work.Asymptotics.KhatE1.KdevE2CoeffDefs
import Submission.Work.Asymptotics.KhatE1.B0Defs
import Submission.Work.Asymptotics.KhatE1.KdevE2c2c1_bound
import Submission.Work.Asymptotics.KhatE1.B0_funnel_bound

/-!
# The funnel/strip bound for the `E(z)²`-coefficient `KdevE2`

`KdevE2 ℓ τ z = KdevE2plus ℓ τ z + KdevE2minus ℓ τ z` is the `E(z)²`-coefficient of the funnel
deviation `K̂^{(8)} - 𝒢̂^{(8)}` (`Submission/Work/Asymptotics/KhatE1/KdevE2Defs.lean`).

* `KdevE2_eq_poly` (`KdevE2CoeffDefs.lean`) writes it as a polynomial of degree `2` in `z`,
  `KdevE2c2 τ · z² + KdevE2c1 ℓ τ · z + KdevE2c0 ℓ τ`.
* `KdevE2c2`, `KdevE2c1` are `O((scale τ)^N ‖q(τ)‖)` on the funnel (`KdevE2c2c1_bound`).
* `KdevE2c0` is half of the `z⁰`-coefficient `B0` of the funnel bracket
  (`KdevE2c0_eq` below), which is `O((scale τ)^N ‖q(τ)‖)` on the funnel (`B0_funnel_bound`).

For `z` in the strip `-1 ≤ Re z ≤ 2` with `Im z = t` one has `|z| ≤ 2(1+t)`, so each polynomial
term is dominated by `‖q(τ)‖ (scale τ)^N (1+t)²`, and the stated bound follows.
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- **The `z⁰`-coefficient of `KdevE2` is half of `B0`.** -/
theorem KdevE2c0_eq (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    KdevE2c0 ℓ τ = B0 ℓ τ / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have htC : Work.Asymptotics.Compact.tailC ≠ 0 := Work.Asymptotics.Compact.tailC_ne_zero
  rw [KdevE2c0, B0, Work.Asymptotics.Compact.R8_q1, Work.Asymptotics.Compact.R8_p1,
    Work.Asymptotics.Compact.tailC]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Funnel bound for the `E(z)²`-coefficient `KdevE2` of the deviation**, on the strip
`-1 ≤ Re z ≤ 2` above the funnel. -/
theorem KdevE2_strip_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1.KdevE2 ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨Cc, Nc, hCc, hNc, hc2, hc1⟩ := KdevE2c2c1_bound ℓ
  obtain ⟨C0, N0, hC0, hN0, hB0⟩ := B0_funnel_bound ℓ
  refine ⟨6 * Cc + C0 / 2 + 1, max Nc N0, 2, by positivity, le_max_of_le_left hNc,
    by norm_num, ?_⟩
  intro τ z t hτ ht hzre1 hzre2 hzim
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_trans zero_le_one hs1
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have h1t1 : (1 : ℝ) ≤ 1 + t := by have h := hτ.2; linarith
  have h1t0 : (0 : ℝ) ≤ 1 + t := by linarith
  have hS0 : (0 : ℝ) ≤ Work.Kernels.scale τ ^ (max Nc N0) := Real.rpow_nonneg hs0 _
  have hsN : Work.Kernels.scale τ ^ Nc ≤ Work.Kernels.scale τ ^ (max Nc N0) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
  have hsN0 : Work.Kernels.scale τ ^ N0 ≤ Work.Kernels.scale τ ^ (max Nc N0) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
  have hc2' : ‖KdevE2c2 τ‖ ≤ Cc * Work.Kernels.scale τ ^ (max Nc N0)
      * ‖Work.Kernels.qParamFun τ‖ := by
    refine le_trans (hc2 τ hτ) ?_
    apply mul_le_mul_of_nonneg_right _ hq0
    exact mul_le_mul_of_nonneg_left hsN hCc.le
  have hc1' : ‖KdevE2c1 ℓ τ‖ ≤ Cc * Work.Kernels.scale τ ^ (max Nc N0)
      * ‖Work.Kernels.qParamFun τ‖ := by
    refine le_trans (hc1 τ hτ) ?_
    apply mul_le_mul_of_nonneg_right _ hq0
    exact mul_le_mul_of_nonneg_left hsN hCc.le
  have hB0' : ‖B0 ℓ τ‖ ≤ C0 * Work.Kernels.scale τ ^ (max Nc N0)
      * ‖Work.Kernels.qParamFun τ‖ := by
    refine le_trans (hB0 τ hτ) ?_
    apply mul_le_mul_of_nonneg_right _ hq0
    exact mul_le_mul_of_nonneg_left hsN0 hC0.le
  -- bound for `‖z‖`
  have hz2 : ‖(z : ℂ)‖ ^ 2 ≤ (2 * (1 + t)) ^ 2 := by
    have h1 : ‖(z : ℂ)‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    rw [h1, hzim]
    nlinarith [hzre1, hzre2]
  have hzb : ‖(z : ℂ)‖ ≤ 2 * (1 + t) := by
    nlinarith [hz2, norm_nonneg (z : ℂ), h1t0]
  -- rewrite the target as the `z`-polynomial
  rw [KdevE2_eq_poly ℓ τ z, KdevE2c0_eq ℓ τ]
  have hF0 : (0 : ℝ) ≤ ((1 + t) ^ 2 : ℝ) := by positivity
  have e2 : ‖KdevE2c2 τ * (z : ℂ) ^ 2‖
      ≤ 4 * Cc * (‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ (max Nc N0)
          * (1 + t) ^ 2) := by
    rw [norm_mul, norm_pow]
    calc ‖KdevE2c2 τ‖ * ‖(z : ℂ)‖ ^ 2
        ≤ (Cc * Work.Kernels.scale τ ^ (max Nc N0) * ‖Work.Kernels.qParamFun τ‖)
            * (2 * (1 + t)) ^ 2 :=
          mul_le_mul hc2' (pow_le_pow_left₀ (norm_nonneg _) hzb 2) (by positivity)
            (by positivity)
      _ = 4 * Cc * (‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ (max Nc N0)
            * (1 + t) ^ 2) := by ring
  have e1 : ‖KdevE2c1 ℓ τ * (z : ℂ)‖
      ≤ 2 * Cc * (‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ (max Nc N0)
          * (1 + t) ^ 2) := by
    rw [norm_mul]
    calc ‖KdevE2c1 ℓ τ‖ * ‖(z : ℂ)‖
        ≤ (Cc * Work.Kernels.scale τ ^ (max Nc N0) * ‖Work.Kernels.qParamFun τ‖)
            * (2 * (1 + t)) :=
          mul_le_mul hc1' hzb (norm_nonneg _) (by positivity)
      _ ≤ (Cc * Work.Kernels.scale τ ^ (max Nc N0) * ‖Work.Kernels.qParamFun τ‖)
            * (2 * (1 + t) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [h1t1]
      _ = 2 * Cc * (‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ (max Nc N0)
            * (1 + t) ^ 2) := by ring
  have e0 : ‖B0 ℓ τ / 2‖
      ≤ C0 / 2 * (‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ (max Nc N0)
          * (1 + t) ^ 2) := by
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    calc ‖B0 ℓ τ‖ / 2
        ≤ (C0 * Work.Kernels.scale τ ^ (max Nc N0) * ‖Work.Kernels.qParamFun τ‖) / 2 :=
          div_le_div_of_nonneg_right hB0' (by norm_num)
      _ ≤ (C0 * Work.Kernels.scale τ ^ (max Nc N0) * ‖Work.Kernels.qParamFun τ‖
            * (1 + t) ^ 2) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          have h1sq : (1 : ℝ) ≤ (1 + t) ^ 2 := by nlinarith [h1t1]
          calc C0 * Work.Kernels.scale τ ^ (max Nc N0) * ‖Work.Kernels.qParamFun τ‖
              = C0 * Work.Kernels.scale τ ^ (max Nc N0) * ‖Work.Kernels.qParamFun τ‖ * 1 :=
                by ring
            _ ≤ C0 * Work.Kernels.scale τ ^ (max Nc N0) * ‖Work.Kernels.qParamFun τ‖
                  * (1 + t) ^ 2 :=
                mul_le_mul_of_nonneg_left h1sq (by positivity)
      _ = C0 / 2 * (‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ (max Nc N0)
            * (1 + t) ^ 2) := by ring
  have hG0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ (max Nc N0)
      * (1 + t) ^ 2 := mul_nonneg (mul_nonneg hq0 hS0) hF0
  have htri : ‖KdevE2c2 τ * (z : ℂ) ^ 2 + KdevE2c1 ℓ τ * (z : ℂ) + B0 ℓ τ / 2‖
      ≤ ‖KdevE2c2 τ * (z : ℂ) ^ 2‖ + ‖KdevE2c1 ℓ τ * (z : ℂ)‖ + ‖B0 ℓ τ / 2‖ := by
    have h1 := norm_add_le (KdevE2c2 τ * (z : ℂ) ^ 2 + KdevE2c1 ℓ τ * (z : ℂ)) (B0 ℓ τ / 2)
    have h2 := norm_add_le (KdevE2c2 τ * (z : ℂ) ^ 2) (KdevE2c1 ℓ τ * (z : ℂ))
    linarith
  have hsum : ‖KdevE2c2 τ * (z : ℂ) ^ 2 + KdevE2c1 ℓ τ * (z : ℂ) + B0 ℓ τ / 2‖
      ≤ (6 * Cc + C0 / 2 + 1) * (‖Work.Kernels.qParamFun τ‖
          * Work.Kernels.scale τ ^ (max Nc N0) * (1 + t) ^ 2) := by
    refine le_trans htri ?_
    have h2 : ‖KdevE2c2 τ * (z : ℂ) ^ 2‖ + ‖KdevE2c1 ℓ τ * (z : ℂ)‖ + ‖B0 ℓ τ / 2‖
        ≤ 4 * Cc * (‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ (max Nc N0)
              * (1 + t) ^ 2)
          + 2 * Cc * (‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ (max Nc N0)
              * (1 + t) ^ 2)
          + C0 / 2 * (‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ (max Nc N0)
              * (1 + t) ^ 2) := by
      linarith [e2, e1, e0]
    refine le_trans h2 ?_
    have h3 : 4 * Cc * (‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ (max Nc N0)
            * (1 + t) ^ 2)
          + 2 * Cc * (‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ (max Nc N0)
            * (1 + t) ^ 2)
          + C0 / 2 * (‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ (max Nc N0)
            * (1 + t) ^ 2)
        = (6 * Cc + C0 / 2) * (‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ (max Nc N0)
            * (1 + t) ^ 2) := by
      ring
    rw [h3]
    apply mul_le_mul_of_nonneg_right _ hG0
    linarith
  refine le_trans hsum (le_of_eq ?_)
  rw [Real.rpow_two]
  ring

end

end Work.Asymptotics.KhatE1
