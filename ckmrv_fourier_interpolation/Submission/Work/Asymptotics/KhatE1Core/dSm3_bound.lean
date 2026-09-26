import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Sm3Split
import Submission.Work.Asymptotics.KhatE1Core.InvE4SecondOrder
import Submission.Work.Asymptotics.KhatE1Core.DSm4Bound
import Submission.Work.Asymptotics.K24FZ
import Submission.Work.Asymptotics.K24FBase

/-!
# `dSm3 = O(‖q(τ)‖⁻¹ ‖q(z)‖³)`

`dSm3 = 3456·R₀(τ)·(dE4c·S0(z) − (dE6·E₂ˢ·E₄(z)⁻¹ + E6Ref·dE2S·E₄(z)⁻¹ + E6Ref·E2SRef·dI4z))`
with every deviation `O(‖q(z)‖³)` and every cofactor bounded on the funnel strip, and
`‖R₀(τ)‖ ≤ C scale τ`.  This is one of the five plus-side deviation rows.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

theorem dSm3_bound :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.dSm3 τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨Cr, hCr, hr⟩ := Work.Asymptotics.K24F.tau_atom_bounds
  obtain ⟨Cc, hCc, hc⟩ := dE4c_bound
  obtain ⟨C6, hC6, h6⟩ := dE6_bound
  obtain ⟨C2, hC2, h2⟩ := dE2S_bound
  obtain ⟨Ci, hCi, hi⟩ := InvE4SecondOrder
  refine ⟨3456 * Cr * (3 * Cc + (2 * C6 * (99 + C2) + 2 * 17137 * C2 + 17137 * 99 * Ci)) + 1,
    1, 0, by positivity, by norm_num, le_rfl, ?_⟩
  intro τ z t hF ht hz0 hz1 hzim
  have ht3 : (3 : ℝ) ≤ t := by have h2 := hF.2; linarith
  have hz3 : (3 : ℝ) ≤ z.im := by rw [hzim]; exact ht3
  have hz1' : (1 : ℝ) ≤ z.im := by linarith
  set q : ℂ := Work.Kernels.qParamFun z with hqdef
  have hqn : ‖q‖ = Real.exp (-(2 * Real.pi * z.im)) := by
    rw [hqdef]; exact Work.Asymptotics.norm_qParamFun z
  have hq1 : ‖q‖ ≤ 1 := by
    rw [hqn, Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hz3]
  have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg _
  have hq3n : (0 : ℝ) ≤ ‖q‖ ^ 3 := pow_nonneg hq0 3
  have hq3le : ‖q‖ ^ 3 ≤ 1 := pow_le_one₀ hq0 hq1
  have hR0 : ‖Work.Asymptotics.K24F.R0 τ‖ ≤ Cr * Work.Kernels.scale τ := (hr τ hF).2.2.1
  have hsc0 : (0 : ℝ) ≤ Work.Kernels.scale τ := (Work.Kernels.scale_pos τ).le
  have hc' : ‖dE4c z‖ ≤ Cc * ‖q‖ ^ 3 := hc z hz1'
  have h6' : ‖dE6 z‖ ≤ C6 * ‖q‖ ^ 3 := h6 z hz1'
  have h2' : ‖dE2S z‖ ≤ C2 * ‖q‖ ^ 3 := h2 z hz1'
  have hS0 : ‖Work.Asymptotics.K24F.S0 z‖ ≤ 3 := Work.Asymptotics.K24F.zS0_norm z hz1'
  have hE2SRef : ‖E2SRef z‖ ≤ 99 := norm_E2SRef_le hz1'
  have hE2S : ‖Work.Kernels.E2S z‖ ≤ 99 + C2 := by
    have he : Work.Kernels.E2S z = E2SRef z + dE2S z := E2S_ref_split z
    rw [he]
    refine le_trans (norm_add_le _ _) ?_
    nlinarith [hE2SRef, h2', hq0, hq1, hq3le, hC2.le]
  have hE4inv : ‖(Work.Kernels.E4Fun z)⁻¹‖ ≤ 2 :=
    Work.Asymptotics.K24F.E4_inv_le_two_three z hz3
  have hI4z : ‖dI4z z‖ ≤ Ci * ‖q‖ ^ 3 := by
    have he : dI4z z = (Work.Kernels.E4Fun z)⁻¹
        - (1 - 240 * Work.Kernels.qParamFun z + 55440 * Work.Kernels.qParamFun z ^ 2) := by
      simp only [dI4z, I4zRef]
    rw [he]
    exact hi z hz3
  have hE6Ref : ‖E6Ref z‖ ≤ 17137 := by
    have he : E6Ref z = 1 - 504 * q - 16632 * q ^ 2 := by simp only [E6Ref, hqdef]
    rw [he]
    have hb : ‖(16632 : ℂ) * q ^ 2‖ = 16632 * ‖q‖ ^ 2 := by rw [norm_mul, norm_pow]; norm_num
    have hb2 : ‖(504 : ℂ) * q‖ = 504 * ‖q‖ := by rw [norm_mul]; norm_num
    have hq2 : ‖q‖ ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
    calc ‖(1 : ℂ) - 504 * q - 16632 * q ^ 2‖
        ≤ ‖(1 : ℂ) - 504 * q‖ + ‖(16632 : ℂ) * q ^ 2‖ := norm_sub_le _ _
      _ ≤ (1 + 504 * ‖q‖) + 16632 * ‖q‖ ^ 2 := by
          rw [hb]
          have h1 : ‖(1 : ℂ) - 504 * q‖ ≤ 1 + 504 * ‖q‖ := by
            refine le_trans (norm_sub_le _ _) (le_of_eq ?_)
            rw [norm_one, hb2]
          linarith
      _ ≤ 17137 := by nlinarith [hq0, hq1, hq2]
  -- local abbreviations for the four pieces of the bracket
  set A : ℂ := dE4c z * Work.Asymptotics.K24F.S0 z with hAdef
  set B : ℂ := dE6 z * Work.Kernels.E2S z * (Work.Kernels.E4Fun z)⁻¹ with hBdef
  set C : ℂ := E6Ref z * dE2S z * (Work.Kernels.E4Fun z)⁻¹ with hCdef
  set D : ℂ := E6Ref z * E2SRef z * dI4z z with hDdef
  have ht1 : ‖A‖ ≤ 3 * Cc * ‖q‖ ^ 3 := by
    rw [hAdef, norm_mul]
    calc ‖dE4c z‖ * ‖Work.Asymptotics.K24F.S0 z‖ ≤ (Cc * ‖q‖ ^ 3) * 3 :=
          mul_le_mul hc' hS0 (norm_nonneg _) (by positivity)
      _ = 3 * Cc * ‖q‖ ^ 3 := by ring
  have ht2 : ‖B‖ ≤ 2 * C6 * (99 + C2) * ‖q‖ ^ 3 := by
    rw [hBdef, norm_mul, norm_mul]
    calc (‖dE6 z‖ * ‖Work.Kernels.E2S z‖) * ‖(Work.Kernels.E4Fun z)⁻¹‖
        ≤ ((C6 * ‖q‖ ^ 3) * (99 + C2)) * 2 :=
          mul_le_mul (mul_le_mul h6' hE2S (norm_nonneg _) (by positivity)) hE4inv
            (norm_nonneg _) (by positivity)
      _ = 2 * C6 * (99 + C2) * ‖q‖ ^ 3 := by ring
  have ht3 : ‖C‖ ≤ 2 * 17137 * C2 * ‖q‖ ^ 3 := by
    rw [hCdef, norm_mul, norm_mul]
    calc (‖E6Ref z‖ * ‖dE2S z‖) * ‖(Work.Kernels.E4Fun z)⁻¹‖
        ≤ (17137 * (C2 * ‖q‖ ^ 3)) * 2 :=
          mul_le_mul (mul_le_mul hE6Ref h2' (norm_nonneg _) (by positivity)) hE4inv
            (norm_nonneg _) (by positivity)
      _ = 2 * 17137 * C2 * ‖q‖ ^ 3 := by ring
  have ht4 : ‖D‖ ≤ 17137 * 99 * Ci * ‖q‖ ^ 3 := by
    rw [hDdef, norm_mul, norm_mul]
    calc (‖E6Ref z‖ * ‖E2SRef z‖) * ‖dI4z z‖ ≤ (17137 * 99) * (Ci * ‖q‖ ^ 3) :=
          mul_le_mul (mul_le_mul hE6Ref hE2SRef (norm_nonneg _) (by positivity)) hI4z
            (norm_nonneg _) (by positivity)
      _ = 17137 * 99 * Ci * ‖q‖ ^ 3 := by ring
  have hX : ‖B + C + D‖ ≤ 2 * C6 * (99 + C2) * ‖q‖ ^ 3
        + (2 * 17137 * C2 * ‖q‖ ^ 3 + 17137 * 99 * Ci * ‖q‖ ^ 3) := by
    have h1 := norm_add_le (B + C) D
    have h2b := norm_add_le B C
    linarith [h1, h2b, ht2, ht3, ht4]
  have hbr : ‖A - (B + C + D)‖
      ≤ (3 * Cc + (2 * C6 * (99 + C2) + 2 * 17137 * C2 + 17137 * 99 * Ci)) * ‖q‖ ^ 3 := by
    refine le_trans (norm_sub_le A (B + C + D)) ?_
    have hK : 3 * Cc * ‖q‖ ^ 3
          + (2 * C6 * (99 + C2) * ‖q‖ ^ 3
              + (2 * 17137 * C2 * ‖q‖ ^ 3 + 17137 * 99 * Ci * ‖q‖ ^ 3))
        = (3 * Cc + (2 * C6 * (99 + C2) + 2 * 17137 * C2 + 17137 * 99 * Ci)) * ‖q‖ ^ 3 := by
      ring
    have hall := add_le_add ht1 hX
    rw [hK] at hall
    exact hall
  have hmain : ‖Work.Asymptotics.KhatE1Core.dSm3 τ z‖
      ≤ 3456 * Cr * (3 * Cc + (2 * C6 * (99 + C2) + 2 * 17137 * C2 + 17137 * 99 * Ci))
          * Work.Kernels.scale τ * ‖q‖ ^ 3 := by
    have he : Work.Asymptotics.KhatE1Core.dSm3 τ z
        = 3456 * Work.Asymptotics.K24F.R0 τ * (A - (B + C + D)) := by
      simp only [Work.Asymptotics.KhatE1Core.dSm3, hAdef, hBdef, hCdef, hDdef]
    rw [he, norm_mul, norm_mul]
    have hb : ‖(3456 : ℂ)‖ = 3456 := by norm_num
    rw [hb]
    have hstep : (3456 : ℝ) * ‖Work.Asymptotics.K24F.R0 τ‖ * ‖A - (B + C + D)‖
        ≤ 3456 * (Cr * Work.Kernels.scale τ)
          * ((3 * Cc + (2 * C6 * (99 + C2) + 2 * 17137 * C2 + 17137 * 99 * Ci)) * ‖q‖ ^ 3) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hR0 (by norm_num)) hbr (norm_nonneg _) (by positivity)
    have hfin : 3456 * (Cr * Work.Kernels.scale τ)
          * ((3 * Cc + (2 * C6 * (99 + C2) + 2 * 17137 * C2 + 17137 * 99 * Ci)) * ‖q‖ ^ 3)
        = 3456 * Cr * (3 * Cc + (2 * C6 * (99 + C2) + 2 * 17137 * C2 + 17137 * 99 * Ci))
            * Work.Kernels.scale τ * ‖q‖ ^ 3 := by ring
    linarith [hstep, hfin.ge, hfin.le]
  have hqtpos : (0 : ℝ) < ‖Work.Kernels.qParamFun τ‖ :=
    norm_pos_iff.mpr (Work.Asymptotics.qParamFun_ne_zero' τ)
  have hqt1 : (1 : ℝ) ≤ (‖Work.Kernels.qParamFun τ‖)⁻¹ := by
    refine (one_le_inv₀ hqtpos).mpr ?_
    rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hF.2]
  calc ‖Work.Asymptotics.KhatE1Core.dSm3 τ z‖
      ≤ 3456 * Cr * (3 * Cc + (2 * C6 * (99 + C2) + 2 * 17137 * C2 + 17137 * 99 * Ci))
          * Work.Kernels.scale τ * ‖q‖ ^ 3 := hmain
    _ ≤ (3456 * Cr * (3 * Cc + (2 * C6 * (99 + C2) + 2 * 17137 * C2 + 17137 * 99 * Ci)) + 1)
          * Work.Kernels.scale τ * (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖q‖ ^ 3 := by
        set K : ℝ := 3456 * Cr * (3 * Cc + (2 * C6 * (99 + C2) + 2 * 17137 * C2 + 17137 * 99 * Ci)) with hKdef
        have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; positivity
        have h1 : K * Work.Kernels.scale τ * ‖q‖ ^ 3
            ≤ K * Work.Kernels.scale τ * (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖q‖ ^ 3 := by
          have hbase : (0 : ℝ) ≤ K * Work.Kernels.scale τ := mul_nonneg hK0 hsc0
          have hh := le_mul_of_one_le_right hbase hqt1
          calc K * Work.Kernels.scale τ * ‖q‖ ^ 3
              = (K * Work.Kernels.scale τ) * ‖q‖ ^ 3 := by ring
            _ ≤ (K * Work.Kernels.scale τ * (‖Work.Kernels.qParamFun τ‖)⁻¹) * ‖q‖ ^ 3 :=
                mul_le_mul_of_nonneg_right hh hq3n
            _ = K * Work.Kernels.scale τ * (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖q‖ ^ 3 := by ring
        have h2 : K * Work.Kernels.scale τ * (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖q‖ ^ 3
            ≤ (K + 1) * Work.Kernels.scale τ * (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖q‖ ^ 3 := by
          have hbase : (0 : ℝ) ≤ Work.Kernels.scale τ * (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖q‖ ^ 3 :=
            mul_nonneg (mul_nonneg hsc0 (inv_nonneg.mpr (norm_nonneg _))) hq3n
          have he : K * Work.Kernels.scale τ * (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖q‖ ^ 3
              = K * (Work.Kernels.scale τ * (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖q‖ ^ 3) := by ring
          have he2 : (K + 1) * Work.Kernels.scale τ * (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖q‖ ^ 3
              = (K + 1) * (Work.Kernels.scale τ * (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖q‖ ^ 3) := by ring
          rw [he, he2]
          exact mul_le_mul_of_nonneg_right (by linarith : K ≤ K + 1) hbase
        linarith [h1, h2]
    _ = (3456 * Cr * (3 * Cc + (2 * C6 * (99 + C2) + 2 * 17137 * C2 + 17137 * 99 * Ci)) + 1)
          * (Work.Kernels.scale τ) ^ (1 : ℝ) * (1 + t) ^ (0 : ℝ)
          * (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖q‖ ^ 3 := by
        rw [Real.rpow_one, Real.rpow_zero, mul_one]

end

end Work.Asymptotics.KhatE1Core
