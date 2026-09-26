import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Sm2Split
import Submission.Work.Asymptotics.KhatE1Core.DKPlusQ1
import Submission.Work.Asymptotics.KhatE1Core.DKPlusBounds
import Submission.Work.Asymptotics.K24F_sm_sum_bound

/-!
# The leading term of `dSm2`

`dSm2 = -(j(τ)Φ_ref dDq) - E4Ref³Φ_ref Donly - dE4c Φ_ref Donly`, so
`dSm2 + 324·q(z)·Φ_ref = O(scale τ · ‖q(z)‖²)`: the `q¹`-coefficient of `dSm2` is `-324Φ_ref`.

This is the *only* surviving `q¹`-term of the plus-side deviation sum `dKPlusSum`, hence
`[dKPlus24]_{E²} = 324 c z² Φ_ref` (`DKPlusQ1.lean`).
-/

set_option maxHeartbeats 4000000

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

theorem dSm2_leading :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.dSm2 τ z
            + 324 * Work.Kernels.qParamFun z * Work.Asymptotics.K24F.Phiref τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
  obtain ⟨Cq, hCq, hDq⟩ := dDq_bound
  obtain ⟨Cc, hCc, hEc⟩ := dE4c_bound
  obtain ⟨Cdl, hCdl, hDl⟩ := Donly_leading
  obtain ⟨Cph, hCph, hPh⟩ := Work.Asymptotics.K24Fsm.phiref_le
  obtain ⟨Cj, hCj, hj⟩ := Work.Asymptotics.K24F.tau_atom_bounds
  refine ⟨Cph * (Cj * Cq + 324 * 13841287200 + 2401 ^ 3 * Cdl)
      + Cc * Cph * (Cdl + 324) + 1, 1, 0, by positivity, by norm_num, le_rfl, ?_⟩
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
  have hq2 : ‖q‖ ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
  have hdDq : ‖dDq z‖ ≤ Cq * ‖q‖ ^ 3 := hDq z hz1'
  have hdE4c : ‖dE4c z‖ ≤ Cc * ‖q‖ ^ 3 := hEc z hz1'
  have hdDon : ‖Donly z - 324 * q‖ ≤ Cdl * ‖q‖ ^ 2 := hDl z hz1'
  have hDon : ‖Donly z‖ ≤ (Cdl + 324) * ‖q‖ := by
    have h324 : ‖(324 : ℂ) * q‖ = 324 * ‖q‖ := by rw [norm_mul]; norm_num
    have he : Donly z = (Donly z - 324 * q) + 324 * q := by ring
    rw [he]
    refine le_trans (norm_add_le _ _) ?_
    rw [h324]
    have hqq : Cdl * ‖q‖ ^ 2 ≤ Cdl * ‖q‖ := by
      have h2 : ‖q‖ ^ 2 ≤ ‖q‖ := by nlinarith [hq0, hq1]
      exact mul_le_mul_of_nonneg_left h2 hCdl.le
    linarith [hdDon, hqq]
  have hPn : ‖E4Ref z‖ ≤ 2401 := norm_E4Ref_le hz1'
  have hPn3 : ‖E4Ref z ^ 3‖ ≤ 2401 ^ 3 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hPn 3
  have hE43 : ‖E4Ref z ^ 3 - 1‖ ≤ 13841287200 * ‖q‖ := by
    have hfac : E4Ref z ^ 3 - 1 = (E4Ref z - 1) * (E4Ref z ^ 2 + E4Ref z + 1) := by ring
    have h1 : ‖E4Ref z - 1‖ ≤ 2400 * ‖q‖ := by
      have hid : E4Ref z - 1 = 240 * q + 2160 * q ^ 2 := by
        simp only [E4Ref, hqdef]; ring
      rw [hid]
      have hb : ‖(2160 : ℂ) * q ^ 2‖ = 2160 * ‖q‖ ^ 2 := by rw [norm_mul, norm_pow]; norm_num
      have hb2 : ‖(240 : ℂ) * q‖ = 240 * ‖q‖ := by rw [norm_mul]; norm_num
      calc ‖(240 : ℂ) * q + (2160 : ℂ) * q ^ 2‖
          ≤ ‖(240 : ℂ) * q‖ + ‖(2160 : ℂ) * q ^ 2‖ := norm_add_le _ _
        _ = 240 * ‖q‖ + 2160 * ‖q‖ ^ 2 := by rw [hb, hb2]
        _ ≤ 2400 * ‖q‖ := by nlinarith [hq0, hq1, hq2]
    have h2 : ‖E4Ref z ^ 2 + E4Ref z + 1‖ ≤ 2401 ^ 2 + 2401 + 1 := by
      have hp : ‖E4Ref z ^ 2‖ ≤ 2401 ^ 2 := by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hPn 2
      calc ‖E4Ref z ^ 2 + E4Ref z + 1‖
          ≤ ‖E4Ref z ^ 2 + E4Ref z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ (‖E4Ref z ^ 2‖ + ‖E4Ref z‖) + ‖(1 : ℂ)‖ := by
            have h := norm_add_le (E4Ref z ^ 2) (E4Ref z); linarith [h]
        _ ≤ 2401 ^ 2 + 2401 + 1 := by rw [norm_one]; linarith [hp, hPn]
    rw [hfac, norm_mul]
    calc ‖E4Ref z - 1‖ * ‖E4Ref z ^ 2 + E4Ref z + 1‖
        ≤ (2400 * ‖q‖) * (2401 ^ 2 + 2401 + 1) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ ≤ 13841287200 * ‖q‖ := by
          have hnum : (2400 : ℝ) * (2401 ^ 2 + 2401 + 1) = 13841287200 := by norm_num
          nlinarith [hq0, hnum]
  have hjτ : ‖Work.Kernels.jInvariantFun τ‖
      ≤ Cj * (‖Work.Kernels.qParamFun τ‖)⁻¹ := by
    have h1 : ‖Work.Kernels.jInvariantFun τ‖ ≤ Cj * Real.exp (2 * Real.pi * τ.im) :=
      (hj τ hF).2.2.2.2.1
    have h2 : Real.exp (2 * Real.pi * τ.im)
        = (Real.exp (-(2 * Real.pi * τ.im)))⁻¹ := by
      rw [Real.exp_neg, inv_inv]
    rw [h2, ← Work.Asymptotics.norm_qParamFun τ] at h1
    exact h1
  have hqtpos : (0 : ℝ) < ‖Work.Kernels.qParamFun τ‖ :=
    norm_pos_iff.mpr (Work.Asymptotics.qParamFun_ne_zero' τ)
  have hqt : ‖q‖ ≤ ‖Work.Kernels.qParamFun τ‖ := by
    rw [hqn, Work.Asymptotics.norm_qParamFun]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht])
  have hrel : (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖q‖ ^ 3 ≤ ‖q‖ ^ 2 := by
    have h3 : ‖q‖ ^ 3 ≤ ‖Work.Kernels.qParamFun τ‖ * ‖q‖ ^ 2 := by
      have he : ‖q‖ ^ 3 = ‖q‖ * ‖q‖ ^ 2 := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right hqt (pow_nonneg hq0 2)
    rw [inv_mul_le_iff₀ hqtpos]
    exact h3
  have hPh' : ‖Work.Asymptotics.K24F.Phiref τ z‖ ≤ Cph * Work.Kernels.scale τ :=
    hPh τ z hF hz3
  have hsc0 : (0 : ℝ) ≤ Work.Kernels.scale τ := (Work.Kernels.scale_pos τ).le
  -- complex factors
  have hC2 : ‖(324 : ℂ) * q * (1 - E4Ref z ^ 3)‖ ≤ 324 * 13841287200 * ‖q‖ ^ 2 := by
    rw [show (1 : ℂ) - E4Ref z ^ 3 = -(E4Ref z ^ 3 - 1) from by ring, norm_mul, norm_neg,
      norm_mul, show ‖(324 : ℂ)‖ = 324 from by norm_num]
    have h := mul_le_mul_of_nonneg_left hE43 (by positivity : (0 : ℝ) ≤ 324 * ‖q‖)
    nlinarith [h, hq0]
  have hid : Work.Asymptotics.KhatE1Core.dSm2 τ z
        + 324 * q * Work.Asymptotics.K24F.Phiref τ z
      = Work.Asymptotics.K24F.Phiref τ z
          * (-(Work.Kernels.jInvariantFun τ * dDq z)
              + 324 * q * (1 - E4Ref z ^ 3)
              - E4Ref z ^ 3 * (Donly z - 324 * q))
        - dE4c z * Work.Asymptotics.K24F.Phiref τ z * Donly z := by
    simp only [Work.Asymptotics.KhatE1Core.dSm2, hqdef]
    ring
  -- the inner sum
  have hsum : ‖(-(Work.Kernels.jInvariantFun τ * dDq z)
        + 324 * q * (1 - E4Ref z ^ 3)
        - E4Ref z ^ 3 * (Donly z - 324 * q))‖
      ≤ ‖Work.Kernels.jInvariantFun τ * dDq z‖ + ‖(324 : ℂ) * q * (1 - E4Ref z ^ 3)‖
        + ‖E4Ref z ^ 3 * (Donly z - 324 * q)‖ := by
    calc ‖-(Work.Kernels.jInvariantFun τ * dDq z)
          + 324 * q * (1 - E4Ref z ^ 3) - E4Ref z ^ 3 * (Donly z - 324 * q)‖
        = ‖-(Work.Kernels.jInvariantFun τ * dDq z)
            + ((324 : ℂ) * q * (1 - E4Ref z ^ 3)
                - E4Ref z ^ 3 * (Donly z - 324 * q))‖ := by
          congr 1; ring
      _ ≤ ‖-(Work.Kernels.jInvariantFun τ * dDq z)‖
            + ‖(324 : ℂ) * q * (1 - E4Ref z ^ 3)
                - E4Ref z ^ 3 * (Donly z - 324 * q)‖ := norm_add_le _ _
      _ = ‖Work.Kernels.jInvariantFun τ * dDq z‖
            + ‖(324 : ℂ) * q * (1 - E4Ref z ^ 3)
                - E4Ref z ^ 3 * (Donly z - 324 * q)‖ := by rw [norm_neg]
      _ ≤ ‖Work.Kernels.jInvariantFun τ * dDq z‖
            + (‖(324 : ℂ) * q * (1 - E4Ref z ^ 3)‖
                + ‖E4Ref z ^ 3 * (Donly z - 324 * q)‖) := by
          have hs := norm_sub_le ((324 : ℂ) * q * (1 - E4Ref z ^ 3))
            (E4Ref z ^ 3 * (Donly z - 324 * q))
          linarith [hs]
      _ = ‖Work.Kernels.jInvariantFun τ * dDq z‖
            + ‖(324 : ℂ) * q * (1 - E4Ref z ^ 3)‖
            + ‖E4Ref z ^ 3 * (Donly z - 324 * q)‖ := by ring
  have hJ1 : ‖Work.Kernels.jInvariantFun τ * dDq z‖ ≤ Cj * Cq * ‖q‖ ^ 2 := by
    rw [norm_mul]
    have h2 : ‖Work.Kernels.jInvariantFun τ‖ * ‖dDq z‖
        ≤ (Cj * (‖Work.Kernels.qParamFun τ‖)⁻¹) * (Cq * ‖q‖ ^ 3) :=
      mul_le_mul hjτ hdDq (norm_nonneg _) (by positivity)
    have he : (Cj * (‖Work.Kernels.qParamFun τ‖)⁻¹) * (Cq * ‖q‖ ^ 3)
        = (Cj * Cq) * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖q‖ ^ 3) := by ring
    rw [he] at h2
    have h3 := mul_le_mul_of_nonneg_left hrel (by positivity : (0 : ℝ) ≤ Cj * Cq)
    linarith [h2, h3]
  -- the four bounds
  have hA : ‖Work.Asymptotics.K24F.Phiref τ z
        * (-(Work.Kernels.jInvariantFun τ * dDq z)
            + 324 * q * (1 - E4Ref z ^ 3)
            - E4Ref z ^ 3 * (Donly z - 324 * q))‖
      ≤ Cph * (Cj * Cq + 324 * 13841287200 + 2401 ^ 3 * Cdl)
          * Work.Kernels.scale τ * ‖q‖ ^ 2 := by
    rw [norm_mul]
    calc ‖Work.Asymptotics.K24F.Phiref τ z‖
          * ‖(-(Work.Kernels.jInvariantFun τ * dDq z)
              + 324 * q * (1 - E4Ref z ^ 3)
              - E4Ref z ^ 3 * (Donly z - 324 * q))‖
        ≤ (Cph * Work.Kernels.scale τ)
          * (‖Work.Kernels.jInvariantFun τ * dDq z‖
              + ‖(324 : ℂ) * q * (1 - E4Ref z ^ 3)‖
              + ‖E4Ref z ^ 3 * (Donly z - 324 * q)‖) :=
          mul_le_mul hPh' hsum (norm_nonneg _) (by positivity)
      _ ≤ (Cph * Work.Kernels.scale τ)
            * (Cj * Cq * ‖q‖ ^ 2 + 324 * 13841287200 * ‖q‖ ^ 2
                + 2401 ^ 3 * Cdl * ‖q‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hb2 : ‖(324 : ℂ) * q * (1 - E4Ref z ^ 3)‖ ≤ 324 * 13841287200 * ‖q‖ ^ 2 := hC2
          have hb3 : ‖E4Ref z ^ 3 * (Donly z - 324 * q)‖ ≤ 2401 ^ 3 * Cdl * ‖q‖ ^ 2 := by
            rw [norm_mul]
            have h := mul_le_mul hPn3 hdDon (norm_nonneg _) (by positivity)
            nlinarith [h]
          linarith [hJ1, hb2, hb3]
      _ = Cph * (Cj * Cq + 324 * 13841287200 + 2401 ^ 3 * Cdl)
            * Work.Kernels.scale τ * ‖q‖ ^ 2 := by ring
  have hT4 : ‖dE4c z * Work.Asymptotics.K24F.Phiref τ z * Donly z‖
      ≤ Cc * Cph * (Cdl + 324) * Work.Kernels.scale τ * ‖q‖ ^ 2 := by
    rw [norm_mul, norm_mul]
    have hstep : (‖dE4c z‖ * ‖Work.Asymptotics.K24F.Phiref τ z‖) * ‖Donly z‖
        ≤ ((Cc * ‖q‖ ^ 3) * (Cph * Work.Kernels.scale τ)) * ((Cdl + 324) * ‖q‖) := by
      refine mul_le_mul (mul_le_mul hdE4c hPh' (norm_nonneg _) (by positivity)) hDon
        (norm_nonneg _) (by positivity)
    have hfin : ((Cc * ‖q‖ ^ 3) * (Cph * Work.Kernels.scale τ)) * ((Cdl + 324) * ‖q‖)
        ≤ Cc * Cph * (Cdl + 324) * Work.Kernels.scale τ * ‖q‖ ^ 2 := by
      have he : ((Cc * ‖q‖ ^ 3) * (Cph * Work.Kernels.scale τ)) * ((Cdl + 324) * ‖q‖)
          = (Cc * Cph * (Cdl + 324) * Work.Kernels.scale τ) * (‖q‖ ^ 3 * ‖q‖) := by ring
      rw [he]
      have h4 : ‖q‖ ^ 3 * ‖q‖ ≤ ‖q‖ ^ 2 := by
        have he2 : ‖q‖ ^ 3 * ‖q‖ = ‖q‖ ^ 2 * ‖q‖ ^ 2 := by ring
        rw [he2]
        exact mul_le_of_le_one_right (pow_nonneg hq0 2) hq2
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    linarith [hstep, hfin]
  have hmain : ‖Work.Asymptotics.K24F.Phiref τ z
        * (-(Work.Kernels.jInvariantFun τ * dDq z)
            + 324 * q * (1 - E4Ref z ^ 3)
            - E4Ref z ^ 3 * (Donly z - 324 * q))
        - dE4c z * Work.Asymptotics.K24F.Phiref τ z * Donly z‖
      ≤ (Cph * (Cj * Cq + 324 * 13841287200 + 2401 ^ 3 * Cdl)
          + Cc * Cph * (Cdl + 324)) * Work.Kernels.scale τ * ‖q‖ ^ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    have hsum2 : Cph * (Cj * Cq + 324 * 13841287200 + 2401 ^ 3 * Cdl)
          * Work.Kernels.scale τ * ‖q‖ ^ 2
        + Cc * Cph * (Cdl + 324) * Work.Kernels.scale τ * ‖q‖ ^ 2
        = (Cph * (Cj * Cq + 324 * 13841287200 + 2401 ^ 3 * Cdl)
            + Cc * Cph * (Cdl + 324)) * Work.Kernels.scale τ * ‖q‖ ^ 2 := by ring
    linarith [hA, hT4, hsum2]
  rw [hid]
  refine le_trans hmain ?_
  rw [Real.rpow_one, Real.rpow_zero, mul_one]
  nlinarith [hsc0, hq0, hq2]

end

end Work.Asymptotics.KhatE1Core
