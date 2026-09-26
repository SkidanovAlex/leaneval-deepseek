/-
# The sharp `K₊^{(24)}` tail on the strip `0 ≤ Re z ≤ 1`

The proved axis version `Work.Asymptotics.EtailE.KPlus24_funnel_tail_sharp` bounds
`K₊^{(24)} τ z - 𝒢₊^{(24)} τ z` by `C (scale τ)^N (1+t)^M e^{-2π(t - Im τ)}` for `z = i t`.
Since `e^{-2π(t-Im τ)} = ‖q(τ)‖⁻¹ e^{-2πt}`, that is the "weight `‖q(τ)‖⁻¹‖E(z)‖²`" shape, which
is the `K₊`-side input of the sharp `d = 24` remainder bound
(`Submission/Work/Asymptotics/KhatE1/Kdev24Lead.lean`).

Here the same estimate is proved on the full strip `0 ≤ Re z ≤ 1`, `Im z = t ≥ Im τ + 1`.
Every ingredient of the axis proof uses the axis hypothesis only through `z.im = t`: the five
remainder groups `K24F.Sm1 … Sm5` are bounded by estimates (`K24Fsm.zdev`, `phi_sub_phiref_le`,
`q1_le`, `th0_le`, `uref_le`, `K24F.tau_atom_bounds_D`) that require only `3 ≤ z.im`, and the
divisor lower bound `‖Δ(z)(j(τ)-j(z))‖ ≥ 1/16` likewise.  Hence the proof replays with
`z.im = t` in place of the axis equation.
-/
import Mathlib
import Submission.Work.Asymptotics.K24FBase
import Submission.Work.Asymptotics.K24FZ
import Submission.Work.Asymptotics.K24FDefs
import Submission.Work.Asymptotics.K24F_sm_sum_bound
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.DeltaFun_funnel_lower_sharp
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.Compact.kplus24_defs

set_option maxHeartbeats 2000000

namespace Work.Asymptotics

open UpperHalfPlane
open Work.Kernels

noncomputable section

namespace KPlus24Strip

theorem sm1_le_strip : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ), Funnel τ → τ.im + 1 ≤ z.im →
    ‖K24F.Sm1 τ z‖ ≤ C * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
  obtain ⟨D, hD24, hDbd⟩ := K24F.tau_atom_bounds_D
  obtain ⟨CΦ, hCΦp, hCΦ⟩ := phi_sub_phiref_le
  obtain ⟨CΦ2, hCΦ2p, hCΦ2⟩ := phi_sub_phiref_sub_le
  obtain ⟨CQ, hCQp, hCQ⟩ := K24Fsm.q1_le
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  have hD0 : (0:ℝ) < D := by linarith
  refine ⟨D * CΦ + (27/8) * CQ * A + (27/8) * CΦ2 * A + 1, by positivity, ?_⟩
  intro τ z hτ ht
  have ht3 : (3:ℝ) ≤ z.im := by have h2 := Funnel.im_two hτ; linarith
  have hz3 : (3:ℝ) ≤ z.im := ht3
  have hz1 : (1:ℝ) ≤ z.im := by linarith
  obtain ⟨hdE4, hdE4c, hdSq, hdF, hdG2, hdE2, hdE4r, hdqd, hd1c, hdqd2, hdlow, hdinv,
    hE4inv, hE4up, hS0b⟩ := hA z hz3
  obtain ⟨hr0, hr2, hR0, hr1, hj, hΔ, hΔinv⟩ := hDbd τ hτ
  have hs0 : (0:ℝ) < scale τ := scale_pos τ
  have hsle : (0:ℝ) ≤ scale τ := hs0.le
  have he0 : (0:ℝ) < Real.exp (-(2 * Real.pi * (z.im - τ.im))) := Real.exp_pos _
  have heq_exp : Real.exp (2 * Real.pi * τ.im) * ‖qParamFun z‖
      = Real.exp (-(2 * Real.pi * (z.im - τ.im))) := K24F.exp_mul_qnorm rfl
  have hqle : ‖qParamFun z‖ ≤ Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
    rw [K24F.qnorm_of_im rfl, Real.exp_le_exp]
    nlinarith [Real.pi_pos, τ.im_pos]
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq1 : ‖qParamFun z‖ ≤ 1 := norm_qParamFun_le_one z hz1
  have hE4c : ‖E4Fun z ^ 3‖ ≤ 27/8 := by
    rw [norm_pow]
    have h2 := pow_le_pow_left₀ (norm_nonneg (E4Fun z)) hE4up 3
    have h3 : ((3:ℝ)/2)^3 = 27/8 := by norm_num
    linarith
  have hT1 : ‖jInvariantFun τ * (K24F.Phi τ z - K24F.Phiref τ z)‖
      ≤ D * CΦ * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
    have h := K24Fsm.norm_mul_le_mul hj (hCΦ τ z hτ hz3)
    calc ‖jInvariantFun τ * (K24F.Phi τ z - K24F.Phiref τ z)‖
        ≤ (D * Real.exp (2 * Real.pi * τ.im)) * (CΦ * scale τ * ‖qParamFun z‖) := h
      _ = D * CΦ * scale τ * (Real.exp (2 * Real.pi * τ.im) * ‖qParamFun z‖) := by ring
      _ = D * CΦ * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by rw [heq_exp]
  have hT2 : ‖E4Fun z ^ 3 * K24F.Q1 τ z * (qParamFun z / DeltaFun z - 1)‖
      ≤ (27/8) * CQ * A * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
    have h1 : ‖E4Fun z ^ 3 * K24F.Q1 τ z‖ ≤ (27/8) * (CQ * scale τ) :=
      K24Fsm.norm_mul_le_mul hE4c (hCQ τ z hτ hz3)
    have h := K24Fsm.norm_mul_le_mul h1 hdqd
    calc ‖E4Fun z ^ 3 * K24F.Q1 τ z * (qParamFun z / DeltaFun z - 1)‖
        ≤ ((27/8) * (CQ * scale τ)) * (A * ‖qParamFun z‖) := h
      _ = (27/8) * CQ * A * scale τ * ‖qParamFun z‖ := by ring
      _ ≤ (27/8) * CQ * A * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) :=
          mul_le_mul_of_nonneg_left hqle (by positivity)
  have hT3 : ‖E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)
        * (DeltaFun z)⁻¹‖
      ≤ (27/8) * CΦ2 * A * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
    have h1 : ‖E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)‖
        ≤ (27/8) * (CΦ2 * scale τ * ‖qParamFun z‖ ^ 2) :=
      K24Fsm.norm_mul_le_mul hE4c (hCΦ2 τ z hτ hz3)
    have h := K24Fsm.norm_mul_le_mul h1 hdinv
    calc ‖E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)
          * (DeltaFun z)⁻¹‖
        ≤ ((27/8) * (CΦ2 * scale τ * ‖qParamFun z‖ ^ 2)) * (A * ‖qParamFun z‖⁻¹) := h
      _ = (27/8) * CΦ2 * A * scale τ * (‖qParamFun z‖ ^ 2 * ‖qParamFun z‖⁻¹) := by ring
      _ = (27/8) * CΦ2 * A * scale τ * ‖qParamFun z‖ := by rw [K24Fsm.qsq_mul_qinv]
      _ ≤ (27/8) * CΦ2 * A * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) :=
          mul_le_mul_of_nonneg_left hqle (by positivity)
  rw [K24F.Sm1]
  rw [show E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)
        / DeltaFun z
      = E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)
        * (DeltaFun z)⁻¹ by ring]
  have hsub1 := norm_sub_le (jInvariantFun τ * (K24F.Phi τ z - K24F.Phiref τ z)
      - E4Fun z ^ 3 * K24F.Q1 τ z * (qParamFun z / DeltaFun z - 1))
      (E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)
        * (DeltaFun z)⁻¹)
  have hsub2 := norm_sub_le (jInvariantFun τ * (K24F.Phi τ z - K24F.Phiref τ z))
      (E4Fun z ^ 3 * K24F.Q1 τ z * (qParamFun z / DeltaFun z - 1))
  calc ‖jInvariantFun τ * (K24F.Phi τ z - K24F.Phiref τ z)
        - E4Fun z ^ 3 * K24F.Q1 τ z * (qParamFun z / DeltaFun z - 1)
        - E4Fun z ^ 3 * (K24F.Phi τ z - K24F.Phiref τ z - qParamFun z * K24F.Q1 τ z)
          * (DeltaFun z)⁻¹‖
      ≤ D * CΦ * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im)))
        + (27/8) * CQ * A * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im)))
        + (27/8) * CΦ2 * A * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
        linarith [hsub1, hsub2, hT1, hT2, hT3]
    _ = (D * CΦ + (27/8) * CQ * A + (27/8) * CΦ2 * A) * scale τ
          * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by ring
    _ ≤ (D * CΦ + (27/8) * CQ * A + (27/8) * CΦ2 * A + 1) * scale τ
          * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by nlinarith [hsle, he0]


theorem sm2_le_strip : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ), Funnel τ → τ.im + 1 ≤ z.im →
    ‖K24F.Sm2 τ z‖ ≤ C * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
  obtain ⟨D, hD24, hDbd⟩ := K24F.tau_atom_bounds_D
  obtain ⟨CΦ, hCΦp, hCΦ⟩ := K24Fsm.phiref_le
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  have hD0 : (0:ℝ) < D := by linarith
  refine ⟨D * CΦ * A + (27/8) * CΦ * A + 1, by positivity, ?_⟩
  intro τ z hτ ht
  have ht3 : (3:ℝ) ≤ z.im := by have h2 := Funnel.im_two hτ; linarith
  have hz3 : (3:ℝ) ≤ z.im := ht3
  have hz1 : (1:ℝ) ≤ z.im := by linarith
  obtain ⟨hdE4, hdE4c, hdSq, hdF, hdG2, hdE2, hdE4r, hdqd, hd1c, hdqd2, hdlow, hdinv,
    hE4inv, hE4up, hS0b⟩ := hA z hz3
  obtain ⟨hr0, hr2, hR0, hr1, hj, hΔ, hΔinv⟩ := hDbd τ hτ
  have hs0 : (0:ℝ) < scale τ := scale_pos τ
  have hsle : (0:ℝ) ≤ scale τ := hs0.le
  have he0 : (0:ℝ) < Real.exp (-(2 * Real.pi * (z.im - τ.im))) := Real.exp_pos _
  have heq_exp : Real.exp (2 * Real.pi * τ.im) * ‖qParamFun z‖
      = Real.exp (-(2 * Real.pi * (z.im - τ.im))) := K24F.exp_mul_qnorm rfl
  have hqle : ‖qParamFun z‖ ≤ Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
    rw [K24F.qnorm_of_im rfl, Real.exp_le_exp]
    nlinarith [Real.pi_pos, τ.im_pos]
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq1 : ‖qParamFun z‖ ≤ 1 := norm_qParamFun_le_one z hz1
  have hE4c : ‖E4Fun z ^ 3‖ ≤ 27/8 := by
    rw [norm_pow]
    have h2 := pow_le_pow_left₀ (norm_nonneg (E4Fun z)) hE4up 3
    have h3 : ((3:ℝ)/2)^3 = 27/8 := by norm_num
    linarith
  have hd1 : ‖K24F.d1 z‖ ≤ A * ‖qParamFun z‖ := hd1c
  have hT1 : ‖jInvariantFun τ * K24F.Phiref τ z * (1 - DeltaFun z / qParamFun z)‖
      ≤ D * CΦ * A * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
    have h1 : ‖jInvariantFun τ * K24F.Phiref τ z‖
        ≤ (D * Real.exp (2 * Real.pi * τ.im)) * (CΦ * scale τ) :=
      K24Fsm.norm_mul_le_mul hj (hCΦ τ z hτ hz3)
    have h := K24Fsm.norm_mul_le_mul h1 hdqd2
    calc ‖jInvariantFun τ * K24F.Phiref τ z * (1 - DeltaFun z / qParamFun z)‖
        ≤ ((D * Real.exp (2 * Real.pi * τ.im)) * (CΦ * scale τ)) * (A * ‖qParamFun z‖) := h
      _ = D * CΦ * A * scale τ * (Real.exp (2 * Real.pi * τ.im) * ‖qParamFun z‖) := by ring
      _ = D * CΦ * A * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by rw [heq_exp]
  have hT2 : ‖E4Fun z ^ 3 * K24F.Phiref τ z * K24F.d1 z‖
      ≤ (27/8) * CΦ * A * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
    have h1 : ‖E4Fun z ^ 3 * K24F.Phiref τ z‖ ≤ (27/8) * (CΦ * scale τ) :=
      K24Fsm.norm_mul_le_mul hE4c (hCΦ τ z hτ hz3)
    have h := K24Fsm.norm_mul_le_mul h1 hd1
    calc ‖E4Fun z ^ 3 * K24F.Phiref τ z * K24F.d1 z‖
        ≤ ((27/8) * (CΦ * scale τ)) * (A * ‖qParamFun z‖) := h
      _ = (27/8) * CΦ * A * scale τ * ‖qParamFun z‖ := by ring
      _ ≤ (27/8) * CΦ * A * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) :=
          mul_le_mul_of_nonneg_left hqle (by positivity)
  rw [K24F.Sm2]
  have hsub := norm_sub_le (jInvariantFun τ * K24F.Phiref τ z * (1 - DeltaFun z / qParamFun z))
    (E4Fun z ^ 3 * K24F.Phiref τ z * K24F.d1 z)
  calc ‖jInvariantFun τ * K24F.Phiref τ z * (1 - DeltaFun z / qParamFun z)
        - E4Fun z ^ 3 * K24F.Phiref τ z * K24F.d1 z‖
      ≤ D * CΦ * A * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im)))
        + (27/8) * CΦ * A * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
        linarith [hsub, hT1, hT2]
    _ = (D * CΦ * A + (27/8) * CΦ * A) * scale τ
          * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by ring
    _ ≤ (D * CΦ * A + (27/8) * CΦ * A + 1) * scale τ
          * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by nlinarith [hsle, he0]


theorem sm3_le_strip : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ), Funnel τ → τ.im + 1 ≤ z.im →
    ‖K24F.Sm3 τ z‖ ≤ C * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
  obtain ⟨D, hD24, hDbd⟩ := K24F.tau_atom_bounds_D
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  have hD0 : (0:ℝ) < D := by linarith
  refine ⟨13824 * A * D + 1, by positivity, ?_⟩
  intro τ z hτ ht
  have ht3 : (3:ℝ) ≤ z.im := by have h2 := Funnel.im_two hτ; linarith
  have hz3 : (3:ℝ) ≤ z.im := ht3
  have hz1 : (1:ℝ) ≤ z.im := by linarith
  obtain ⟨hdE4, hdE4c, hdSq, hdF, hdG2, hdE2, hdE4r, hdqd, hd1c, hdqd2, hdlow, hdinv,
    hE4inv, hE4up, hS0b⟩ := hA z hz3
  obtain ⟨hr0, hr2, hR0, hr1, hj, hΔ, hΔinv⟩ := hDbd τ hτ
  have hs0 : (0:ℝ) < scale τ := scale_pos τ
  have hsle : (0:ℝ) ≤ scale τ := hs0.le
  have he0 : (0:ℝ) < Real.exp (-(2 * Real.pi * (z.im - τ.im))) := Real.exp_pos _
  have hqle : ‖qParamFun z‖ ≤ Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
    rw [K24F.qnorm_of_im rfl, Real.exp_le_exp]
    nlinarith [Real.pi_pos, τ.im_pos]
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq1 : ‖qParamFun z‖ ≤ 1 := norm_qParamFun_le_one z hz1
  have hS0 : ‖K24F.S0 z‖ ≤ 3 := K24F.zS0_norm z hz1
  have hdF' : ‖E6Fun z * E2S z / E4Fun z - K24F.S0 z‖ ≤ A * ‖qParamFun z‖ := hdF
  have hbr : ‖K24F.S0 z * (E4Fun z ^ 3 - 1)
        - (E6Fun z * E2S z / E4Fun z - K24F.S0 z)‖ ≤ 4 * A * ‖qParamFun z‖ := by
    have h1 : ‖K24F.S0 z * (E4Fun z ^ 3 - 1)‖ ≤ 3 * (A * ‖qParamFun z‖) :=
      K24Fsm.norm_mul_le_mul hS0 hdE4c
    have hsub := norm_sub_le (K24F.S0 z * (E4Fun z ^ 3 - 1))
      (E6Fun z * E2S z / E4Fun z - K24F.S0 z)
    linarith
  have h3456 : ‖(3456:ℂ) * K24F.R0 τ‖ ≤ 3456 * (D * scale τ) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hR0 (by norm_num)
  have hmain : ‖(3456:ℂ) * K24F.R0 τ * (K24F.S0 z * (E4Fun z ^ 3 - 1)
        - (E6Fun z * E2S z / E4Fun z - K24F.S0 z))‖
      ≤ 13824 * A * D * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
    have h := K24Fsm.norm_mul_le_mul h3456 hbr
    calc ‖(3456:ℂ) * K24F.R0 τ * (K24F.S0 z * (E4Fun z ^ 3 - 1)
          - (E6Fun z * E2S z / E4Fun z - K24F.S0 z))‖
        ≤ (3456 * (D * scale τ)) * (4 * A * ‖qParamFun z‖) := h
      _ = 13824 * A * D * scale τ * ‖qParamFun z‖ := by ring
      _ ≤ 13824 * A * D * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) :=
          mul_le_mul_of_nonneg_left hqle (by positivity)
  rw [K24F.Sm3_bracket]
  refine le_trans hmain ?_
  calc 13824 * A * D * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im)))
      ≤ (13824 * A * D + 1) * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
        nlinarith [hsle, he0]


theorem sm4_le_strip : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ), Funnel τ → τ.im + 1 ≤ z.im →
    ‖K24F.Sm4 τ z‖ ≤ C * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
  obtain ⟨D, hD24, hDbd⟩ := K24F.tau_atom_bounds_D
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  have hD0 : (0:ℝ) < D := by linarith
  refine ⟨20736 * A * D + 1, by positivity, ?_⟩
  intro τ z hτ ht
  have ht3 : (3:ℝ) ≤ z.im := by have h2 := Funnel.im_two hτ; linarith
  have hz3 : (3:ℝ) ≤ z.im := ht3
  have hz1 : (1:ℝ) ≤ z.im := by linarith
  obtain ⟨hdE4, hdE4c, hdSq, hdF, hdG2, hdE2, hdE4r, hdqd, hd1c, hdqd2, hdlow, hdinv,
    hE4inv, hE4up, hS0b⟩ := hA z hz3
  obtain ⟨hr0, hr2, hR0, hr1, hj, hΔ, hΔinv⟩ := hDbd τ hτ
  have hs0 : (0:ℝ) < scale τ := scale_pos τ
  have hsle : (0:ℝ) ≤ scale τ := hs0.le
  have he0 : (0:ℝ) < Real.exp (-(2 * Real.pi * (z.im - τ.im))) := Real.exp_pos _
  have hqle : ‖qParamFun z‖ ≤ Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
    rw [K24F.qnorm_of_im rfl, Real.exp_le_exp]
    nlinarith [Real.pi_pos, τ.im_pos]
  have hq0 : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq1 : ‖qParamFun z‖ ≤ 1 := norm_qParamFun_le_one z hz1
  have hS0 : ‖K24F.S0 z‖ ≤ 3 := K24F.zS0_norm z hz1
  have hS0sq : ‖K24F.S0 z ^ 2‖ ≤ 9 := by
    rw [norm_pow]; nlinarith [hS0, norm_nonneg (K24F.S0 z)]
  have h1E4c : ‖1 - E4Fun z ^ 3‖ ≤ A * ‖qParamFun z‖ := by
    rw [show 1 - E4Fun z ^ 3 = -(E4Fun z ^ 3 - 1) by ring, norm_neg]
    exact hdE4c
  have h1728r0 : ‖(1728:ℂ) * K24F.r0 τ‖ ≤ 1728 * (D * scale τ) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hr0 (by norm_num)
  have h1728r2 : ‖(1728:ℂ) * K24F.r2 τ‖ ≤ 1728 * (D * scale τ) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hr2 (by norm_num)
  have hT1 : ‖(1728:ℂ) * K24F.r0 τ * (E2S z ^ 2 - K24F.S0 z ^ 2)‖
      ≤ 1728 * A * D * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
    have h := K24Fsm.norm_mul_le_mul h1728r0 hdSq
    calc ‖(1728:ℂ) * K24F.r0 τ * (E2S z ^ 2 - K24F.S0 z ^ 2)‖
        ≤ (1728 * (D * scale τ)) * (A * ‖qParamFun z‖) := h
      _ = 1728 * A * D * scale τ * ‖qParamFun z‖ := by ring
      _ ≤ 1728 * A * D * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) :=
          mul_le_mul_of_nonneg_left hqle (by positivity)
  have hT2 : ‖(1728:ℂ) * K24F.r2 τ * (E4Fun z - 1)‖
      ≤ 1728 * A * D * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
    have h := K24Fsm.norm_mul_le_mul h1728r2 hdE4
    calc ‖(1728:ℂ) * K24F.r2 τ * (E4Fun z - 1)‖
        ≤ (1728 * (D * scale τ)) * (A * ‖qParamFun z‖) := h
      _ = 1728 * A * D * scale τ * ‖qParamFun z‖ := by ring
      _ ≤ 1728 * A * D * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) :=
          mul_le_mul_of_nonneg_left hqle (by positivity)
  have hinner : ‖(1728:ℂ) * K24F.r0 τ * K24F.S0 z ^ 2 + (1728:ℂ) * K24F.r2 τ‖
      ≤ 1728 * (D * scale τ) * 9 + 1728 * (D * scale τ) := by
    have h1 : ‖(1728:ℂ) * K24F.r0 τ * K24F.S0 z ^ 2‖ ≤ (1728 * (D * scale τ)) * 9 :=
      K24Fsm.norm_mul_le_mul h1728r0 hS0sq
    have hadd := norm_add_le ((1728:ℂ) * K24F.r0 τ * K24F.S0 z ^ 2) ((1728:ℂ) * K24F.r2 τ)
    linarith
  have hT3 : ‖((1728:ℂ) * K24F.r0 τ * K24F.S0 z ^ 2 + (1728:ℂ) * K24F.r2 τ)
        * (1 - E4Fun z ^ 3)‖
      ≤ (1728 * (D * scale τ) * 9 + 1728 * (D * scale τ)) * (A * ‖qParamFun z‖) :=
    K24Fsm.norm_mul_le_mul hinner h1E4c
  rw [K24F.Sm4_split]
  have hsum : ‖(1728:ℂ) * K24F.r0 τ * (E2S z ^ 2 - K24F.S0 z ^ 2)
        + (1728:ℂ) * K24F.r2 τ * (E4Fun z - 1)
        + ((1728:ℂ) * K24F.r0 τ * K24F.S0 z ^ 2 + (1728:ℂ) * K24F.r2 τ)
          * (1 - E4Fun z ^ 3)‖
      ≤ ‖(1728:ℂ) * K24F.r0 τ * (E2S z ^ 2 - K24F.S0 z ^ 2)‖
        + ‖(1728:ℂ) * K24F.r2 τ * (E4Fun z - 1)‖
        + ‖((1728:ℂ) * K24F.r0 τ * K24F.S0 z ^ 2 + (1728:ℂ) * K24F.r2 τ)
            * (1 - E4Fun z ^ 3)‖ := K24Fsm.norm_sum3_le
  calc ‖(1728:ℂ) * K24F.r0 τ * (E2S z ^ 2 - K24F.S0 z ^ 2)
        + (1728:ℂ) * K24F.r2 τ * (E4Fun z - 1)
        + ((1728:ℂ) * K24F.r0 τ * K24F.S0 z ^ 2 + (1728:ℂ) * K24F.r2 τ)
          * (1 - E4Fun z ^ 3)‖
      ≤ 1728 * A * D * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im)))
        + 1728 * A * D * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im)))
        + (1728 * (D * scale τ) * 9 + 1728 * (D * scale τ)) * (A * ‖qParamFun z‖) := by
        linarith [hsum, hT1, hT2, hT3]
    _ ≤ 20736 * A * D * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
        have h3 : (1728 * (D * scale τ) * 9 + 1728 * (D * scale τ)) * (A * ‖qParamFun z‖)
            ≤ 17280 * A * D * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
          have hnn : (0:ℝ) ≤ 17280 * A * D * scale τ := by positivity
          calc (1728 * (D * scale τ) * 9 + 1728 * (D * scale τ)) * (A * ‖qParamFun z‖)
              = 17280 * A * D * scale τ * ‖qParamFun z‖ := by ring
            _ ≤ 17280 * A * D * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) :=
                mul_le_mul_of_nonneg_left hqle hnn
        linarith [hT1, hT2, h3]
    _ ≤ (20736 * A * D + 1) * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
        nlinarith [hsle, he0]


theorem sm5_le_strip : ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ), Funnel τ → τ.im + 1 ≤ z.im →
    ‖K24F.Sm5 τ z‖ ≤ C * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
  obtain ⟨D, hD24, hDbd⟩ := K24F.tau_atom_bounds_D
  obtain ⟨CΘ, hCΘp, hCΘ⟩ := K24Fsm.th0_le
  have hD0 : (0:ℝ) < D := by linarith
  refine ⟨2 * D * CΘ + 1, by positivity, ?_⟩
  intro τ z hτ ht
  have ht3 : (3:ℝ) ≤ z.im := by have h2 := Funnel.im_two hτ; linarith
  have hz3 : (3:ℝ) ≤ z.im := ht3
  obtain ⟨hr0, hr2, hR0, hr1, hj, hΔ, hΔinv⟩ := hDbd τ hτ
  have hs0 : (0:ℝ) < scale τ := scale_pos τ
  have hsle : (0:ℝ) ≤ scale τ := hs0.le
  have he0 : (0:ℝ) < Real.exp (-(2 * Real.pi * (z.im - τ.im))) := Real.exp_pos _
  have hDz : ‖DeltaFun z‖ ≤ 2 * Real.exp (-(2 * Real.pi * z.im)) := by
    have h := DeltaFun_upper_sharp z (by linarith : 1 ≤ z.im)
    exact h
  have hprod : ‖DeltaFun z * jInvariantFun τ‖
      ≤ 2 * D * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
    have h := K24Fsm.norm_mul_le_mul hDz hj
    calc ‖DeltaFun z * jInvariantFun τ‖
        ≤ (2 * Real.exp (-(2 * Real.pi * z.im))) * (D * Real.exp (2 * Real.pi * τ.im)) := h
      _ = 2 * D * (Real.exp (-(2 * Real.pi * z.im)) * Real.exp (2 * Real.pi * τ.im)) := by ring
      _ = 2 * D * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
          rw [show -(2 * Real.pi * (z.im - τ.im)) = -(2 * Real.pi * z.im) + 2 * Real.pi * τ.im by ring,
            Real.exp_add]
  rw [K24F.Sm5]
  rw [show -(DeltaFun z * jInvariantFun τ) * K24F.Th0 τ z
      = -((DeltaFun z * jInvariantFun τ) * K24F.Th0 τ z) by ring, norm_neg]
  have h := K24Fsm.norm_mul_le_mul hprod (hCΘ τ z hτ hz3)
  calc ‖(DeltaFun z * jInvariantFun τ) * K24F.Th0 τ z‖
      ≤ (2 * D * Real.exp (-(2 * Real.pi * (z.im - τ.im)))) * (CΘ * scale τ) := h
    _ = 2 * D * CΘ * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by ring
    _ ≤ (2 * D * CΘ + 1) * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
        nlinarith [hsle, he0]

/-- **The five remainder groups of the `K₊^{(24)}` cusp expansion are `O(e^{-2π(t - Im τ)})`.**

For `τ` in the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}` and `z = i t` with `t ≥ Im τ + 1`,

  `‖Sm1 τ z + … + Sm5 τ z‖ ≤ C (scale τ)^N e^{-2π(t - Im τ)}`. -/

theorem divisor_lower_strip (τ z : ℍ) (hτ : Funnel τ) (ht : τ.im + 1 ≤ z.im) :
    (1 / 16 : ℝ) ≤ ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ := by
  
  have ht3 : (3 : ℝ) ≤ z.im := by have := Funnel.im_two hτ; linarith
  have hz3 : (3 : ℝ) ≤ z.im := ht3
  have him1 : (1 : ℝ) ≤ τ.im := Funnel.im_one hτ
  have him2 : (2 : ℝ) ≤ τ.im := Funnel.im_two hτ
  have hkey : DeltaFun z * (jInvariantFun τ - jInvariantFun z)
      = DeltaFun z * jInvariantFun τ - E4Fun z ^ 3 := by
    rw [mul_sub, ClassicalFacts.DeltaFun_mul_jInvariantFun z]
  have hE4z : (1 / 2 : ℝ) ≤ ‖E4Fun z‖ := Work.FunnelNumerics.E4_funnel_bounds.2 z hz3
  have hE4z3 : (1 / 8 : ℝ) ≤ ‖E4Fun z ^ 3‖ := by
    rw [norm_pow]
    exact le_trans (by norm_num : (1/8:ℝ) ≤ (1/2:ℝ)^3) (pow_le_pow_left₀ (by norm_num) hE4z 3)
  have hΔz : ‖DeltaFun z‖ ≤ 2 * Real.exp (-(2 * Real.pi * z.im)) := by
    have h := DeltaFun_upper_sharp z (by linarith : 1 ≤ z.im)
    exact h
  have hE4t : ‖E4Fun τ‖ ≤ 3 / 2 := Work.FunnelNumerics.E4_funnel_bounds.1 τ hτ
  have hΔlo : (1 / 2) * Real.exp (-(2 * Real.pi * τ.im)) ≤ ‖DeltaFun τ‖ :=
    DeltaFun_funnel_lower_sharp him2
  have hjτ : ‖jInvariantFun τ‖ ≤ 27 / 4 * Real.exp (2 * Real.pi * τ.im) := by
    have hcoe : jInvariantFun τ = E4Fun τ ^ 3 / DeltaFun τ := rfl
    rw [hcoe, norm_div]
    have hE43 : ‖E4Fun τ ^ 3‖ ≤ (3 / 2) ^ 3 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hE4t 3
    have hpos : 0 < ‖DeltaFun τ‖ := lt_of_lt_of_le (by positivity) hΔlo
    calc ‖E4Fun τ ^ 3‖ / ‖DeltaFun τ‖
        ≤ (3 / 2) ^ 3 / ((1 / 2) * Real.exp (-(2 * Real.pi * τ.im))) :=
          div_le_div₀ (by positivity) hE43 (by positivity) hΔlo
      _ = 27 / 4 * Real.exp (2 * Real.pi * τ.im) := by
          rw [div_eq_mul_inv, mul_inv, K24F.inv_exp_neg, show ((1 / 2 : ℝ))⁻¹ = 2 by norm_num]
          norm_num
          ring
  have hprod : ‖DeltaFun z * jInvariantFun τ‖
      ≤ (27 / 2) * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
    have h1 : ‖DeltaFun z * jInvariantFun τ‖ ≤ (2 * Real.exp (-(2 * Real.pi * z.im)))
        * (27 / 4 * Real.exp (2 * Real.pi * τ.im)) := by
      rw [norm_mul]
      exact mul_le_mul hΔz hjτ (norm_nonneg _) (by positivity)
    refine le_trans h1 (le_of_eq ?_)
    have hexp : Real.exp (-(2 * Real.pi * (z.im - τ.im)))
        = Real.exp (-(2 * Real.pi * z.im)) * Real.exp (2 * Real.pi * τ.im) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp]; ring
  have hstep : Real.exp (-(2 * Real.pi * (z.im - τ.im))) ≤ Real.exp (-(2 * Real.pi)) := by
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos, ht]
  have he108 : (216 : ℝ) ≤ Real.exp (2 * Real.pi) := by
    have h1 : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have h2 : Real.exp 6 ≤ Real.exp (2 * Real.pi) := Real.exp_le_exp.mpr h1
    have h3 : Real.exp 6 = (Real.exp 1) ^ 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    have h4 : (2.7 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 :=
      pow_le_pow_left₀ (show (0:ℝ) ≤ 2.7 by norm_num)
        (show (2.7:ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 6
    have h5 : (216 : ℝ) ≤ (2.7 : ℝ) ^ 6 := by norm_num
    rw [h3] at h2
    linarith
  have h108 : Real.exp (-(2 * Real.pi)) ≤ 1 / 216 := by
    have h : (Real.exp (2 * Real.pi))⁻¹ ≤ (216 : ℝ)⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr he108
    rw [Real.exp_neg, show (1:ℝ)/216 = (216:ℝ)⁻¹ by norm_num]
    exact h
  have hsmall : (27 / 2) * Real.exp (-(2 * Real.pi * (z.im - τ.im))) ≤ 1 / 16 := by
    calc (27 / 2) * Real.exp (-(2 * Real.pi * (z.im - τ.im)))
        ≤ (27 / 2) * Real.exp (-(2 * Real.pi)) := mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ ≤ (27 / 2) * (1 / 216) := mul_le_mul_of_nonneg_left h108 (by norm_num)
      _ = 1 / 16 := by norm_num
  have hfinal : ‖DeltaFun z * jInvariantFun τ‖ ≤ 1 / 16 := le_trans hprod hsmall
  calc (1 / 16 : ℝ) = 1 / 8 - 1 / 16 := by norm_num
    _ ≤ ‖E4Fun z ^ 3‖ - ‖DeltaFun z * jInvariantFun τ‖ := by linarith
    _ ≤ ‖E4Fun z ^ 3 - DeltaFun z * jInvariantFun τ‖ := norm_sub_norm_le _ _
    _ = ‖DeltaFun z * jInvariantFun τ - E4Fun z ^ 3‖ := norm_sub_rev _ _
    _ = ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ := by rw [hkey]


/-- **The five remainder groups on the strip.** -/
theorem Sm_sum_strip :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (τ z : UpperHalfPlane), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ z.im →
        ‖Work.Asymptotics.K24F.Sm1 τ z + Work.Asymptotics.K24F.Sm2 τ z
          + Work.Asymptotics.K24F.Sm3 τ z + Work.Asymptotics.K24F.Sm4 τ z
          + Work.Asymptotics.K24F.Sm5 τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N
              * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
  obtain ⟨C1, hC1p, hC1⟩ := sm1_le_strip
  obtain ⟨C2, hC2p, hC2⟩ := sm2_le_strip
  obtain ⟨C3, hC3p, hC3⟩ := sm3_le_strip
  obtain ⟨C4, hC4p, hC4⟩ := sm4_le_strip
  obtain ⟨C5, hC5p, hC5⟩ := sm5_le_strip
  refine ⟨C1 + C2 + C3 + C4 + C5 + 1, 1, by positivity, by norm_num, ?_⟩
  intro τ z hτ ht
  have h1 := hC1 τ z hτ ht
  have h2 := hC2 τ z hτ ht
  have h3 := hC3 τ z hτ ht
  have h4 := hC4 τ z hτ ht
  have h5 := hC5 τ z hτ ht
  have hs0 : (0:ℝ) < scale τ := scale_pos τ
  have he0 : (0:ℝ) < Real.exp (-(2 * Real.pi * (z.im - τ.im))) := Real.exp_pos _
  have hsum : ‖Work.Asymptotics.K24F.Sm1 τ z + Work.Asymptotics.K24F.Sm2 τ z
        + Work.Asymptotics.K24F.Sm3 τ z + Work.Asymptotics.K24F.Sm4 τ z
        + Work.Asymptotics.K24F.Sm5 τ z‖
      ≤ ‖Work.Asymptotics.K24F.Sm1 τ z‖ + ‖Work.Asymptotics.K24F.Sm2 τ z‖
        + ‖Work.Asymptotics.K24F.Sm3 τ z‖ + ‖Work.Asymptotics.K24F.Sm4 τ z‖
        + ‖Work.Asymptotics.K24F.Sm5 τ z‖ := K24Fsm.norm_sum5_le
  rw [Real.rpow_one]
  calc ‖Work.Asymptotics.K24F.Sm1 τ z + Work.Asymptotics.K24F.Sm2 τ z
        + Work.Asymptotics.K24F.Sm3 τ z + Work.Asymptotics.K24F.Sm4 τ z
        + Work.Asymptotics.K24F.Sm5 τ z‖
      ≤ (C1 * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))))
        + (C2 * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))))
        + (C3 * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))))
        + (C4 * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))))
        + (C5 * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im)))) := by
        linarith [hsum, h1, h2, h3, h4, h5]
    _ = (C1 + C2 + C3 + C4 + C5) * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by ring
    _ ≤ (C1 + C2 + C3 + C4 + C5 + 1) * scale τ * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
        nlinarith [hs0.le, he0.le]

/-- **The sharp `K₊^{(24)}` tail on the strip.** -/
theorem KPlus24SharpStrip (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Kernels.KPlus 24 τ z - Work.Asymptotics.Compact.Gplus 24 τ z‖
          ≤ C * (‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ N
              * (1 + t) ^ M * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨Cs, Ns, hCs, hNs, hsb⟩ := Sm_sum_strip
  set Cc : ℝ := max ‖Work.Asymptotics.K24F.c‖ 1 with hCc
  have hCc0 : (0 : ℝ) < Cc := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨16 * Cc * Cs + 1, Ns, 2, by positivity, hNs, by norm_num, ?_⟩
  intro τ z t hτ ht hz0 hz1 hzim
  have htz : τ.im + 1 ≤ z.im := by rw [hzim]; exact ht
  have ht3 : (3 : ℝ) ≤ t := by have h2 := Funnel.im_two hτ; linarith
  have hz3 : (3 : ℝ) ≤ z.im := by rw [hzim]; exact ht3
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hden : (1 / 16 : ℝ) ≤ ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ :=
    divisor_lower_strip τ z hτ htz
  have hJ : jInvariantFun τ - jInvariantFun z ≠ 0 := by
    intro h0
    rw [h0, mul_zero, norm_zero] at hden
    norm_num at hden
  have hE4 : E4Fun z ≠ 0 := Work.Asymptotics.K24F.E4_ne_zero_three z hz3
  have hΔJ : DeltaFun z * (jInvariantFun τ - jInvariantFun z) ≠ 0 := mul_ne_zero hDz hJ
  have hdiff := Work.Asymptotics.K24F.KPlus24_diff τ z hJ hE4
  have hrepr : Work.Kernels.KPlus 24 τ z - Work.Asymptotics.Compact.Gplus 24 τ z
      = Work.Asymptotics.K24F.c * (z : ℂ) ^ 2
          * (Work.Asymptotics.K24F.Sm1 τ z + Work.Asymptotics.K24F.Sm2 τ z
              + Work.Asymptotics.K24F.Sm3 τ z + Work.Asymptotics.K24F.Sm4 τ z
              + Work.Asymptotics.K24F.Sm5 τ z)
          / (DeltaFun z * (jInvariantFun τ - jInvariantFun z)) := by
    rw [eq_div_iff hΔJ]
    rw [show (Work.Kernels.KPlus 24 τ z - Work.Asymptotics.Compact.Gplus 24 τ z)
          * (DeltaFun z * (jInvariantFun τ - jInvariantFun z))
        = DeltaFun z * (jInvariantFun τ - jInvariantFun z)
          * (Work.Kernels.KPlus 24 τ z - Work.Asymptotics.Compact.Gplus 24 τ z) from by ring]
    exact hdiff
  have hdenpos : 0 < ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ :=
    lt_of_lt_of_le (by norm_num) hden
  have hdeninv : (‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖)⁻¹ ≤ 16 := by
    rw [inv_le_comm₀ hdenpos (by norm_num : (0 : ℝ) < 16)]
    have h16 : ((16 : ℝ))⁻¹ = 1 / 16 := by norm_num
    rw [h16]
    exact hden
  have hS : ‖Work.Asymptotics.K24F.Sm1 τ z + Work.Asymptotics.K24F.Sm2 τ z
        + Work.Asymptotics.K24F.Sm3 τ z + Work.Asymptotics.K24F.Sm4 τ z
        + Work.Asymptotics.K24F.Sm5 τ z‖
      ≤ Cs * (scale τ) ^ Ns * Real.exp (-(2 * Real.pi * (z.im - τ.im))) :=
    hsb τ z hτ htz
  have hznorm : ‖(z : ℂ) ^ 2‖ ≤ (1 + t) ^ 2 := by
    have h2 : ‖(z : ℂ)‖ ≤ 1 + t := by
      have h := Complex.norm_le_abs_re_add_abs_im (z : ℂ)
      have hre0 : (0 : ℝ) ≤ (z : ℂ).re := hz0
      have hre : |(z : ℂ).re| ≤ 1 := by
        rw [abs_of_nonneg hre0]
        exact hz1
      have himpos : (0 : ℝ) < (z : ℂ).im := z.im_pos
      have him : |(z : ℂ).im| = t := by
        rw [abs_of_pos himpos]
        exact hzim
      rw [him] at h
      linarith [h, hre]
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hstep1 : ‖Work.Kernels.KPlus 24 τ z - Work.Asymptotics.Compact.Gplus 24 τ z‖
      ≤ ‖Work.Asymptotics.K24F.c * (z : ℂ) ^ 2
          * (Work.Asymptotics.K24F.Sm1 τ z + Work.Asymptotics.K24F.Sm2 τ z
              + Work.Asymptotics.K24F.Sm3 τ z + Work.Asymptotics.K24F.Sm4 τ z
              + Work.Asymptotics.K24F.Sm5 τ z)‖ * 16 := by
    rw [hrepr, norm_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hdeninv (norm_nonneg _)
  have hstep2' : ‖Work.Asymptotics.K24F.c * (z : ℂ) ^ 2
        * (Work.Asymptotics.K24F.Sm1 τ z + Work.Asymptotics.K24F.Sm2 τ z
            + Work.Asymptotics.K24F.Sm3 τ z + Work.Asymptotics.K24F.Sm4 τ z
            + Work.Asymptotics.K24F.Sm5 τ z)‖
      ≤ Cc * (1 + t) ^ 2
          * (Cs * (scale τ) ^ Ns * Real.exp (-(2 * Real.pi * (z.im - τ.im)))) := by
    rw [norm_mul, norm_mul]
    have h1 : ‖Work.Asymptotics.K24F.c‖ ≤ Cc := le_max_left _ _
    have h3 : ‖Work.Asymptotics.K24F.c‖ * ‖(z : ℂ) ^ 2‖ ≤ Cc * (1 + t) ^ 2 :=
      mul_le_mul h1 hznorm (norm_nonneg _) hCc0.le
    have h4 : (0 : ℝ) ≤ Cc * (1 + t) ^ 2 := mul_nonneg hCc0.le (by positivity)
    exact mul_le_mul h3 hS (norm_nonneg _) h4
  have hfin : ‖Work.Kernels.KPlus 24 τ z - Work.Asymptotics.Compact.Gplus 24 τ z‖
      ≤ 16 * Cc * Cs * (scale τ) ^ Ns * (1 + t) ^ 2
          * Real.exp (-(2 * Real.pi * (z.im - τ.im))) := by
    refine le_trans hstep1 ?_
    refine le_trans (mul_le_mul_of_nonneg_right hstep2' (by norm_num : (0:ℝ) ≤ 16)) ?_
    exact le_of_eq (by ring)
  have hq : (‖Work.Kernels.qParamFun τ‖)⁻¹ = Real.exp (2 * Real.pi * τ.im) := by
    rw [Work.Asymptotics.norm_qParamFun, Real.exp_neg, inv_inv]
  have hpow2 : (1 + t) ^ (2 : ℝ) = (1 + t) ^ 2 := by rw [Real.rpow_two]
  have hexp : Real.exp (-(2 * Real.pi * (z.im - τ.im)))
      = Real.exp (2 * Real.pi * τ.im) * Real.exp (-(2 * Real.pi * t)) := by
    rw [show -(2 * Real.pi * (z.im - τ.im)) = -(2 * Real.pi * z.im) + 2 * Real.pi * τ.im by ring,
      Real.exp_add, hzim]
    try ring
  have heq : 16 * Cc * Cs * (scale τ) ^ Ns * (1 + t) ^ 2
        * Real.exp (-(2 * Real.pi * (z.im - τ.im)))
      = 16 * Cc * Cs * (‖Work.Kernels.qParamFun τ‖)⁻¹ * (scale τ) ^ Ns
          * (1 + t) ^ (2 : ℝ) * Real.exp (-(2 * Real.pi * t)) := by
    rw [hq, hexp, ← hpow2]
    ring
  have hB : (0 : ℝ) ≤ (‖Work.Kernels.qParamFun τ‖)⁻¹ * (scale τ) ^ Ns
      * (1 + t) ^ (2 : ℝ) * Real.exp (-(2 * Real.pi * t)) := by
    have h1 : (0 : ℝ) ≤ (‖Work.Kernels.qParamFun τ‖)⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    have h2 : (0 : ℝ) ≤ (scale τ) ^ Ns := Real.rpow_nonneg (scale_pos τ).le Ns
    have h3 : (0 : ℝ) ≤ (1 + t) ^ (2 : ℝ) := Real.rpow_nonneg (by linarith) 2
    have h4 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * t)) := (Real.exp_pos _).le
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
  have hstep3 : 16 * Cc * Cs * (‖Work.Kernels.qParamFun τ‖)⁻¹ * (scale τ) ^ Ns
        * (1 + t) ^ (2 : ℝ) * Real.exp (-(2 * Real.pi * t))
      ≤ (16 * Cc * Cs + 1) * (‖Work.Kernels.qParamFun τ‖)⁻¹ * (scale τ) ^ Ns
        * (1 + t) ^ (2 : ℝ) * Real.exp (-(2 * Real.pi * t)) := by
    have h' := mul_le_mul_of_nonneg_right
      (show (16:ℝ) * Cc * Cs ≤ 16 * Cc * Cs + 1 by linarith) hB
    linarith [h']
  exact le_trans hfin (le_trans (le_of_eq heq) hstep3)


end KPlus24Strip

end

end Work.Asymptotics
