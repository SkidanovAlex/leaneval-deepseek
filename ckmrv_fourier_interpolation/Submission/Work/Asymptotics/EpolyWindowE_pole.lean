import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.EBase
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Divisor
import Submission.Work.Asymptotics.KClear_mg2
import Submission.Work.Asymptotics.DeltaFun_funnel_lower_sharp
import Submission.Work.Asymptotics.SpikeCircle.DeltaFunBoundsHalf
import Submission.Work.Asymptotics.SpikeCircle.divisorLowerDisc
import Submission.Work.Asymptotics.SpikeCircle.jInvariantFunUpperDisc
import Submission.Work.Asymptotics.SpikeCircle.spike_KPlus8_bound
import Submission.Work.Asymptotics.SpikeCircle.spike_KMinus8_bound
import Submission.Work.Asymptotics.SpikeCircle.spike_KPlus24_bound
import Submission.Work.Asymptotics.SpikeCircle.spike_KMinus24_bound
import Submission.Work.Asymptotics.SpikeCircle.SBs
import Submission.Work.Analysis.ThreeZeros.three_zeros_bound_ball
import Submission.Work.Asymptotics.Funnel_Kfun_diag_bound
import Submission.Work.Asymptotics.MiddleRange.Classify
import Submission.Work.Residues.KPlusClear_diag
import Submission.Work.Residues.KMinusClear_diag
import Submission.Work.Residues.KPlusClear_T
import Submission.Work.Residues.KMinusClear_T
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul
import Submission.Work.Kernels.KernelGrowth
import Submission.Work.Kernels.KMinusSlash
import Submission.Work.Asymptotics.HalfFunnel.spikeShift
import Submission.Work.Asymptotics.HalfFunnel.funnelFlat

set_option maxHeartbeats 3200000

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Manifold
open Work.Analysis.ThreeZeros

noncomputable section

/-! ## 0. Elementary `scale` comparisons -/

/-- On `E`, `2 ‖w‖² ≤ Im w`. -/
lemma two_normSq_le_im_of_mem_KEpsilon {w : ℍ} (hw : w ∈ KEpsilon) :
    2 * ‖(w : ℂ)‖ ^ 2 ≤ w.im := by
  have hS : (2 : ℝ) ≤ (ModularGroup.S • w).im := hw.2
  rw [E_S_im] at hS
  have hn : 0 < ‖(w : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr w.ne_zero) 2
  rw [le_div_iff₀ hn] at hS
  linarith

lemma im_le_norm_coe (w : ℍ) : w.im ≤ ‖(w : ℂ)‖ := by
  simpa [UpperHalfPlane.coe_im, abs_of_pos w.im_pos] using Complex.abs_im_le_norm (w : ℂ)

lemma coe_S_smul_eq (w : ℍ) : (((ModularGroup.S • w : ℍ)) : ℂ) = -((w : ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]

/-- `‖S • w‖ ≤ scale w`. -/
lemma coe_norm_S_smul_le_scale (w : ℍ) :
    ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ≤ Work.Kernels.scale w := by
  rw [coe_S_smul_eq, norm_neg, norm_inv]
  have h1 : ‖(w : ℂ)‖⁻¹ ≤ (w.im)⁻¹ := by
    rw [inv_le_inv₀ (norm_pos_iff.mpr w.ne_zero) w.im_pos]
    exact im_le_norm_coe w
  exact h1.trans (Work.Kernels.inv_im_le_scale w)

/-- On `E`, `scale (S • w) ≤ 3 scale w`. -/
lemma scale_S_smul_le_of_mem_KEpsilon (w : ℍ) (hw : w ∈ KEpsilon) :
    Work.Kernels.scale (ModularGroup.S • w) ≤ 3 * Work.Kernels.scale w := by
  have h2 := two_normSq_le_im_of_mem_KEpsilon hw
  have hwpos : 0 < w.im := w.im_pos
  have h1 : ((ModularGroup.S • w).im)⁻¹ ≤ 1 / 2 := by
    rw [E_S_im, inv_div, div_le_iff₀ hwpos]
    linarith
  have h3 : ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ≤ 1 + (w.im)⁻¹ + ‖(w : ℂ)‖ := by
    simpa only [Work.Kernels.scale] using coe_norm_S_smul_le_scale w
  have h4 : (1 : ℝ) ≤ 1 + (w.im)⁻¹ + ‖(w : ℂ)‖ := by
    simpa only [Work.Kernels.scale] using Work.Kernels.one_le_scale w
  have key : (1 : ℝ) + (ModularGroup.S • w).im⁻¹ + ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖
      ≤ 3 * (1 + (w.im)⁻¹ + ‖(w : ℂ)‖) := by linarith
  simpa only [Work.Kernels.scale] using key

/-- If `‖ζ - τ‖ ≤ 29/20` and `2 ≤ Im τ` then `scale ζ ≤ 6 scale τ`. -/
lemma scale_le_six_of_norm_sub_le {τ ζ : ℍ} (hτ : 2 ≤ τ.im)
    (h : ‖(ζ : ℂ) - (τ : ℂ)‖ ≤ 29 / 20) : Work.Kernels.scale ζ ≤ 6 * Work.Kernels.scale τ := by
  have h1 : |ζ.im - τ.im| ≤ 29 / 20 := by
    have h2 : |((ζ : ℂ) - (τ : ℂ)).im| ≤ ‖(ζ : ℂ) - (τ : ℂ)‖ := Complex.abs_im_le_norm _
    have h3 : ((ζ : ℂ) - (τ : ℂ)).im = ζ.im - τ.im := by
      rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im]
    rw [h3] at h2
    linarith
  have him : (11 / 20 : ℝ) ≤ ζ.im := by
    have := (abs_le.mp h1).1
    linarith
  have himpos : 0 < ζ.im := by linarith
  have h2 : ‖(ζ : ℂ)‖ ≤ ‖(τ : ℂ)‖ + 29 / 20 := by
    have h3 : ‖(ζ : ℂ)‖ ≤ ‖(τ : ℂ)‖ + ‖(ζ : ℂ) - (τ : ℂ)‖ := by
      have h4 := norm_add_le ((ζ : ℂ) - (τ : ℂ)) (τ : ℂ)
      rw [sub_add_cancel] at h4
      linarith
    linarith
  have h3 : (ζ.im)⁻¹ ≤ 20 / 11 := by
    rw [inv_le_comm₀ himpos (by norm_num)]
    linarith
  have h4 : ‖(τ : ℂ)‖ ≤ 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := by
    simpa only [Work.Kernels.scale] using Work.Kernels.coe_norm_le_scale τ
  have h5 : (1 : ℝ) ≤ 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := by
    simpa only [Work.Kernels.scale] using Work.Kernels.one_le_scale τ
  have key : (1 : ℝ) + (ζ.im)⁻¹ + ‖(ζ : ℂ)‖ ≤ 6 * (1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖) := by
    linarith
  simpa only [Work.Kernels.scale] using key

/-! ## 1. `KhatClear` and its three zeros -/

/-- The cleared kernel `K̄` is the `growthPrefactor` times `K̂` off the coincidence. -/
lemma KhatClear_eq_growthPrefactor_mul (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {τ z : ℍ}
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.KhatClear ℓ d τ z =
      Work.Kernels.growthPrefactor d τ z * Work.Kernels.Khat ℓ d τ z := by
  have h1 := Work.Kernels.ClearLink.KPlusClear_eq_smul d hd τ z h
  have h2 := Work.Kernels.ClearLink.KMinusClear_eq_smul ℓ d hd τ z h
  rw [Work.Kernels.KhatClear, h1, h2, Work.Kernels.Khat]
  ring

lemma KhatClear_self_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) : Work.Kernels.KhatClear ℓ d z z = 0 := by
  rw [Work.Kernels.KhatClear, Work.Residues.KPlusClear_diag d hd z,
    Work.Residues.KMinusClear_diag ℓ d hd z]
  ring

lemma KhatClear_vadd_one_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) : Work.Kernels.KhatClear ℓ d ((1 : ℝ) +ᵥ z) z = 0 := by
  rw [Work.Kernels.KhatClear, Work.Residues.KPlusClear_T d hd z,
    Work.Residues.KMinusClear_T ℓ d hd z]
  ring

/-- The `τ`-affinity of the cleared kernel. -/
lemma KhatClear_T2 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.KhatClear ℓ d τ z) = 0 := by
  have hp := HalfFunnel.KPlusClear_T2' d hd z
  have hm := HalfFunnel.KMinusClear_T2' ℓ d hd z
  have hsplit : (fun τ : ℍ => Work.Kernels.KhatClear ℓ d τ z)
      = fun τ : ℍ => (2 : ℂ)⁻¹ * Work.Kernels.KPlusClear d τ z
          - (2 : ℂ)⁻¹ * Work.Kernels.KMinusClear ℓ d τ z := by
    funext τ; rw [Work.Kernels.KhatClear]; ring
  rw [hsplit]
  have hsub : Work.Kernels.T2op (fun τ : ℍ => (2 : ℂ)⁻¹ * Work.Kernels.KPlusClear d τ z
        - (2 : ℂ)⁻¹ * Work.Kernels.KMinusClear ℓ d τ z)
      = Work.Kernels.T2op (fun τ : ℍ => (2 : ℂ)⁻¹ * Work.Kernels.KPlusClear d τ z)
        - Work.Kernels.T2op (fun τ : ℍ => (2 : ℂ)⁻¹ * Work.Kernels.KMinusClear ℓ d τ z) := by
    funext τ; simp only [Work.Kernels.T2op, Pi.sub_apply]; ring
  rw [hsub, HalfFunnel.T2op_const_mul, HalfFunnel.T2op_const_mul, hp, hm]
  ext τ; simp

/-- The cleared kernel vanishes at the `T` translate in the second variable. -/
lemma KhatClear_vadd_neg_one_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) : Work.Kernels.KhatClear ℓ d z ((1 : ℝ) +ᵥ z) = 0 := by
  have h := congr_fun (KhatClear_T2 ℓ d hd ((1 : ℝ) +ᵥ z)) z
  simp only [Work.Kernels.T2op, Pi.zero_apply] at h
  have h1 : Work.Kernels.KhatClear ℓ d ((2 : ℝ) +ᵥ z) ((1 : ℝ) +ᵥ z) = 0 := by
    have : ((2 : ℝ) +ᵥ z) = (1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ z) := by rw [← add_vadd]; norm_num
    rw [this]
    exact KhatClear_vadd_one_zero ℓ d hd ((1 : ℝ) +ᵥ z)
  have h2 : Work.Kernels.KhatClear ℓ d ((1 : ℝ) +ᵥ z) ((1 : ℝ) +ᵥ z) = 0 :=
    KhatClear_self_zero ℓ d hd _
  rw [h1, h2] at h
  simpa using h

/-! ## 2. The spike-circle bound for `K̂` on the funnel -/

open Work.Asymptotics.SpikeCircle in
/-- **The spike-circle bound for `K̂`**: there are `C, N, H₀` with `3 ≤ H₀` such that on the
circle `‖ζ - τ‖ = 29/20` about a funnel point `τ` of height `≥ H₀` the cleared kernel `K̂`
satisfies `‖K̂(τ,ζ)‖ ≤ C (scale τ)^N`. -/
theorem Khat_spike_circle_high (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N H₀ : ℝ, 0 < C ∧ 0 ≤ N ∧ 3 ≤ H₀ ∧
      ∀ (τ ζ : ℍ), Funnel τ → ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 → H₀ ≤ τ.im →
        ‖Work.Kernels.Khat ℓ d τ ζ‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
  rcases hd with rfl | rfl
  · obtain ⟨C1, N1, hC1, hN1, hb1⟩ := SpikeCircle.spike_KPlus8_bound
    obtain ⟨C2, N2, hC2, hN2, hb2⟩ := SpikeCircle.spike_KMinus8_bound ℓ
    refine ⟨(C1 + C2) / 2 + 1, max N1 N2, 3, by positivity, le_max_of_le_left hN1, le_refl 3, ?_⟩
    intro τ ζ hτ hζ h3
    have h1 := hb1 τ ζ hτ hζ h3
    have h2 := hb2 τ ζ hτ hζ h3
    have hs : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hN : Work.Kernels.scale τ ^ N1 ≤ Work.Kernels.scale τ ^ max N1 N2 :=
      Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _)
    have hN' : Work.Kernels.scale τ ^ N2 ≤ Work.Kernels.scale τ ^ max N1 N2 :=
      Real.rpow_le_rpow_of_exponent_le hs (le_max_right _ _)
    have hs0 : (0 : ℝ) ≤ Work.Kernels.scale τ ^ max N1 N2 :=
      Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _
    rw [Work.Kernels.Khat]
    calc ‖(Work.Kernels.KPlus 8 τ ζ - Work.Kernels.KMinus ℓ 8 τ ζ) / 2‖
        ≤ (‖Work.Kernels.KPlus 8 τ ζ‖ + ‖Work.Kernels.KMinus ℓ 8 τ ζ‖) / 2 := by
          rw [norm_div]
          have : ‖(2 : ℂ)‖ = 2 := by norm_num
          rw [this]
          have := norm_sub_le (Work.Kernels.KPlus 8 τ ζ) (Work.Kernels.KMinus ℓ 8 τ ζ)
          linarith
      _ ≤ (C1 * Work.Kernels.scale τ ^ N1 + C2 * Work.Kernels.scale τ ^ N2) / 2 := by
          linarith
      _ ≤ ((C1 + C2) / 2 + 1) * Work.Kernels.scale τ ^ max N1 N2 := by
          have hC10 : 0 ≤ C1 := hC1.le
          have hC20 : 0 ≤ C2 := hC2.le
          nlinarith [hN, hN', hs0, mul_le_mul_of_nonneg_left hN hC10,
            mul_le_mul_of_nonneg_left hN' hC20]
  · obtain ⟨H1, hSB1⟩ := SpikeCircle.SBs_KPlus24
    obtain ⟨H2, hSB2⟩ := SpikeCircle.SBs_KMinus24 ℓ
    obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hSB1
    obtain ⟨C2, N2, hC2, hN2, hb2⟩ := hSB2
    refine ⟨(C1 + C2) / 2 + 1, max N1 N2, max 3 (max H1 H2),
      by positivity, le_max_of_le_left hN1, le_max_left 3 (max H1 H2), ?_⟩
    intro τ ζ hτ hζ hH0
    have hA : H1 ≤ τ.im := le_trans (le_trans (le_max_left H1 H2) (le_max_right 3 (max H1 H2))) hH0
    have hB : H2 ≤ τ.im := le_trans (le_trans (le_max_right H1 H2) (le_max_right 3 (max H1 H2))) hH0
    have h1 := hb1 τ ζ hτ hζ hA
    have h2 := hb2 τ ζ hτ hζ hB
    simp only [Real.rpow_zero, mul_one] at h1 h2
    have hs : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hN : Work.Kernels.scale τ ^ N1 ≤ Work.Kernels.scale τ ^ max N1 N2 :=
      Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _)
    have hN' : Work.Kernels.scale τ ^ N2 ≤ Work.Kernels.scale τ ^ max N1 N2 :=
      Real.rpow_le_rpow_of_exponent_le hs (le_max_right _ _)
    have hs0 : (0 : ℝ) ≤ Work.Kernels.scale τ ^ max N1 N2 :=
      Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _
    rw [Work.Kernels.Khat]
    calc ‖(Work.Kernels.KPlus 24 τ ζ - Work.Kernels.KMinus ℓ 24 τ ζ) / 2‖
        ≤ (‖Work.Kernels.KPlus 24 τ ζ‖ + ‖Work.Kernels.KMinus ℓ 24 τ ζ‖) / 2 := by
          rw [norm_div]
          have : ‖(2 : ℂ)‖ = 2 := by norm_num
          rw [this]
          have := norm_sub_le (Work.Kernels.KPlus 24 τ ζ) (Work.Kernels.KMinus ℓ 24 τ ζ)
          linarith
      _ ≤ (C1 * Work.Kernels.scale τ ^ N1 + C2 * Work.Kernels.scale τ ^ N2) / 2 := by
          linarith
      _ ≤ ((C1 + C2) / 2 + 1) * Work.Kernels.scale τ ^ max N1 N2 := by
          have hC10 : 0 ≤ C1 := hC1.le
          have hC20 : 0 ≤ C2 := hC2.le
          nlinarith [hN, hN', hs0, mul_le_mul_of_nonneg_left hN hC10,
            mul_le_mul_of_nonneg_left hN' hC20]

/-! ## 3. The `K̂` window bound on the funnel -/

/-- **The window bound for `K̂` on the funnel, from a spike-circle bound.**

Let `E` be the exponent of `growthPrefactor`.  Given a bound `‖K̂‖ ≤ CK (scale τ)^NK` on the
spike circle `‖ζ - τ‖ = 29/20` for `Im τ ≥ H₀`, the kernel `K̂` is polynomially bounded on the
whole window `|t - Im τ| ≤ 1` (off the coincidence): the three-zero estimate for the holomorphic
`KhatClear` (whose zeros at `τ, τ±1` encode the vanishing of the residues) cancels the divisor
`j τ - j ζ` of `SpikeCircle.divisorLowerDisc`, and the exponential factors of `Δ` combine into
the bounded factor `e^{2πE(t - Im τ)}`. -/
theorem Khat_window_funnel_aux (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (E : ℕ) (hE : (if d = 8 then 1 else 2) = E) (hE1 : 1 ≤ E) (hE2 : E ≤ 2)
    (hspike : ∃ CK NK H₀ : ℝ, 0 < CK ∧ 0 ≤ NK ∧ 3 ≤ H₀ ∧
      ∀ (τ ζ : ℍ), Funnel τ → ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 → H₀ ≤ τ.im →
        ‖Work.Kernels.Khat ℓ d τ ζ‖ ≤ CK * (Work.Kernels.scale τ) ^ NK) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (τ ζ : ℍ) (t : ℝ), Funnel τ → (ζ : ℂ) = (t : ℂ) * Complex.I →
        τ.im - 1 ≤ t → t ≤ τ.im + 1 →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ →
        ‖Work.Kernels.Khat ℓ d τ ζ‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨cΔ, CΔ, hcΔ, hCΔ, hΔb⟩ := SpikeCircle.DeltaFunBoundsHalf
  obtain ⟨cd, hcd, hdiv⟩ := SpikeCircle.divisorLowerDisc
  obtain ⟨Cj, hCj, hjb⟩ := SpikeCircle.jInvariantFunUpperDisc
  obtain ⟨CK, NK, H₀, hCK, hNK, hH0, hspikeb⟩ := hspike
  obtain ⟨α, Nα, Mα, hα, hNα, hMα, hcrude⟩ :=
    norm_Khat_mul_growthPrefactor_le (ℓ := ℓ) (d := d) hd (KClear_mg2 ℓ d hd).2
  have hEcases : E = 1 ∨ E = 2 := by omega
  set ρ : ℝ := 29 / 20 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; norm_num
  set δ : ℝ := ρ * (9 / 20) * (9 / 20) with hδdef
  have hδpos : 0 < δ := by rw [hδdef, hρdef]; norm_num
  set c0 : ℝ := min cΔ (cΔ ^ 2) with hc0def
  have hc0pos : 0 < c0 := lt_min hcΔ (pow_pos hcΔ 2)
  set Kout : ℝ := 1 / (cΔ * c0 * cd * δ) with hKoutdef
  have hKoutpos : 0 < Kout := by rw [hKoutdef]; positivity
  set CΔup : ℝ := max CΔ (max (CΔ ^ 2) (CΔ ^ 3)) * Real.exp (4 * Real.pi * (29 / 20)) with hCΔupdef
  have hCΔup0 : 0 ≤ CΔup := by rw [hCΔupdef]; positivity
  set K1 : ℝ := Kout * (α * 6 ^ Mα * Real.exp (4 * Real.pi * (H₀ + 1))) with hK1def
  set K2 : ℝ := Kout * (CΔup * Cj * CK * Real.exp (4 * Real.pi)) with hK2def
  have hK1nn : 0 ≤ K1 := by rw [hK1def]; positivity
  have hK2nn : 0 ≤ K2 := by rw [hK2def]; positivity
  refine ⟨K1 + K2 + 1, max (Nα + Mα) NK, by linarith,
    le_trans (by linarith) (le_max_left _ _), ?_⟩
  intro τ ζ t hτ hζ ht1 ht2 hJ
  -- ## basic facts
  have hT : (2 : ℝ) ≤ τ.im := hτ.2
  have htpos : 0 < t := by linarith
  have hζim : ζ.im = t := by
    have h : ((ζ : ℂ)).im = t := by rw [hζ]; simp
    simpa using h
  have hζhalf : (1 / 2 : ℝ) ≤ ζ.im := by rw [hζim]; linarith
  have hτre_lt : τ.re < 1 := (mem_DomainD.mp hτ.1).2.1
  have hτre_gt : -1 < τ.re := (mem_DomainD.mp hτ.1).1
  have hρτ : ρ < τ.im := by rw [hρdef]; linarith
  have hsq : ‖(ζ : ℂ) - (τ : ℂ)‖ ^ 2 = τ.re ^ 2 + (t - τ.im) ^ 2 := by
    rw [hζ, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im]
    ring
  have hdistlt : ‖(ζ : ℂ) - (τ : ℂ)‖ < ρ := by
    have h1 : τ.re ^ 2 < 1 := by
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - τ.re)
        (by linarith : (0 : ℝ) < 1 + τ.re)]
    have h2 : (t - τ.im) ^ 2 ≤ 1 := by
      have hh : -(1 : ℝ) ≤ t - τ.im ∧ t - τ.im ≤ 1 := ⟨by linarith, by linarith⟩
      have := (sq_le_sq (a := t - τ.im) (b := (1 : ℝ))).mpr (by simpa using abs_le.mpr hh)
      simpa using this
    have h3 : ‖(ζ : ℂ) - (τ : ℂ)‖ ^ 2 < (29 / 20 : ℝ) ^ 2 := by
      rw [hsq]; nlinarith
    rw [hρdef]
    have h4 : |‖(ζ : ℂ) - (τ : ℂ)‖| < |(29 / 20 : ℝ)| := by
      rw [← sq_lt_sq]; simpa using h3
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 29 / 20)] at h4
    rw [abs_of_nonneg (norm_nonneg _)] at h4
    exact h4
  have hdistle : ‖(ζ : ℂ) - (τ : ℂ)‖ ≤ ρ := le_of_lt hdistlt
  -- ## the holomorphic function and its three zeros
  set f : ℂ → ℂ := fun u => Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex u) with hfdef
  have hfval : ∀ u : ℂ, f u = Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex u) :=
    fun u => by rw [hfdef]
  have hclosed : Metric.closedBall ((τ : ℂ)) ρ ⊆ {u : ℂ | 0 < u.im} := by
    intro u hu
    have h1 : ‖u - (τ : ℂ)‖ ≤ ρ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hu
    have him : |u.im - τ.im| ≤ ρ := by
      have h2 : |(u - (τ : ℂ)).im| ≤ ‖u - (τ : ℂ)‖ := Complex.abs_im_le_norm _
      have h3 : (u - (τ : ℂ)).im = u.im - τ.im := by
        rw [Complex.sub_im, UpperHalfPlane.coe_im]
      rw [h3] at h2
      linarith
    have h4 := (abs_le.mp him).1
    show 0 < u.im
    linarith
  have hf : DiffContOnCl ℂ f (Metric.ball ((τ : ℂ)) ρ) := by
    have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : ℍ => Work.Kernels.KhatClear ℓ d τ z) :=
      (Work.Kernels.KernelClear_growth_z ℓ d hd τ).2.1
    have hdiff : DifferentiableOn ℂ
        (fun u : ℂ => Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex u))
        {u : ℂ | 0 < u.im} := (UpperHalfPlane.mdifferentiable_iff).mp hmd
    exact hdiff.diffContOnCl_ball hclosed
  have hsphere_le : ∀ u ∈ Metric.sphere ((τ : ℂ)) ρ, ‖u - (τ : ℂ)‖ = ρ := by
    intro u hu
    rwa [Metric.mem_sphere, dist_eq_norm] at hu
  have him_sphere : ∀ u ∈ Metric.sphere ((τ : ℂ)) ρ, 0 < u.im := by
    intro u hu
    have h1 : |u.im - τ.im| ≤ ρ := by
      have h2 : |(u - (τ : ℂ)).im| ≤ ‖u - (τ : ℂ)‖ := Complex.abs_im_le_norm _
      have h3 : (u - (τ : ℂ)).im = u.im - τ.im := by
        rw [Complex.sub_im, UpperHalfPlane.coe_im]
      rw [h3] at h2
      rw [hsphere_le u hu] at h2
      exact h2
    have h4 := (abs_le.mp h1).1
    show 0 < u.im
    linarith
  have hsphere_prod : ∀ u ∈ Metric.sphere ((τ : ℂ)) ρ,
      δ ≤ ‖u - (τ : ℂ)‖ * ‖u - ((τ : ℂ) - 1)‖ * ‖u - ((τ : ℂ) + 1)‖ := by
    intro u hu
    have hu' := hsphere_le u hu
    have h1 : (9 / 20 : ℝ) ≤ ‖u - ((τ : ℂ) + 1)‖ := by
      have h := abs_norm_sub_norm_le (u - (τ : ℂ)) (1 : ℂ)
      have h2 : (u - (τ : ℂ)) - 1 = u - ((τ : ℂ) + 1) := by ring
      rw [h2, hu', norm_one] at h
      have h3 : |ρ - 1| = 9 / 20 := by rw [hρdef]; norm_num
      rw [h3] at h
      exact h
    have h4 : (9 / 20 : ℝ) ≤ ‖u - ((τ : ℂ) - 1)‖ := by
      have h := abs_norm_sub_norm_le (u - (τ : ℂ)) (-1 : ℂ)
      have h2 : (u - (τ : ℂ)) - (-1) = u - ((τ : ℂ) - 1) := by ring
      rw [h2, hu', norm_neg, norm_one] at h
      have h3 : |ρ - 1| = 9 / 20 := by rw [hρdef]; norm_num
      rw [h3] at h
      exact h
    rw [hδdef, hu']
    have step1 : ρ * (9 / 20) ≤ ρ * ‖u - ((τ : ℂ) + 1)‖ :=
      mul_le_mul_of_nonneg_left h1 hρpos.le
    have step2 : ρ * (9 / 20) * (9 / 20)
        ≤ (ρ * ‖u - ((τ : ℂ) + 1)‖) * ‖u - ((τ : ℂ) - 1)‖ :=
      mul_le_mul step1 h4 (by norm_num) (by positivity)
    calc ρ * (9 / 20) * (9 / 20)
        = ρ * (9 / 20) * (9 / 20) := rfl
      _ ≤ (ρ * ‖u - ((τ : ℂ) + 1)‖) * ‖u - ((τ : ℂ) - 1)‖ := step2
      _ = ρ * ‖u - ((τ : ℂ) - 1)‖ * ‖u - ((τ : ℂ) + 1)‖ := by ring
  have hz1 : f (τ : ℂ) = 0 := by
    rw [hfval, UpperHalfPlane.ofComplex_apply]
    exact KhatClear_self_zero ℓ d hd τ
  have hz2 : f ((τ : ℂ) - 1) = 0 := by
    have him : 0 < (((τ : ℂ) - 1)).im := by
      rw [Complex.sub_im, UpperHalfPlane.coe_im]; norm_num; exact τ.im_pos
    rw [hfval]
    have hcoe : UpperHalfPlane.ofComplex ((τ : ℂ) - 1) = (-1 : ℝ) +ᵥ τ := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos him, UpperHalfPlane.coe_vadd]
      push_cast; ring
    rw [hcoe]
    have h := KhatClear_vadd_one_zero ℓ d hd ((-1 : ℝ) +ᵥ τ)
    have h2 : ((1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ)) = τ := by rw [← add_vadd]; norm_num
    rw [h2] at h
    exact h
  have hz3 : f ((τ : ℂ) + 1) = 0 := by
    have him : 0 < (((τ : ℂ) + 1)).im := by
      rw [Complex.add_im, UpperHalfPlane.coe_im]; norm_num; exact τ.im_pos
    rw [hfval]
    have hcoe : UpperHalfPlane.ofComplex ((τ : ℂ) + 1) = (1 : ℝ) +ᵥ τ := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos him, UpperHalfPlane.coe_vadd]
      push_cast; ring
    rw [hcoe]
    exact KhatClear_vadd_neg_one_zero ℓ d hd τ
  have hz12 : (τ : ℂ) ≠ (τ : ℂ) - 1 := by
    intro h
    have h' : (1 : ℂ) = 0 := by linear_combination h
    exact one_ne_zero h'
  have hz13 : (τ : ℂ) ≠ (τ : ℂ) + 1 := by
    intro h
    have h' : (1 : ℂ) = 0 := by linear_combination -h
    exact one_ne_zero h'
  have hz23 : (τ : ℂ) - 1 ≠ (τ : ℂ) + 1 := by
    intro h
    have h' : (2 : ℂ) = 0 := by linear_combination -h
    norm_num at h'
  -- ## the ball bound from a circle bound
  have ball_of_sphere : ∀ M : ℝ, (∀ u ∈ Metric.sphere ((τ : ℂ)) ρ, ‖f u‖ ≤ M) →
      ∀ u ∈ Metric.ball ((τ : ℂ)) ρ, ‖f u‖ ≤ M := by
    intro M hsp u hu
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hf ?_ (subset_closure hu)
    intro u hu'
    exact hsp u (Metric.frontier_ball_subset_sphere hu')
  -- ## the circle bounds
  have hJsphere : ∀ u ∈ Metric.sphere ((τ : ℂ)) ρ,
      Work.Kernels.jInvariantFun τ
        ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex u) := by
    intro u hu
    have him := him_sphere u hu
    have hcoe : ((UpperHalfPlane.ofComplex u : ℍ) : ℂ) = u := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
    intro hcon
    have hd := hdiv τ (UpperHalfPlane.ofComplex u) hτ (by rw [hcoe]; exact le_of_eq (hsphere_le u hu))
    rw [hcon, sub_self, norm_zero] at hd
    rw [hcoe] at hd
    have hpos : 0 < cd * Real.exp (2 * Real.pi * τ.im)
        * ‖(u - (τ : ℂ)) * (u - ((τ : ℂ) - 1)) * (u - ((τ : ℂ) + 1))‖ := by
      have h1 : 0 < cd * Real.exp (2 * Real.pi * τ.im) := by positivity
      have h2 : 0 < ‖(u - (τ : ℂ)) * (u - ((τ : ℂ) - 1)) * (u - ((τ : ℂ) + 1))‖ := by
        rw [norm_mul, norm_mul]
        have h3 := hsphere_prod u hu
        linarith [hδpos, h3]
      exact mul_pos h1 h2
    linarith
  have hsphere_crude : ∀ u ∈ Metric.sphere ((τ : ℂ)) ρ,
      ‖f u‖ ≤ α * 6 ^ Mα * (Work.Kernels.scale τ) ^ (Nα + Mα) := by
    intro u hu
    have him := him_sphere u hu
    have hcoe : ((UpperHalfPlane.ofComplex u : ℍ) : ℂ) = u := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
    have hJ' := hJsphere u hu
    have hsc : Work.Kernels.scale (UpperHalfPlane.ofComplex u) ≤ 6 * Work.Kernels.scale τ := by
      refine scale_le_six_of_norm_sub_le hT ?_
      rw [hcoe]; exact le_of_eq (hsphere_le u hu)
    have hcr := hcrude τ (UpperHalfPlane.ofComplex u)
    have hcle := KhatClear_eq_growthPrefactor_mul ℓ d hd hJ'
    have hpow : (Work.Kernels.scale (UpperHalfPlane.ofComplex u)) ^ Mα
        ≤ (6 * Work.Kernels.scale τ) ^ Mα :=
      Real.rpow_le_rpow (Work.Kernels.scale_pos _).le hsc hMα
    have hs1 : (0 : ℝ) ≤ Work.Kernels.scale τ := (Work.Kernels.scale_pos τ).le
    have hsplit : α * (Work.Kernels.scale τ) ^ Nα * (6 * Work.Kernels.scale τ) ^ Mα
        = α * 6 ^ Mα * (Work.Kernels.scale τ) ^ (Nα + Mα) := by
      have h1 : (6 * Work.Kernels.scale τ) ^ Mα
          = 6 ^ Mα * (Work.Kernels.scale τ) ^ Mα :=
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) hs1
      have h2 : (Work.Kernels.scale τ) ^ Nα * (Work.Kernels.scale τ) ^ Mα
          = (Work.Kernels.scale τ) ^ (Nα + Mα) :=
        (Real.rpow_add (Work.Kernels.scale_pos τ) Nα Mα).symm
      rw [h1]
      linear_combination (α * 6 ^ Mα) * h2
    calc ‖f u‖ = ‖Work.Kernels.growthPrefactor d τ (UpperHalfPlane.ofComplex u)
          * Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex u)‖ := by rw [hfval u, hcle]
      _ = ‖Work.Kernels.growthPrefactor d τ (UpperHalfPlane.ofComplex u)‖
          * ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex u)‖ := norm_mul _ _
      _ ≤ α * (Work.Kernels.scale τ) ^ Nα * (Work.Kernels.scale (UpperHalfPlane.ofComplex u)) ^ Mα := by
          rw [mul_comm]; exact hcr
      _ ≤ α * (Work.Kernels.scale τ) ^ Nα * (6 * Work.Kernels.scale τ) ^ Mα :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = α * 6 ^ Mα * (Work.Kernels.scale τ) ^ (Nα + Mα) := hsplit
  have hsphere_sharp : ∀ (hH : H₀ ≤ τ.im) (u : ℂ), u ∈ Metric.sphere ((τ : ℂ)) ρ →
      ‖f u‖ ≤ CΔup * Cj * CK * Real.exp (-(2 * Real.pi * (E : ℝ) * τ.im))
        * (Work.Kernels.scale τ) ^ NK := by
    intro hH u hu
    have him := him_sphere u hu
    have hcoe : ((UpperHalfPlane.ofComplex u : ℍ) : ℂ) = u := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
    have hJ' := hJsphere u hu
    have hcle := KhatClear_eq_growthPrefactor_mul ℓ d hd hJ'
    -- imaginary parts
    have himabs : |(UpperHalfPlane.ofComplex u).im - τ.im| ≤ ρ := by
      have h2 : |((UpperHalfPlane.ofComplex u : ℍ) : ℂ).im - τ.im| ≤ ρ := by
        rw [hcoe]
        have h4 : |(u - (τ : ℂ)).im| ≤ ‖u - (τ : ℂ)‖ := Complex.abs_im_le_norm _
        have h5 : (u - (τ : ℂ)).im = u.im - τ.im := by
          rw [Complex.sub_im, UpperHalfPlane.coe_im]
        rw [h5, hsphere_le u hu] at h4
        exact h4
      simpa using h2
    have bim : (1 / 2 : ℝ) ≤ (UpperHalfPlane.ofComplex u).im := by
      have h1 : τ.im - 29 / 20 ≤ (UpperHalfPlane.ofComplex u).im := by
        have h := (abs_le.mp himabs).1
        rw [hρdef] at h
        linarith
      linarith [h1, hT]
    have blim : (UpperHalfPlane.ofComplex u).im ≤ τ.im + ρ := by linarith [(abs_le.mp himabs).2]
    have b1 : ‖Work.Kernels.DeltaFun τ‖ ≤ CΔ * Real.exp (-(2 * Real.pi * τ.im)) :=
      (hΔb τ (le_trans (by norm_num) hT)).2
    have b2 : ‖Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex u) ^ E‖
        ≤ CΔ ^ E * Real.exp (-(2 * Real.pi * (E : ℝ) * (τ.im - ρ))) := by
      have h1 : ‖Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex u)‖
          ≤ CΔ * Real.exp (-(2 * Real.pi * (UpperHalfPlane.ofComplex u).im)) := (hΔb _ bim).2
      have h2 : CΔ * Real.exp (-(2 * Real.pi * (UpperHalfPlane.ofComplex u).im))
          ≤ CΔ * Real.exp (-(2 * Real.pi * (τ.im - ρ))) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCΔ.le
        have hle : τ.im - ρ ≤ (UpperHalfPlane.ofComplex u).im := by
          linarith [(abs_le.mp himabs).1]
        have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
        have := mul_le_mul_of_nonneg_left hle hpi
        linarith
      have h3 : (CΔ * Real.exp (-(2 * Real.pi * (UpperHalfPlane.ofComplex u).im))) ^ E
          = CΔ ^ E * Real.exp (-(2 * Real.pi * (E : ℝ) * (UpperHalfPlane.ofComplex u).im)) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
      have h4 : Real.exp (-(2 * Real.pi * (E : ℝ) * (UpperHalfPlane.ofComplex u).im))
          ≤ Real.exp (-(2 * Real.pi * (E : ℝ) * (τ.im - ρ))) := by
        refine Real.exp_le_exp.mpr ?_
        have hle : τ.im - ρ ≤ (UpperHalfPlane.ofComplex u).im := by
          linarith [(abs_le.mp himabs).1]
        have hpi : (0 : ℝ) ≤ 2 * Real.pi * (E : ℝ) := by positivity
        have := mul_le_mul_of_nonneg_left hle hpi
        linarith
      rw [norm_pow]
      calc ‖Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex u)‖ ^ E
          ≤ (CΔ * Real.exp (-(2 * Real.pi * (UpperHalfPlane.ofComplex u).im))) ^ E :=
            pow_le_pow_left₀ (by positivity) h1 E
        _ = CΔ ^ E * Real.exp (-(2 * Real.pi * (E : ℝ) * (UpperHalfPlane.ofComplex u).im)) := h3
        _ ≤ CΔ ^ E * Real.exp (-(2 * Real.pi * (E : ℝ) * (τ.im - ρ))) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
    have b3 : ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex u)‖
        ≤ Cj * Real.exp (2 * Real.pi * τ.im) :=
      hjb τ _ hτ (by rw [hcoe]; exact le_of_eq (hsphere_le u hu))
    have b4 : ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex u)‖
        ≤ CK * (Work.Kernels.scale τ) ^ NK :=
      hspikeb τ _ hτ (by rw [hcoe]; exact hsphere_le u hu) hH
    have hgoal : ‖f u‖ ≤ CΔ * Real.exp (-(2 * Real.pi * τ.im))
          * (CΔ ^ E * Real.exp (-(2 * Real.pi * (E : ℝ) * (τ.im - ρ))))
          * (Cj * Real.exp (2 * Real.pi * τ.im)) * (CK * (Work.Kernels.scale τ) ^ NK) := by
      calc ‖f u‖ = ‖Work.Kernels.growthPrefactor d τ (UpperHalfPlane.ofComplex u)‖
            * ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex u)‖ := by
            rw [hfval u, hcle, norm_mul]
        _ = ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex u) ^ E‖
            * ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex u)‖
            * ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex u)‖ := by
            simp only [Work.Kernels.growthPrefactor, hE, norm_mul]
        _ ≤ CΔ * Real.exp (-(2 * Real.pi * τ.im))
            * (CΔ ^ E * Real.exp (-(2 * Real.pi * (E : ℝ) * (τ.im - ρ))))
            * (Cj * Real.exp (2 * Real.pi * τ.im)) * (CK * (Work.Kernels.scale τ) ^ NK) := by
            refine mul_le_mul (mul_le_mul (mul_le_mul b1 b2 (by positivity) (by positivity))
              b3 (by positivity) (by positivity)) b4 (by positivity) (by positivity)
    -- absorb the constants and the `e^{2πEρ}` factor
    have hCΔpow : CΔ ^ (E + 1) ≤ max CΔ (max (CΔ ^ 2) (CΔ ^ 3)) := by
      rcases hEcases with h | h
      · subst h
        exact le_trans (le_max_left _ _) (le_max_right _ _)
      · subst h
        exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hcue : Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im) = 1 := by
      rw [← Real.exp_add]; norm_num
    have hsplit2 : Real.exp (-(2 * Real.pi * (E : ℝ) * (τ.im - ρ)))
        = Real.exp (-(2 * Real.pi * (E : ℝ) * τ.im)) * Real.exp (2 * Real.pi * (E : ℝ) * ρ) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexpρ : Real.exp (2 * Real.pi * (E : ℝ) * ρ) ≤ Real.exp (4 * Real.pi * ρ) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : (E : ℝ) ≤ 2 := by exact_mod_cast hE2
      have h2 : (0 : ℝ) ≤ 2 * Real.pi * ρ := by positivity
      calc 2 * Real.pi * (E : ℝ) * ρ = (2 * Real.pi * ρ) * E := by ring
        _ ≤ (2 * Real.pi * ρ) * 2 := mul_le_mul_of_nonneg_left h1 h2
        _ = 4 * Real.pi * ρ := by ring
    have hcomb : CΔ * Real.exp (-(2 * Real.pi * τ.im))
          * (CΔ ^ E * Real.exp (-(2 * Real.pi * (E : ℝ) * (τ.im - ρ))))
          * (Cj * Real.exp (2 * Real.pi * τ.im)) * (CK * (Work.Kernels.scale τ) ^ NK)
        ≤ CΔup * Cj * CK * Real.exp (-(2 * Real.pi * (E : ℝ) * τ.im))
          * (Work.Kernels.scale τ) ^ NK := by
      have hLHS : CΔ * Real.exp (-(2 * Real.pi * τ.im))
            * (CΔ ^ E * Real.exp (-(2 * Real.pi * (E : ℝ) * (τ.im - ρ))))
            * (Cj * Real.exp (2 * Real.pi * τ.im)) * (CK * (Work.Kernels.scale τ) ^ NK)
          = CΔ ^ (E + 1) * Cj * CK * Real.exp (-(2 * Real.pi * (E : ℝ) * τ.im))
            * Real.exp (2 * Real.pi * (E : ℝ) * ρ) * (Work.Kernels.scale τ) ^ NK := by
        have hgroup : CΔ * Real.exp (-(2 * Real.pi * τ.im))
              * (CΔ ^ E * Real.exp (-(2 * Real.pi * (E : ℝ) * (τ.im - ρ))))
              * (Cj * Real.exp (2 * Real.pi * τ.im)) * (CK * (Work.Kernels.scale τ) ^ NK)
            = (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im))
              * (CΔ * CΔ ^ E * Real.exp (-(2 * Real.pi * (E : ℝ) * (τ.im - ρ))) * Cj * CK
                * (Work.Kernels.scale τ) ^ NK) := by ring
        rw [hgroup, hcue, one_mul, hsplit2]
        ring
      rw [hLHS]
      have hstep : CΔ ^ (E + 1) * Real.exp (2 * Real.pi * (E : ℝ) * ρ)
          ≤ max CΔ (max (CΔ ^ 2) (CΔ ^ 3)) * Real.exp (4 * Real.pi * ρ) :=
        mul_le_mul hCΔpow hexpρ (by positivity) (by positivity)
      calc CΔ ^ (E + 1) * Cj * CK * Real.exp (-(2 * Real.pi * (E : ℝ) * τ.im))
            * Real.exp (2 * Real.pi * (E : ℝ) * ρ) * (Work.Kernels.scale τ) ^ NK
          = (CΔ ^ (E + 1) * Real.exp (2 * Real.pi * (E : ℝ) * ρ))
            * (Cj * CK * Real.exp (-(2 * Real.pi * (E : ℝ) * τ.im))
              * (Work.Kernels.scale τ) ^ NK) := by ring
        _ ≤ (max CΔ (max (CΔ ^ 2) (CΔ ^ 3)) * Real.exp (4 * Real.pi * ρ))
            * (Cj * CK * Real.exp (-(2 * Real.pi * (E : ℝ) * τ.im))
              * (Work.Kernels.scale τ) ^ NK) :=
            mul_le_mul_of_nonneg_right hstep
              (mul_nonneg (mul_nonneg (mul_nonneg hCj.le hCK.le) (Real.exp_pos _).le)
                (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _))
        _ = CΔup * Cj * CK * Real.exp (-(2 * Real.pi * (E : ℝ) * τ.im))
            * (Work.Kernels.scale τ) ^ NK := by
            rw [hCΔupdef]; ring
    exact le_trans hgoal hcomb
  -- ## the shared core: three zeros + divisor
  have core : ∀ M : ℝ, 0 ≤ M →
      (∀ u ∈ Metric.ball ((τ : ℂ)) ρ, ‖f u‖ ≤ M) →
      ‖Work.Kernels.Khat ℓ d τ ζ‖ ≤ M * Kout * Real.exp (2 * Real.pi * (E : ℝ) * t) := by
    intro M hM hball
    have h3z := three_zeros_bound_ball (f := f) (c := (τ : ℂ)) (ρ := ρ) (M := M) (δ := δ)
      hρpos hM hδpos hf hball hz12 hz13 hz23 hz1 hz2 hz3 hsphere_prod
    have hζball : (ζ : ℂ) ∈ Metric.ball ((τ : ℂ)) ρ :=
      Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hdistlt)
    have h1 := h3z (ζ : ℂ) hζball
    have hfζ : f (ζ : ℂ) = Work.Kernels.KhatClear ℓ d τ ζ := by
      rw [hfval, UpperHalfPlane.ofComplex_apply]
    rw [hfζ] at h1
    -- ### the lower bounds for the two `Δ` factors
    have hΔτ : cΔ * Real.exp (-(2 * Real.pi * τ.im)) ≤ ‖Work.Kernels.DeltaFun τ‖ :=
      (hΔb τ (le_trans (by norm_num) hT)).1
    have hexpE : (Real.exp (-(2 * Real.pi * ζ.im))) ^ E
        = Real.exp (-(2 * Real.pi * (E : ℝ) * ζ.im)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have hΔζ : c0 * Real.exp (-(2 * Real.pi * (E : ℝ) * t))
        ≤ ‖Work.Kernels.DeltaFun ζ ^ E‖ := by
      have h1' : cΔ * Real.exp (-(2 * Real.pi * ζ.im)) ≤ ‖Work.Kernels.DeltaFun ζ‖ :=
        (hΔb ζ hζhalf).1
      have h2' : cΔ ^ E * (Real.exp (-(2 * Real.pi * ζ.im))) ^ E
          ≤ ‖Work.Kernels.DeltaFun ζ‖ ^ E := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) h1' E
      have h3' : c0 ≤ cΔ ^ E := by
        rcases hEcases with h | h <;> subst h <;> simp [hc0def]
      have h4' : c0 * Real.exp (-(2 * Real.pi * (E : ℝ) * t))
          ≤ cΔ ^ E * (Real.exp (-(2 * Real.pi * ζ.im))) ^ E := by
        rw [← hζim, hexpE]
        exact mul_le_mul_of_nonneg_right h3' (Real.exp_pos _).le
      rw [norm_pow]
      exact le_trans h4' h2'
    -- ### the divisor, in the normalisation `P`
    set P : ℝ := ‖(ζ : ℂ) - (τ : ℂ)‖ * ‖(ζ : ℂ) - ((τ : ℂ) - 1)‖ * ‖(ζ : ℂ) - ((τ : ℂ) + 1)‖
      with hPdef
    have hjneg : Work.Kernels.jInvariantFun ((-1 : ℝ) +ᵥ τ) = Work.Kernels.jInvariantFun τ := by
      have h := Work.Kernels.KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ τ)
      rw [show ((1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ)) = τ from by rw [← add_vadd]; norm_num] at h
      exact h.symm
    have hPpos : 0 < P := by
      rw [hPdef]
      have h2 : 0 < ‖(ζ : ℂ) - (τ : ℂ)‖ := by
        rw [norm_pos_iff]
        intro h
        exact hJ (by rw [UpperHalfPlane.ext (sub_eq_zero.mp h)])
      have h3 : 0 < ‖(ζ : ℂ) - ((τ : ℂ) - 1)‖ := by
        rw [norm_pos_iff]
        intro h
        have hζτ : ζ = (-1 : ℝ) +ᵥ τ := by
          apply UpperHalfPlane.ext
          rw [UpperHalfPlane.coe_vadd]
          push_cast
          rw [sub_eq_zero.mp h]
          ring
        exact hJ (by rw [hζτ, hjneg])
      have h4 : 0 < ‖(ζ : ℂ) - ((τ : ℂ) + 1)‖ := by
        rw [norm_pos_iff]
        intro h
        have hζτ : ζ = (1 : ℝ) +ᵥ τ := by
          apply UpperHalfPlane.ext
          rw [UpperHalfPlane.coe_vadd]
          push_cast
          rw [sub_eq_zero.mp h]
          ring
        exact hJ (by rw [hζτ, Work.Kernels.KernelFacts.jInvariantFun_vadd_one])
      positivity
    have hPnorm : ‖((ζ : ℂ) - (τ : ℂ)) * ((ζ : ℂ) - ((τ : ℂ) - 1)) * ((ζ : ℂ) - ((τ : ℂ) + 1))‖
        = P := by
      rw [hPdef, norm_mul, norm_mul]
    have hdiv' : cd * Real.exp (2 * Real.pi * τ.im) * P
        ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖ := by
      have h := hdiv τ ζ hτ hdistle
      rwa [hPnorm] at h
    -- ### the lower bound for the growth prefactor
    have hgp_eq : ‖Work.Kernels.growthPrefactor d τ ζ‖
        = ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun ζ ^ E‖
          * ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖ := by
      simp only [Work.Kernels.growthPrefactor, hE, norm_mul]
    have hXpos : 0 < cΔ * c0 * cd * P * Real.exp (-(2 * Real.pi * (E : ℝ) * t)) :=
      mul_pos (mul_pos (mul_pos (mul_pos hcΔ hc0pos) hcd) hPpos) (Real.exp_pos _)
    have hden : cΔ * c0 * cd * P * Real.exp (-(2 * Real.pi * (E : ℝ) * t))
        ≤ ‖Work.Kernels.growthPrefactor d τ ζ‖ := by
      rw [hgp_eq]
      have hXeq : cΔ * c0 * cd * P * Real.exp (-(2 * Real.pi * (E : ℝ) * t))
          = (cΔ * Real.exp (-(2 * Real.pi * τ.im)))
            * (c0 * Real.exp (-(2 * Real.pi * (E : ℝ) * t)))
            * (cd * Real.exp (2 * Real.pi * τ.im) * P) := by
        have hx : Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im) = 1 := by
          rw [← Real.exp_add]; norm_num
        calc cΔ * c0 * cd * P * Real.exp (-(2 * Real.pi * (E : ℝ) * t))
            = (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im))
              * (cΔ * c0 * cd * P * Real.exp (-(2 * Real.pi * (E : ℝ) * t))) := by
              rw [hx]; ring
          _ = (cΔ * Real.exp (-(2 * Real.pi * τ.im)))
              * (c0 * Real.exp (-(2 * Real.pi * (E : ℝ) * t)))
              * (cd * Real.exp (2 * Real.pi * τ.im) * P) := by ring
      rw [hXeq]
      exact mul_le_mul
        (mul_le_mul hΔτ hΔζ (mul_nonneg hc0pos.le (Real.exp_pos _).le) (norm_nonneg _))
        hdiv' (mul_nonneg (mul_nonneg hcd.le (Real.exp_pos _).le) hPpos.le)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hgppos : 0 < ‖Work.Kernels.growthPrefactor d τ ζ‖ := lt_of_lt_of_le hXpos hden
    have hKhat : ‖Work.Kernels.Khat ℓ d τ ζ‖
        = ‖Work.Kernels.KhatClear ℓ d τ ζ‖ / ‖Work.Kernels.growthPrefactor d τ ζ‖ := by
      have hcle := KhatClear_eq_growthPrefactor_mul ℓ d hd hJ
      rw [hcle, norm_mul, eq_div_iff (ne_of_gt hgppos)]
      ring
    have h1P : ‖Work.Kernels.KhatClear ℓ d τ ζ‖ ≤ (M / δ) * P := by
      rw [hPdef]
      calc ‖Work.Kernels.KhatClear ℓ d τ ζ‖
          ≤ (M / δ) * ‖(ζ : ℂ) - (τ : ℂ)‖ * ‖(ζ : ℂ) - ((τ : ℂ) - 1)‖
            * ‖(ζ : ℂ) - ((τ : ℂ) + 1)‖ := h1
        _ = (M / δ) * (‖(ζ : ℂ) - (τ : ℂ)‖ * ‖(ζ : ℂ) - ((τ : ℂ) - 1)‖
            * ‖(ζ : ℂ) - ((τ : ℂ) + 1)‖) := by ring
    calc ‖Work.Kernels.Khat ℓ d τ ζ‖
        = ‖Work.Kernels.KhatClear ℓ d τ ζ‖ / ‖Work.Kernels.growthPrefactor d τ ζ‖ := hKhat
      _ ≤ ((M / δ) * P) / (cΔ * c0 * cd * P * Real.exp (-(2 * Real.pi * (E : ℝ) * t))) := by
          rw [le_div_iff₀ hXpos, div_mul_eq_mul_div]
          exact (div_le_iff₀ hgppos).mpr
            (mul_le_mul h1P hden hXpos.le (mul_nonneg (div_nonneg hM hδpos.le) hPpos.le))
      _ = M * Kout * Real.exp (2 * Real.pi * (E : ℝ) * t) := by
          rw [hKoutdef]
          have hx : Real.exp (-(2 * Real.pi * (E : ℝ) * t)) * Real.exp (2 * Real.pi * (E : ℝ) * t) = 1 := by
            rw [← Real.exp_add]; ring_nf; norm_num
          field_simp [hPpos.ne', hδpos.ne', hcΔ.ne', hc0pos.ne', hcd.ne']
          have hMM : M * Real.exp (-(2 * Real.pi * (E : ℝ) * t))
              * Real.exp (2 * Real.pi * (E : ℝ) * t) = M := by
            rw [mul_assoc, hx, mul_one]
          rw [hMM]
  -- ## the two regimes for the circle bound
  by_cases hcase : τ.im ≤ H₀
  · have hb := ball_of_sphere (α * 6 ^ Mα * (Work.Kernels.scale τ) ^ (Nα + Mα)) hsphere_crude
    have hc := core _
      (mul_nonneg (mul_nonneg hα (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 6) Mα))
        (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _)) hb
    have hexp : Real.exp (2 * Real.pi * (E : ℝ) * t) ≤ Real.exp (4 * Real.pi * (H₀ + 1)) := by
      refine Real.exp_le_exp.mpr ?_
      have ht : t ≤ H₀ + 1 := by linarith
      have h1 : (E : ℝ) ≤ 2 := by exact_mod_cast hE2
      have h2 : (0 : ℝ) ≤ t := htpos.le
      calc 2 * Real.pi * (E : ℝ) * t ≤ 2 * Real.pi * 2 * t := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
        _ ≤ 2 * Real.pi * 2 * (H₀ + 1) :=
            mul_le_mul_of_nonneg_left ht (by positivity)
        _ = 4 * Real.pi * (H₀ + 1) := by ring
    have hN : (Work.Kernels.scale τ) ^ (Nα + Mα)
        ≤ (Work.Kernels.scale τ) ^ (max (Nα + Mα) NK) :=
      Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ) (le_max_left _ _)
    have hN0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ (max (Nα + Mα) NK) :=
      Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _
    have hNs : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ (Nα + Mα) :=
      Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _
    calc ‖Work.Kernels.Khat ℓ d τ ζ‖
        ≤ α * 6 ^ Mα * (Work.Kernels.scale τ) ^ (Nα + Mα) * Kout
          * Real.exp (2 * Real.pi * (E : ℝ) * t) := hc
      _ = (α * 6 ^ Mα * Real.exp (2 * Real.pi * (E : ℝ) * t)) * Kout
            * (Work.Kernels.scale τ) ^ (Nα + Mα) := by ring
      _ ≤ (α * 6 ^ Mα * Real.exp (4 * Real.pi * (H₀ + 1))) * Kout
            * (Work.Kernels.scale τ) ^ (Nα + Mα) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hKoutpos.le) hNs
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = K1 * (Work.Kernels.scale τ) ^ (Nα + Mα) := by rw [hK1def]; ring
      _ ≤ (K1 + K2 + 1) * (Work.Kernels.scale τ) ^ (max (Nα + Mα) NK) := by
          refine mul_le_mul ?_ hN hNs (by linarith)
          linarith
  · have hH : H₀ ≤ τ.im := le_of_not_ge hcase
    set Mv : ℝ := CΔup * Cj * CK * Real.exp (-(2 * Real.pi * (E : ℝ) * τ.im))
      * (Work.Kernels.scale τ) ^ NK with hMv
    have hb := ball_of_sphere Mv (by rw [hMv]; exact hsphere_sharp hH)
    have hc := core Mv (by
      rw [hMv]
      refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCΔup0 hCj.le) hCK.le)
        (Real.exp_pos _).le) (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _)) hb
    have hexp2 : Real.exp (-(2 * Real.pi * (E : ℝ) * τ.im)) * Real.exp (2 * Real.pi * (E : ℝ) * t)
        ≤ Real.exp (4 * Real.pi) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have ht : t - τ.im ≤ 1 := by linarith
      have h1 : (E : ℝ) ≤ 2 := by exact_mod_cast hE2
      have hE0 : (0 : ℝ) ≤ (E : ℝ) := by positivity
      have hkey : (E : ℝ) * (t - τ.im) ≤ 2 := by nlinarith
      have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
      have := mul_le_mul_of_nonneg_left hkey hpi
      linarith
    have hN : (Work.Kernels.scale τ) ^ NK
        ≤ (Work.Kernels.scale τ) ^ (max (Nα + Mα) NK) :=
      Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ) (le_max_right _ _)
    have hN0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ (max (Nα + Mα) NK) :=
      Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _
    have hNs : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ NK :=
      Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _
    calc ‖Work.Kernels.Khat ℓ d τ ζ‖
        ≤ CΔup * Cj * CK * Real.exp (-(2 * Real.pi * (E : ℝ) * τ.im))
          * (Work.Kernels.scale τ) ^ NK * Kout * Real.exp (2 * Real.pi * (E : ℝ) * t) := hc
      _ = (CΔup * Cj * CK * (Real.exp (-(2 * Real.pi * (E : ℝ) * τ.im))
            * Real.exp (2 * Real.pi * (E : ℝ) * t))) * Kout
            * (Work.Kernels.scale τ) ^ NK := by ring
      _ ≤ (CΔup * Cj * CK * Real.exp (4 * Real.pi)) * Kout
            * (Work.Kernels.scale τ) ^ NK := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hKoutpos.le) hNs
          exact mul_le_mul_of_nonneg_left hexp2 (by positivity)
      _ = K2 * (Work.Kernels.scale τ) ^ NK := by rw [hK2def]; ring
      _ ≤ (K1 + K2 + 1) * (Work.Kernels.scale τ) ^ (max (Nα + Mα) NK) := by
          refine mul_le_mul ?_ hN hNs (by linarith)
          linarith

/-! ## 4. Transport to the cusp-`0` tile and the final assembly -/

/-- **The polynomial window around the pole height on the cusp-`0` tile.**

For `w ∈ E = KEpsilon` and `t` in the two-unit window around the height of the pole `ζ = S • w`
of `ζ ↦ K^{(d)}(w,ζ)`, the kernel is polynomially bounded (a `(1+t)^M` factor is not needed, so we
take `M = 0`).  The proof uses the `S`-duality `Kaxis K w t = -↑(S•w)^{d/2} Kaxis K̂ (S•w) t`,
the funnel window bound `Khat_window_funnel_aux` off the coincidence, and the diagonal bound
`Funnel_Kfun_diag_bound` at the (unique) coincidence `i t = S • w`. -/
theorem EpolyWindowE_pole (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon →
        (ModularGroup.S • w).im - 1 ≤ t → t ≤ (ModularGroup.S • w).im + 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
  have hE1 : 1 ≤ (if d = 8 then 1 else 2) := by split <;> norm_num
  have hE2 : (if d = 8 then 1 else 2) ≤ 2 := by split <;> norm_num
  obtain ⟨C₁, N₁, hC₁, hN₁, hwin⟩ :=
    Khat_window_funnel_aux ℓ d hd (if d = 8 then 1 else 2) rfl hE1 hE2
      (Khat_spike_circle_high ℓ d hd)
  obtain ⟨Cd, Nd, hCd, hNd, hdiag⟩ := Funnel_Kfun_diag_bound ℓ d hd
  set Nm : ℝ := max N₁ Nd with hNm
  have hNm0 : 0 ≤ Nm := by
    rw [hNm]; exact le_trans hN₁ (le_max_left _ _)
  refine ⟨(C₁ + Cd) * 3 ^ Nm + 1, ((d / 2 : ℕ) : ℝ) + Nm, 0,
    by positivity, by positivity, le_refl 0, ?_⟩
  intro w t hw ht1 ht2
  have hT2 : (2 : ℝ) ≤ (ModularGroup.S • w).im := hw.2
  have htpos : 0 < t := by linarith
  have hτF : Funnel (ModularGroup.S • w) := S_smul_mem_funnel hw
  have hnormτ : ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ≤ Work.Kernels.scale w :=
    coe_norm_S_smul_le_scale w
  have hscaleτ : Work.Kernels.scale (ModularGroup.S • w) ≤ 3 * Work.Kernels.scale w :=
    scale_S_smul_le_of_mem_KEpsilon w hw
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have h3 : (1 : ℝ) ≤ 3 := by norm_num
  rw [HalfFunnel.kaxis_dual ℓ d hd w htpos, norm_mul, norm_neg]
  have hnormpow : ‖(((ModularGroup.S • w : ℍ)) : ℂ) ^ (d / 2)‖
      = ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ (d / 2) := norm_pow _ _
  rw [hnormpow]
  -- the two cases
  have hmain : ‖Work.Kernels.Kaxis (Work.Kernels.Khat ℓ d) (ModularGroup.S • w) t‖
      ≤ (C₁ + Cd) * (3 ^ Nm) * (Work.Kernels.scale w) ^ Nm := by
    rcases eq_or_ne (Work.Kernels.jInvariantFun w)
      (Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t htpos)) with hcoinc | hne
    · -- the coincidence: `i t = S • w`
      have hz : Work.Kernels.imagAxis t htpos = ModularGroup.S • w := by
        rcases eq_or_eq_S_of_re_eq_zero (τ := w) (z := Work.Kernels.imagAxis t htpos) hw.1
          (by simp [Work.Kernels.imagAxis]) hcoinc with h | h
        · exfalso
          have him : t = w.im := by
            have := congrArg UpperHalfPlane.im h
            simpa [Work.Kernels.imagAxis] using this
          have := E_im_le_half hw
          linarith
        · exact h
      have hKhat : Work.Kernels.Khat ℓ d (ModularGroup.S • w) (ModularGroup.S • w)
          = Work.Kernels.Kfun ℓ d (ModularGroup.S • w) (ModularGroup.S • w) := by
        have hz0 : Work.Kernels.KMinus ℓ d (ModularGroup.S • w) (ModularGroup.S • w) = 0 :=
          MiddleRange.KMinus_eq_zero_of_coincidence ℓ hd rfl
        rw [Work.Kernels.Khat, Work.Kernels.Kfun, hz0]
        ring
      have hτre : (ModularGroup.S • w).re = 0 := by
        rw [← hz]; simp [Work.Kernels.imagAxis]
      have hdiag' := hdiag (ModularGroup.S • w) hτre hT2
      have hval : Work.Kernels.Kaxis (Work.Kernels.Khat ℓ d) (ModularGroup.S • w) t
          = Work.Kernels.Khat ℓ d (ModularGroup.S • w) (ModularGroup.S • w) := by
        rw [Work.Kernels.Kaxis, dif_pos htpos, hz]
      rw [hval, hKhat]
      calc ‖Work.Kernels.Kfun ℓ d (ModularGroup.S • w) (ModularGroup.S • w)‖
          ≤ Cd * (Work.Kernels.scale (ModularGroup.S • w)) ^ Nd := hdiag'
        _ ≤ (C₁ + Cd) * (Work.Kernels.scale (ModularGroup.S • w)) ^ Nm := by
            have h1 : Cd ≤ C₁ + Cd := by linarith
            have h2 : (Work.Kernels.scale (ModularGroup.S • w)) ^ Nd
                ≤ (Work.Kernels.scale (ModularGroup.S • w)) ^ Nm :=
              Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale _) (by rw [hNm]; exact le_max_right _ _)
            exact mul_le_mul h1 h2 (Real.rpow_nonneg (Work.Kernels.scale_pos _).le _) (by positivity)
        _ ≤ (C₁ + Cd) * (3 ^ Nm) * (Work.Kernels.scale w) ^ Nm := by
            have h2 : (Work.Kernels.scale (ModularGroup.S • w)) ^ Nm
                ≤ (3 * Work.Kernels.scale w) ^ Nm :=
              Real.rpow_le_rpow (Work.Kernels.scale_pos _).le hscaleτ hNm0
            have h3' : (3 * Work.Kernels.scale w) ^ Nm
                = 3 ^ Nm * (Work.Kernels.scale w) ^ Nm :=
              Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (Work.Kernels.scale_pos w).le
            calc (C₁ + Cd) * (Work.Kernels.scale (ModularGroup.S • w)) ^ Nm
                ≤ (C₁ + Cd) * (3 * Work.Kernels.scale w) ^ Nm :=
                  mul_le_mul_of_nonneg_left h2 (by linarith)
              _ = (C₁ + Cd) * (3 ^ Nm) * (Work.Kernels.scale w) ^ Nm := by rw [h3']; ring
    · -- the non-coincidence: the funnel window bound
      have hJτ : Work.Kernels.jInvariantFun (ModularGroup.S • w)
          ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t htpos) := by
        rwa [Work.Kernels.KernelFacts.jInvariantFun_S_smul]
      have hb := hwin (ModularGroup.S • w) (Work.Kernels.imagAxis t htpos) t hτF rfl ht1 ht2 hJτ
      have hval : Work.Kernels.Kaxis (Work.Kernels.Khat ℓ d) (ModularGroup.S • w) t
          = Work.Kernels.Khat ℓ d (ModularGroup.S • w) (Work.Kernels.imagAxis t htpos) := by
        rw [Work.Kernels.Kaxis, dif_pos htpos]
      rw [hval]
      calc ‖Work.Kernels.Khat ℓ d (ModularGroup.S • w) (Work.Kernels.imagAxis t htpos)‖
          ≤ C₁ * (Work.Kernels.scale (ModularGroup.S • w)) ^ N₁ := hb
        _ ≤ (C₁ + Cd) * (Work.Kernels.scale (ModularGroup.S • w)) ^ Nm := by
            have h1 : C₁ ≤ C₁ + Cd := by linarith
            have h2 : (Work.Kernels.scale (ModularGroup.S • w)) ^ N₁
                ≤ (Work.Kernels.scale (ModularGroup.S • w)) ^ Nm :=
              Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale _) (by rw [hNm]; exact le_max_left _ _)
            exact mul_le_mul h1 h2 (Real.rpow_nonneg (Work.Kernels.scale_pos _).le _) (by positivity)
        _ ≤ (C₁ + Cd) * (3 ^ Nm) * (Work.Kernels.scale w) ^ Nm := by
            have h2 : (Work.Kernels.scale (ModularGroup.S • w)) ^ Nm
                ≤ (3 * Work.Kernels.scale w) ^ Nm :=
              Real.rpow_le_rpow (Work.Kernels.scale_pos _).le hscaleτ hNm0
            have h3' : (3 * Work.Kernels.scale w) ^ Nm
                = 3 ^ Nm * (Work.Kernels.scale w) ^ Nm :=
              Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (Work.Kernels.scale_pos w).le
            calc (C₁ + Cd) * (Work.Kernels.scale (ModularGroup.S • w)) ^ Nm
                ≤ (C₁ + Cd) * (3 * Work.Kernels.scale w) ^ Nm :=
                  mul_le_mul_of_nonneg_left h2 (by linarith)
              _ = (C₁ + Cd) * (3 ^ Nm) * (Work.Kernels.scale w) ^ Nm := by rw [h3']; ring
  -- final assembly
  have hτpow : ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ (d / 2)
      ≤ (Work.Kernels.scale w) ^ ((d / 2 : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ Work.Kernels.scale w := hs1
    calc ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ (d / 2)
        ≤ (Work.Kernels.scale w) ^ (d / 2) := pow_le_pow_left₀ (norm_nonneg _) hnormτ (d / 2)
      _ = (Work.Kernels.scale w) ^ ((d / 2 : ℕ) : ℝ) := by rw [Real.rpow_natCast]
  have hkey : ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ (d / 2)
        * ((C₁ + Cd) * (3 ^ Nm) * (Work.Kernels.scale w) ^ Nm)
      ≤ ((C₁ + Cd) * (3 ^ Nm) + 1) * (Work.Kernels.scale w) ^ (((d / 2 : ℕ) : ℝ) + Nm) := by
    have h1 : (Work.Kernels.scale w) ^ ((d / 2 : ℕ) : ℝ)
        * (Work.Kernels.scale w) ^ Nm
        = (Work.Kernels.scale w) ^ (((d / 2 : ℕ) : ℝ) + Nm) :=
      (Real.rpow_add (Work.Kernels.scale_pos w) _ _).symm
    have hSc : (0 : ℝ) ≤ (C₁ + Cd) * 3 ^ Nm := by positivity
    have hSn : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ Nm :=
      Real.rpow_nonneg (Work.Kernels.scale_pos w).le _
    calc ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ (d / 2)
          * ((C₁ + Cd) * (3 ^ Nm) * (Work.Kernels.scale w) ^ Nm)
        = ((C₁ + Cd) * (3 ^ Nm) * ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ (d / 2))
            * (Work.Kernels.scale w) ^ Nm := by ring
      _ ≤ ((C₁ + Cd) * 3 ^ Nm * (Work.Kernels.scale w) ^ ((d / 2 : ℕ) : ℝ))
            * (Work.Kernels.scale w) ^ Nm :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτpow hSc) hSn
      _ = (C₁ + Cd) * 3 ^ Nm * (Work.Kernels.scale w) ^ (((d / 2 : ℕ) : ℝ) + Nm) := by
          rw [← h1]; ring
      _ ≤ ((C₁ + Cd) * 3 ^ Nm + 1) * (Work.Kernels.scale w) ^ (((d / 2 : ℕ) : ℝ) + Nm) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
          linarith
  calc ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ (d / 2)
        * ‖Work.Kernels.Kaxis (Work.Kernels.Khat ℓ d) (ModularGroup.S • w) t‖
      ≤ ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ (d / 2)
          * ((C₁ + Cd) * (3 ^ Nm) * (Work.Kernels.scale w) ^ Nm) :=
        mul_le_mul_of_nonneg_left hmain (pow_nonneg (norm_nonneg _) _)
    _ ≤ ((C₁ + Cd) * (3 ^ Nm) + 1) * (Work.Kernels.scale w) ^ (((d / 2 : ℕ) : ℝ) + Nm) := hkey
    _ = ((C₁ + Cd) * 3 ^ Nm + 1) * (Work.Kernels.scale w) ^ (((d / 2 : ℕ) : ℝ) + Nm)
          * (1 + t) ^ (0 : ℝ) := by
        rw [Real.rpow_zero, mul_one]

end
end Work.Asymptotics
