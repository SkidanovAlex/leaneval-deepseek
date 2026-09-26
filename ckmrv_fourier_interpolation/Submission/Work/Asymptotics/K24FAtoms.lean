/-
# The `τ`- and `z`-atom bounds for the `K₊^{(24)}` funnel expansion, with one constant `D`
-/
import Mathlib
import Submission.Work.Asymptotics.K24FBase
import Submission.Work.Asymptotics.K24FZ
import Submission.Work.Asymptotics.Compact.zsmall

set_option maxHeartbeats 1000000

namespace Work.Asymptotics

open UpperHalfPlane
open Work.Kernels

noncomputable section

namespace K24F

/-- The `τ`-atom bounds with a single constant `D ≥ 24`. -/
theorem sm_atoms_tau : ∃ D : ℝ, 24 ≤ D ∧ ∀ τ : ℍ, Funnel τ →
    ‖r0 τ‖ ≤ D * scale τ ∧
    ‖r2 τ‖ ≤ D * scale τ ∧
    ‖R0 τ‖ ≤ D * scale τ ∧
    ‖r1 τ‖ ≤ D * scale τ ∧
    ‖jInvariantFun τ‖ ≤ D * Real.exp (2 * Real.pi * τ.im) ∧
    ‖DeltaFun τ‖ ≤ D ∧
    ‖(DeltaFun τ)⁻¹‖ ≤ D * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨D0, hD024, htb⟩ := tau_atom_bounds_D
  exact ⟨D0, hD024, htb⟩

/-- The `z`-atom conversions at the threshold `Im z ≥ 3`, with a single constant `D ≥ 24`. -/
theorem sm_atoms_z : ∃ D : ℝ, 24 ≤ D ∧ ∀ (z : ℍ) (t : ℝ), 3 ≤ t →
    (z : ℂ) = (t : ℂ) * Complex.I →
      ‖S0 z‖ ≤ 3 ∧
      E4Fun z ≠ 0 ∧
      ‖(E4Fun z)⁻¹‖ ≤ 2 ∧
      ‖E4Fun z ^ 3‖ ≤ 2 * D ∧
      ‖E4Fun z - 1‖ ≤ D * ‖qParamFun z‖ ∧
      ‖E4Fun z ^ 3 - 1‖ ≤ D * ‖qParamFun z‖ ∧
      ‖E2S z ^ 2 - S0 z ^ 2‖ ≤ D * ‖qParamFun z‖ ∧
      ‖E6Fun z * E2S z / E4Fun z - S0 z‖ ≤ D * ‖qParamFun z‖ ∧
      ‖DeltaFun z‖ ≤ D * ‖qParamFun z‖ ∧
      ‖(DeltaFun z)⁻¹‖ ≤ D * ‖qParamFun z‖⁻¹ ∧
      ‖(DeltaFun z)⁻¹ - (qParamFun z)⁻¹ - 24‖ ≤ D * ‖qParamFun z‖ ∧
      ‖1 - DeltaFun z / qParamFun z‖ ≤ D * ‖qParamFun z‖ ∧
      ‖E4Fun z - 1 - 240 * qParamFun z‖ ≤ D * ‖qParamFun z‖ ^ 2 ∧
      ‖E2S z - S0 z + 24 * qParamFun z‖ ≤ D * ‖qParamFun z‖ ^ 2 ∧
      ‖E6Fun z * E2S z / E4Fun z - S0 z + 24 * qParamFun z
          + 744 * qParamFun z * S0 z‖ ≤ D * ‖qParamFun z‖ ^ 2 := by
  obtain ⟨a4, ha4p, ha4⟩ := Small.E4_sub_one
  obtain ⟨a4c, ha4cp, ha4c⟩ := Small.E4_cube_sub_one
  obtain ⟨aSq, haSqp, haSq⟩ := Small.E2S_sq_sub_S0c_sq
  obtain ⟨aF, haFp, haF⟩ := E6_E2S_div_E4_sub_S0c_three
  obtain ⟨aG2, haG2p, haG2⟩ := E6_E2S_div_E4_second_three
  obtain ⟨aD, haDp, haD⟩ := Small.delta_bound
  obtain ⟨aInv, haInvp, haInv⟩ := Small.delta_inv_bound
  obtain ⟨a1c, ha1p, ha1⟩ := Small.delta_inv_small
  obtain ⟨aq, haqp, haq⟩ := Small.one_sub_delta_div_q
  obtain ⟨r4, hr4p, hr4⟩ := Small.E4_sub_one_second
  obtain ⟨r2c, hr2cp, hr2c⟩ := Small.E2_sub_one_second
  set D : ℝ := a4 + a4c + aSq + aF + aG2 + aD + aInv + a1c + aq + r4 + r2c + 24 + 1
    with hDdef
  have hD24 : 24 ≤ D := by rw [hDdef]; linarith
  have hD1 : (1 : ℝ) ≤ D := by linarith
  have ha4D : a4 ≤ D := by rw [hDdef]; linarith
  have ha4cD : a4c ≤ D := by rw [hDdef]; linarith
  have haSqD : aSq ≤ D := by rw [hDdef]; linarith
  have haFD : aF ≤ D := by rw [hDdef]; linarith
  have haG2D : aG2 ≤ D := by rw [hDdef]; linarith
  have haDD : aD ≤ D := by rw [hDdef]; linarith
  have haInvD : aInv ≤ D := by rw [hDdef]; linarith
  have ha1D : a1c ≤ D := by rw [hDdef]; linarith
  have haqD : aq ≤ D := by rw [hDdef]; linarith
  have hr4D : r4 ≤ D := by rw [hDdef]; linarith
  have hr2cD : r2c ≤ D := by rw [hDdef]; linarith
  refine ⟨D, hD24, fun z t ht hz => ?_⟩
  have hzim : z.im = t := im_of_coe_eq_axis hz
  have hz1 : (1 : ℝ) ≤ z.im := by rw [hzim]; linarith
  have hz3 : (3 : ℝ) ≤ z.im := by rw [hzim]; exact ht
  have hqnn : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq1 : ‖qParamFun z‖ ≤ 1 := norm_qParamFun_le_one z hz1
  have hS0 : ‖S0 z‖ ≤ 3 := zS0_norm z hz1
  have hE4ne : E4Fun z ≠ 0 := E4_ne_zero_three z hz3
  have hE4inv : ‖(E4Fun z)⁻¹‖ ≤ 2 := E4_inv_le_two_three z hz3
  have hE4d : ‖E4Fun z - 1‖ ≤ D * ‖qParamFun z‖ := by
    have h3 : ‖E4Fun z - 1‖ ≤ a4 * ‖qParamFun z‖ := by
      simpa only [pow_one] using ha4 z hz1
    exact le_trans h3 (mul_le_mul_of_nonneg_right ha4D hqnn)
  have hE4cd : ‖E4Fun z ^ 3 - 1‖ ≤ D * ‖qParamFun z‖ := by
    have h3 : ‖E4Fun z ^ 3 - 1‖ ≤ a4c * ‖qParamFun z‖ := by
      simpa only [pow_one] using ha4c z hz1
    exact le_trans h3 (mul_le_mul_of_nonneg_right ha4cD hqnn)
  have hSqd : ‖E2S z ^ 2 - S0 z ^ 2‖ ≤ D * ‖qParamFun z‖ := by
    have h3 : ‖E2S z ^ 2 - S0 z ^ 2‖ ≤ aSq * ‖qParamFun z‖ := by
      simpa only [Small.S0c, S0, pow_one] using haSq z hz1
    exact le_trans h3 (mul_le_mul_of_nonneg_right haSqD hqnn)
  have hFd : ‖E6Fun z * E2S z / E4Fun z - S0 z‖ ≤ D * ‖qParamFun z‖ := by
    have h3 : ‖E6Fun z * E2S z / E4Fun z - S0 z‖ ≤ aF * ‖qParamFun z‖ := by
      simpa only [Small.S0c, S0, pow_one] using haF z hz3
    exact le_trans h3 (mul_le_mul_of_nonneg_right haFD hqnn)
  have hΔzd : ‖DeltaFun z‖ ≤ D * ‖qParamFun z‖ := by
    have h3 : ‖DeltaFun z‖ ≤ aD * ‖qParamFun z‖ := by
      simpa only [pow_one] using haD z hz1
    exact le_trans h3 (mul_le_mul_of_nonneg_right haDD hqnn)
  have hΔinvd : ‖(DeltaFun z)⁻¹‖ ≤ D * ‖qParamFun z‖⁻¹ :=
    le_trans (haInv z hz1) (mul_le_mul_of_nonneg_right haInvD (inv_nonneg.mpr hqnn))
  have hd1d : ‖(DeltaFun z)⁻¹ - (qParamFun z)⁻¹ - 24‖ ≤ D * ‖qParamFun z‖ := by
    have h3 : ‖(DeltaFun z)⁻¹ - (qParamFun z)⁻¹ - 24‖ ≤ a1c * ‖qParamFun z‖ := by
      simpa only [pow_one] using ha1 z hz1
    exact le_trans h3 (mul_le_mul_of_nonneg_right ha1D hqnn)
  have hqΔd : ‖1 - DeltaFun z / qParamFun z‖ ≤ D * ‖qParamFun z‖ := by
    have h3 : ‖1 - DeltaFun z / qParamFun z‖ ≤ aq * ‖qParamFun z‖ := by
      simpa only [pow_one] using haq z hz1
    exact le_trans h3 (mul_le_mul_of_nonneg_right haqD hqnn)
  have hr4d : ‖E4Fun z - 1 - 240 * qParamFun z‖ ≤ D * ‖qParamFun z‖ ^ 2 :=
    le_trans (hr4 z hz1) (mul_le_mul_of_nonneg_right hr4D (by positivity))
  have hr2c2 : ‖E2S z - S0 z + 24 * qParamFun z‖ ≤ r2c * ‖qParamFun z‖ ^ 2 := by
    have h := hr2c z hz1
    have heq : E2S z - S0 z + 24 * qParamFun z = E2Fun z - 1 + 24 * qParamFun z := by
      rw [TildeFacts.E2S_eq, S0]; ring
    rw [heq]; exact h
  have hr2cd : ‖E2S z - S0 z + 24 * qParamFun z‖ ≤ D * ‖qParamFun z‖ ^ 2 :=
    le_trans hr2c2 (mul_le_mul_of_nonneg_right hr2cD (by positivity))
  have hG2d : ‖E6Fun z * E2S z / E4Fun z - S0 z + 24 * qParamFun z
        + 744 * qParamFun z * S0 z‖ ≤ D * ‖qParamFun z‖ ^ 2 := by
    have h3 : ‖E6Fun z * E2S z / E4Fun z - S0 z + 24 * qParamFun z
        + 744 * qParamFun z * S0 z‖ ≤ aG2 * ‖qParamFun z‖ ^ 2 := by
      have h := haG2 z hz3
      have heq : E6Fun z * E2S z / E4Fun z - S0 z + 24 * qParamFun z
            + 744 * qParamFun z * S0 z
          = E6Fun z * E2S z / E4Fun z - Small.S0c z + 24 * qParamFun z
            + 744 * qParamFun z * Small.S0c z := by
        simp only [S0, Small.S0c]
      rw [heq]; exact h
    exact le_trans h3 (mul_le_mul_of_nonneg_right haG2D (by positivity))
  have hE4cube : ‖E4Fun z ^ 3‖ ≤ 2 * D := by
    have hsplit : E4Fun z ^ 3 = (E4Fun z ^ 3 - 1) + 1 := by ring
    rw [hsplit]
    calc ‖(E4Fun z ^ 3 - 1) + 1‖ ≤ ‖E4Fun z ^ 3 - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖E4Fun z ^ 3 - 1‖ + 1 := by rw [norm_one]
      _ ≤ D * ‖qParamFun z‖ + 1 := by linarith
      _ ≤ 2 * D := by nlinarith [hD1, hq1]
  exact ⟨hS0, hE4ne, hE4inv, hE4cube, hE4d, hE4cd, hSqd, hFd, hΔzd, hΔinvd, hd1d, hqΔd,
    hr4d, hr2cd, hG2d⟩

end K24F

end

end Work.Asymptotics
