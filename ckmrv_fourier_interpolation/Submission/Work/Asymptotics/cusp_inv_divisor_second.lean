import Mathlib
import Submission.Work.Residues.ThetaExpansion
import Submission.Work.Kernels.Kernels
import Submission.Work.Residues.DeltaExpansion
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic

namespace Work.Asymptotics

open UpperHalfPlane ModularForm
open scoped MatrixGroups Manifold Modular ModularForm

noncomputable section

private lemma qParamFun_eq_Ept_sq (z : UpperHalfPlane) :
    Work.Kernels.qParamFun z = Work.Residues.Ept z ^ 2 := by
  rw [Work.Residues.Ept, Work.Kernels.qParamFun, sq, ← Complex.exp_add]
  congr 1; ring

private lemma norm_qParamFun_eq (z : UpperHalfPlane) :
    ‖Work.Kernels.qParamFun z‖ = ‖Work.Residues.Ept z‖ ^ 2 := by
  rw [qParamFun_eq_Ept_sq, norm_pow]

private lemma norm_qParamFun_exp (z : UpperHalfPlane) :
    ‖Work.Kernels.qParamFun z‖ = Real.exp (-(2 * Real.pi * z.im)) := by
  rw [norm_qParamFun_eq, Work.Residues.norm_Ept, sq, ← Real.exp_add]
  congr 1; ring

private lemma qParamFun_lt_one (z : UpperHalfPlane) : ‖Work.Kernels.qParamFun z‖ < 1 := by
  rw [norm_qParamFun_eq]
  have h := Work.Residues.norm_Ept_lt_one z
  nlinarith [norm_nonneg (Work.Residues.Ept z)]

private theorem E4Fun_cube_second :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖Work.Kernels.E4Fun z ^ 3 - 1 - 720 * Work.Kernels.qParamFun z‖ ≤
        C * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
  obtain ⟨C0, hC0, hE4⟩ := Work.Residues.E4FunSecondOrder
  refine ⟨3 * C0 + 3 * (240 + C0) ^ 2 + (240 + C0) ^ 3, by positivity, ?_⟩
  intro z hz
  set q : ℂ := Work.Kernels.qParamFun z with hq
  set s : ℂ := Work.Kernels.E4Fun z - 1 with hs
  have hq1 : ‖q‖ ≤ 1 := le_of_lt (by rw [hq]; exact qParamFun_lt_one z)
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
  have hsbound : ‖s - 240 * q‖ ≤ C0 * ‖q‖ ^ 2 := by
    rw [hs, hq]
    exact hE4 z hz
  have hs_le : ‖s‖ ≤ (240 + C0) * ‖q‖ := by
    have h1 : ‖s‖ ≤ ‖s - 240 * q‖ + ‖(240 : ℂ) * q‖ := by
      have h := norm_add_le (s - 240 * q) ((240 : ℂ) * q)
      rwa [sub_add_cancel] at h
    have h2 : ‖(240 : ℂ) * q‖ = 240 * ‖q‖ := by rw [norm_mul]; norm_num
    have h3 : C0 * ‖q‖ ^ 2 ≤ C0 * ‖q‖ :=
      mul_le_mul_of_nonneg_left (by nlinarith [hq0, hq1]) hC0.le
    nlinarith [h1, h2, hsbound, h3]
  have hkey : Work.Kernels.E4Fun z ^ 3 - 1 - 720 * q
      = 3 * (s - 240 * q) + 3 * s ^ 2 + s ^ 3 := by
    rw [hs]; ring
  rw [hkey]
  have htri : ‖(3 : ℂ) * (s - 240 * q) + (3 : ℂ) * s ^ 2 + s ^ 3‖
      ≤ 3 * ‖s - 240 * q‖ + 3 * ‖s‖ ^ 2 + ‖s‖ ^ 3 := by
    have a := norm_add_le ((3 : ℂ) * (s - 240 * q) + (3 : ℂ) * s ^ 2) (s ^ 3)
    have b := norm_add_le ((3 : ℂ) * (s - 240 * q)) ((3 : ℂ) * s ^ 2)
    have c1 : ‖(3 : ℂ)‖ = 3 := by norm_num
    have c2 : ‖(3 : ℂ) * (s - 240 * q)‖ = 3 * ‖s - 240 * q‖ := by
      rw [norm_mul, c1]
    have c3 : ‖(3 : ℂ) * s ^ 2‖ = 3 * ‖s‖ ^ 2 := by
      rw [norm_mul, c1, norm_pow]
    have c4 : ‖s ^ 3‖ = ‖s‖ ^ 3 := norm_pow s 3
    linarith [a, b, c2, c3, c4]
  calc ‖(3 : ℂ) * (s - 240 * q) + (3 : ℂ) * s ^ 2 + s ^ 3‖
      ≤ 3 * ‖s - 240 * q‖ + 3 * ‖s‖ ^ 2 + ‖s‖ ^ 3 := htri
    _ ≤ 3 * (C0 * ‖q‖ ^ 2) + 3 * ((240 + C0) * ‖q‖) ^ 2 + ((240 + C0) * ‖q‖) ^ 3 := by
        have ha : 3 * ‖s - 240 * q‖ ≤ 3 * (C0 * ‖q‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsbound (by norm_num)
        have hb : 3 * ‖s‖ ^ 2 ≤ 3 * ((240 + C0) * ‖q‖) ^ 2 := by
          have h : ‖s‖ ^ 2 ≤ ((240 + C0) * ‖q‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hs_le 2
          linarith
        have hc : ‖s‖ ^ 3 ≤ ((240 + C0) * ‖q‖) ^ 3 :=
          pow_le_pow_left₀ (norm_nonneg _) hs_le 3
        linarith
    _ ≤ (3 * C0 + 3 * (240 + C0) ^ 2 + (240 + C0) ^ 3) * ‖q‖ ^ 2 := by
        have hq3 : ‖q‖ ^ 3 ≤ ‖q‖ ^ 2 := by nlinarith [hq0, hq1]
        have hA0 : (0 : ℝ) ≤ 240 + C0 := by linarith
        have h2 : ((240 + C0) * ‖q‖) ^ 2 = (240 + C0) ^ 2 * ‖q‖ ^ 2 := by ring
        have h3 : ((240 + C0) * ‖q‖) ^ 3 = (240 + C0) ^ 3 * ‖q‖ ^ 3 := by ring
        have h4 : (240 + C0) ^ 3 * ‖q‖ ^ 3 ≤ (240 + C0) ^ 3 * ‖q‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hq3 (pow_nonneg hA0 3)
        nlinarith [h2, h3, h4, hq0, hC0]

private lemma jInvariantFun_bound_compact {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ K, ‖Work.Kernels.jInvariantFun τ‖ ≤ M := by
  have hDcont : Continuous (fun τ : UpperHalfPlane => Work.Kernels.DeltaFun τ) :=
    (CuspForm.holo' CuspForm.discriminant).continuous
  have hE4cont : Continuous (fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ) :=
    (ModularForm.holo' ModularForm.E₄).continuous
  have hjcont : Continuous (fun τ : UpperHalfPlane => Work.Kernels.jInvariantFun τ) := by
    simp only [Work.Kernels.jInvariantFun, Work.Kernels.E4Fun]
    exact (hE4cont.pow 3).div hDcont
      (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hjcont.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun τ hτ => le_trans (hM τ hτ) (le_max_left _ _)⟩

theorem cusp_inv_divisor_second {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ T : ℝ, 0 < T ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (τ : UpperHalfPlane), τ ∈ K → ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖(Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))⁻¹
            + 1 - (720 - Work.Kernels.jInvariantFun τ) * (Work.Residues.Ept z) ^ 2‖
          ≤ C * ‖Work.Residues.Ept z‖ ^ 4 := by
  obtain ⟨M, hM0, hMb⟩ := jInvariantFun_bound_compact hK
  obtain ⟨cΔ, hcΔ0, hcΔ⟩ := Work.Residues.DeltaExpansion
  obtain ⟨cA, hcA0, hcA⟩ := E4Fun_cube_second
  set Cw : ℝ := M * cΔ + cA with hCw
  have hCw0 : 0 < Cw := by
    rw [hCw]
    have : 0 ≤ M * cΔ := mul_nonneg hM0 hcΔ0.le
    linarith
  set Cu : ℝ := 720 + M + Cw with hCu
  set δ : ℝ := 1 / (4 * (720 + M + Cw + 1)) with hδ
  have hRpos : 0 < 4 * (720 + M + Cw + 1) := by linarith
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_iff₀ hRpos]
    linarith
  have hq_delta : ∀ z : UpperHalfPlane, max 1 (Real.log (1 / δ) / (2 * Real.pi)) ≤ z.im →
      ‖Work.Kernels.qParamFun z‖ ≤ δ := by
    intro z hz
    rw [norm_qParamFun_exp]
    have hzT : Real.log (1 / δ) / (2 * Real.pi) ≤ z.im := le_trans (le_max_right _ _) hz
    have h2pi : 0 < 2 * Real.pi := by positivity
    have hlog : Real.log (1 / δ) ≤ 2 * Real.pi * z.im := by
      rw [div_le_iff₀ h2pi] at hzT
      linarith
    have hlog' : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
    have hmain : -(2 * Real.pi * z.im) ≤ Real.log δ := by
      rw [hlog'] at hlog
      linarith
    calc Real.exp (-(2 * Real.pi * z.im)) ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hmain
      _ = δ := Real.exp_log hδ0
  refine ⟨max 1 (Real.log (1 / δ) / (2 * Real.pi)),
    lt_of_lt_of_le one_pos (le_max_left _ _), Cw + 2 * Cu ^ 2, ?_, ?_⟩
  · linarith [hCw0, sq_nonneg Cu]
  · intro τ hτ z hz
    have hz1 : (1 : ℝ) ≤ z.im := le_trans (le_max_left _ _) hz
    set D : ℂ := Work.Kernels.DeltaFun z with hD
    set q : ℂ := Work.Kernels.qParamFun z with hq
    set jτ : ℂ := Work.Kernels.jInvariantFun τ with hjτ
    set jz : ℂ := Work.Kernels.jInvariantFun z with hjz
    have hqE : Work.Kernels.qParamFun z = Work.Residues.Ept z ^ 2 := qParamFun_eq_Ept_sq z
    have hqE4 : ‖Work.Residues.Ept z‖ ^ 4 = ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      rw [norm_qParamFun_eq]; ring
    have hMτ : ‖jτ‖ ≤ M := by
      have h := hMb τ hτ
      rwa [← hjτ] at h
    have hq_le : ‖q‖ ≤ δ := by
      have h := hq_delta z hz
      rwa [← hq] at h
    have hq1 : ‖q‖ ≤ 1 := le_trans hq_le hδ1
    have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
    have hΔz : ‖D - q‖ ≤ cΔ * ‖q‖ ^ 2 := by
      have h := hcΔ z hz1
      rw [← hqE, ← hq, hqE4, ← hq, ← hD] at h
      exact h
    have hAz : ‖Work.Kernels.E4Fun z ^ 3 - 1 - 720 * q‖ ≤ cA * ‖q‖ ^ 2 := by
      have h := hcA z hz1
      rw [← hq] at h
      exact h
    have hDjz : D * jz = Work.Kernels.E4Fun z ^ 3 := by
      rw [hD, hjz]
      exact Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun z
    rw [← hqE, ← hq, hqE4, ← hq]
    set w : ℂ := D * (jτ - jz) + 1 + (720 - jτ) * q with hw
    set u : ℂ := (720 - jτ) * q - w with hu
    have hw_bound : ‖w‖ ≤ Cw * ‖q‖ ^ 2 := by
      have hkey : w = jτ * (D - q) - (Work.Kernels.E4Fun z ^ 3 - 1 - 720 * q) := by
        rw [hw, mul_sub, hDjz]; ring
      rw [hkey]
      calc ‖jτ * (D - q) - (Work.Kernels.E4Fun z ^ 3 - 1 - 720 * q)‖
          ≤ ‖jτ * (D - q)‖ + ‖Work.Kernels.E4Fun z ^ 3 - 1 - 720 * q‖ := norm_sub_le _ _
        _ = ‖jτ‖ * ‖D - q‖ + ‖Work.Kernels.E4Fun z ^ 3 - 1 - 720 * q‖ := by rw [norm_mul]
        _ ≤ M * (cΔ * ‖q‖ ^ 2) + cA * ‖q‖ ^ 2 := by
            apply add_le_add
            · exact mul_le_mul hMτ hΔz (norm_nonneg _) hM0
            · exact hAz
        _ = Cw * ‖q‖ ^ 2 := by rw [hCw]; ring
    have hw_quarter : ‖w‖ ≤ 1 / 4 := by
      have h1 : Cw * ‖q‖ ^ 2 ≤ Cw * δ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq_le 2) hCw0.le
      have h2 : Cw * δ ^ 2 ≤ 1 / 4 := by
        have h3 : Cw * δ ≤ 1 / 4 := by
          rw [hδ, mul_one_div, div_le_iff₀ hRpos]
          linarith
        have h4 : δ ^ 2 ≤ δ := by nlinarith [hδ0, hδ1]
        nlinarith [h3, h4, hCw0.le]
      linarith [hw_bound, h1, h2]
    have hy_low : 1 - (720 + M) * ‖q‖ ≤ ‖1 + (720 - jτ) * q‖ := by
      have h1 : 1 - ‖(720 - jτ) * q‖ ≤ ‖1 + (720 - jτ) * q‖ := by
        have h2 := norm_sub_le (1 + (720 - jτ) * q) ((720 - jτ) * q)
        simp only [add_sub_cancel_right, norm_one] at h2
        linarith
      have h2 : ‖(720 - jτ) * q‖ ≤ (720 + M) * ‖q‖ := by
        rw [norm_mul]
        have h3 : ‖(720 : ℂ) - jτ‖ ≤ 720 + M := by
          have h := norm_sub_le (720 : ℂ) jτ
          rw [Complex.norm_ofNat] at h
          linarith [hMτ]
        exact mul_le_mul_of_nonneg_right h3 hq0
      linarith
    have h4 : (720 + M) * ‖q‖ ≤ 1 / 4 := by
      have h5 : (720 + M) * δ ≤ 1 / 4 := by
        rw [hδ, mul_one_div, div_le_iff₀ hRpos]
        linarith
      have h6 : (720 + M) * ‖q‖ ≤ (720 + M) * δ :=
        mul_le_mul_of_nonneg_left hq_le (by linarith)
      linarith
    have hDJ_low : (1 : ℝ) / 2 ≤ ‖D * (jτ - jz)‖ := by
      have heq : D * (jτ - jz) = w - (1 + (720 - jτ) * q) := by rw [hw]; ring
      have h := norm_add_le ((1 + (720 - jτ) * q) - w) w
      rw [sub_add_cancel] at h
      have h2 : ‖(1 + (720 - jτ) * q) - w‖ = ‖D * (jτ - jz)‖ := by
        rw [norm_sub_rev, ← heq]
      linarith [h, h2, hy_low, h4, hw_quarter]
    have h1u_ne : 1 + u ≠ 0 := by
      have heq : D * (jτ - jz) = -(1 + u) := by rw [hu, hw]; ring
      have hnorm : ‖1 + u‖ = ‖D * (jτ - jz)‖ := by simp only [heq, norm_neg]
      intro hc
      have hzero : ‖1 + u‖ = 0 := by rw [hc, norm_zero]
      rw [hnorm] at hzero
      linarith [hDJ_low]
    have hkey2 : (D * (jτ - jz))⁻¹ + 1 - (720 - jτ) * q = -(u ^ 2 / (1 + u)) - w := by
      have heq : D * (jτ - jz) = -(1 + u) := by rw [hu, hw]; ring
      have hqu : (720 - jτ) * q = u + w := by rw [hu]; ring
      rw [heq, inv_neg, hqu]
      field_simp
      ring
    rw [hkey2]
    have hden : (1 : ℝ) / 2 ≤ ‖1 + u‖ := by
      have heq : D * (jτ - jz) = -(1 + u) := by rw [hu, hw]; ring
      have hnorm : ‖1 + u‖ = ‖D * (jτ - jz)‖ := by simp only [heq, norm_neg]
      rw [hnorm]
      exact hDJ_low
    have hu_bound : ‖u‖ ≤ Cu * ‖q‖ := by
      have h1 : ‖u‖ ≤ ‖(720 - jτ) * q‖ + ‖w‖ := by
        rw [hu]; exact norm_sub_le _ _
      have h2 : ‖(720 - jτ) * q‖ ≤ (720 + M) * ‖q‖ := by
        rw [norm_mul]
        have h3 : ‖(720 : ℂ) - jτ‖ ≤ 720 + M := by
          have h := norm_sub_le (720 : ℂ) jτ
          rw [Complex.norm_ofNat] at h
          linarith [hMτ]
        exact mul_le_mul_of_nonneg_right h3 (norm_nonneg q)
      have h4w : ‖w‖ ≤ Cw * ‖q‖ := by
        have h5 : ‖q‖ ^ 2 ≤ ‖q‖ := by nlinarith [hq0, hq1]
        calc ‖w‖ ≤ Cw * ‖q‖ ^ 2 := hw_bound
          _ ≤ Cw * ‖q‖ := mul_le_mul_of_nonneg_left h5 hCw0.le
      calc ‖u‖ ≤ (720 + M) * ‖q‖ + Cw * ‖q‖ := by linarith [h1, h2, h4w]
        _ = Cu * ‖q‖ := by rw [hCu]; ring
    have hratio : ‖u‖ ^ 2 / ‖1 + u‖ ≤ 2 * ‖u‖ ^ 2 := by
      have hpos : 0 < ‖1 + u‖ := by linarith
      rw [div_le_iff₀ hpos]
      nlinarith [hden, sq_nonneg ‖u‖]
    have hfinal : ‖-(u ^ 2 / (1 + u)) - w‖ ≤ (Cw + 2 * Cu ^ 2) * ‖q‖ ^ 2 := by
      have h1 : ‖-(u ^ 2 / (1 + u)) - w‖ ≤ ‖-(u ^ 2 / (1 + u))‖ + ‖w‖ := norm_sub_le _ _
      have h2 : ‖-(u ^ 2 / (1 + u))‖ = ‖u‖ ^ 2 / ‖1 + u‖ := by
        simp only [norm_neg, norm_div, norm_pow]
      have h3 : 2 * ‖u‖ ^ 2 ≤ 2 * Cu ^ 2 * ‖q‖ ^ 2 := by
        have h : ‖u‖ ^ 2 ≤ (Cu * ‖q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu_bound 2
        nlinarith [h, sq_nonneg ‖q‖]
      calc ‖-(u ^ 2 / (1 + u)) - w‖ ≤ ‖-(u ^ 2 / (1 + u))‖ + ‖w‖ := h1
        _ = ‖u‖ ^ 2 / ‖1 + u‖ + ‖w‖ := by rw [h2]
        _ ≤ 2 * ‖u‖ ^ 2 + Cw * ‖q‖ ^ 2 := by linarith [hratio, hw_bound]
        _ ≤ 2 * Cu ^ 2 * ‖q‖ ^ 2 + Cw * ‖q‖ ^ 2 := by linarith [h3]
        _ = (Cw + 2 * Cu ^ 2) * ‖q‖ ^ 2 := by ring
    exact hfinal

end

end Work.Asymptotics
