/-
# The low-`Im` bound for the `K_+`-numerator `Xi24` (private copy of `Xi24_low_bound`)

This is a verbatim copy of `Submission/Work/Asymptotics/Xi24_low_bound.lean` with the declarations
renamed by the prefix `SKX24_` and two local elaborations fixed.  The original module is another
colleague's file and currently does not compile (two tactic errors); the mathematics is unchanged.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Xi24_bound_E
import Submission.Work.Asymptotics.Xi8_low_bound
import Submission.Work.Asymptotics.KMinusFunnelZBounds
import Submission.Work.Asymptotics.EBase
import Submission.Work.Asymptotics.DeltaFun_imagAxis_lower_sharp

namespace Work.Asymptotics

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

open Work.Kernels (DeltaFun imagAxis E4Fun E6Fun E2Fun jInvariantFun scale qParamFun)

set_option maxHeartbeats 16000000

/-- `S • (i/t) = i t`. -/
lemma SKX24_S_smul_imagAxis_inv (t : ℝ) (ht : 0 < t) :
    ModularGroup.S • imagAxis t⁻¹ (inv_pos.mpr ht) = imagAxis t ht := by
  apply UpperHalfPlane.ext
  rw [Work.Kernels.S_smul_coe]
  show (-(((imagAxis t⁻¹ (inv_pos.mpr ht) : UpperHalfPlane)) : ℂ)⁻¹)
      = ((imagAxis t ht : UpperHalfPlane) : ℂ)
  simp only [imagAxis]
  rw [mul_inv, Complex.inv_I, ← Complex.ofReal_inv, inv_inv]
  push_cast
  ring

/-- Norm of a product from bounds on the factors. -/
lemma SKX24_norm_mul_le {a b : ℂ} {A B : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) :
    ‖a * b‖ ≤ A * B := by
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg _) (le_trans (norm_nonneg _) ha)

/-- **`1/Δ(i s)` is `O(s^{12}e^{2π/s})`.** -/
lemma SKX24_DeltaFun_imagAxis_inv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ) (hs : 0 < s), s ≤ 1 →
      ‖DeltaFun (imagAxis s hs)‖⁻¹ ≤ C * s ^ 12 * Real.exp (2 * Real.pi / s) := by
  refine ⟨2, by norm_num, fun s hs hs1 => ?_⟩
  have hS : ModularGroup.S • imagAxis s⁻¹ (inv_pos.mpr hs) = imagAxis s hs :=
    SKX24_S_smul_imagAxis_inv s hs
  have h := DeltaFun_S_smul' (imagAxis s⁻¹ (inv_pos.mpr hs))
  rw [hS] at h
  have hnorm : ‖DeltaFun (imagAxis s⁻¹ (inv_pos.mpr hs))‖
      = s ^ 12 * ‖DeltaFun (imagAxis s hs)‖ := by
    rw [h, norm_mul, norm_pow, norm_imagAxis_coe' s hs]
  have hlow := DeltaFun_imagAxis_lower_sharp s⁻¹ (inv_pos.mpr hs) ((one_le_inv₀ hs).mpr hs1)
  have hs12 : (0 : ℝ) < s ^ 12 := by positivity
  have hΔpos : 0 < ‖DeltaFun (imagAxis s hs)‖ :=
    norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)
  have h1 : (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * s⁻¹))
      ≤ s ^ 12 * ‖DeltaFun (imagAxis s hs)‖ := by rw [← hnorm]; exact hlow
  have h3 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hs12.le)
  have h4 : (s ^ 12)⁻¹ * (s ^ 12 * ‖DeltaFun (imagAxis s hs)‖)
      = ‖DeltaFun (imagAxis s hs)‖ := by
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hs12), one_mul]
  rw [h4] at h3
  have h5 : ‖DeltaFun (imagAxis s hs)‖⁻¹
      ≤ (((s ^ 12)⁻¹) * ((1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * s⁻¹))))⁻¹ :=
    (inv_le_inv₀ hΔpos (by positivity)).mpr h3
  calc ‖DeltaFun (imagAxis s hs)‖⁻¹
      ≤ (((s ^ 12)⁻¹) * ((1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * s⁻¹))))⁻¹ := h5
    _ = 2 * s ^ 12 * Real.exp (2 * Real.pi / s) := by
        rw [Real.exp_neg]
        have hs12ne : s ^ 12 ≠ 0 := ne_of_gt hs12
        have hene : Real.exp (-(2 * Real.pi * s⁻¹)) ≠ 0 := Real.exp_ne_zero _
        field_simp

/-- **`j(i s)` is `O(e^{2π/s})`.** -/
lemma SKX24_jInvariantFun_imagAxis_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ) (hs : 0 < s), s ≤ 1 →
      ‖jInvariantFun (imagAxis s hs)‖ ≤ C * Real.exp (2 * Real.pi / s) := by
  obtain ⟨C, hC, hb⟩ := jInvariantFun_bound_third
  refine ⟨C, hC, fun s hs hs1 => ?_⟩
  have hs' : 0 < s⁻¹ := inv_pos.mpr hs
  have hle : (1 : ℝ) ≤ s⁻¹ := (one_le_inv₀ hs).mpr hs1
  have h13 : (1 : ℝ) / 3 ≤ (imagAxis s⁻¹ hs').im := by
    rw [imagAxis_im' s⁻¹ hs']; linarith
  have h := hb (imagAxis s⁻¹ hs') h13
  have hSm : ModularGroup.S • imagAxis s⁻¹ hs' = imagAxis s hs := SKX24_S_smul_imagAxis_inv s hs
  have heq : jInvariantFun (imagAxis s⁻¹ hs') = jInvariantFun (imagAxis s hs) := by
    have h2 := (Work.Kernels.KernelFacts.jInvariantFun_S_smul (imagAxis s⁻¹ hs')).symm
    rw [hSm] at h2
    exact h2
  rw [heq, imagAxis_im' s⁻¹ hs'] at h
  refine le_trans h (mul_le_mul_of_nonneg_left ?_ hC.le)
  rw [show (2 : ℝ) * Real.pi * s⁻¹ = 2 * Real.pi / s by rw [div_eq_mul_inv]]

/-! ## The `B`-identity of `Xi24_decomp`

`Xi24_B_eq` is private in `Xi24_bound_E`; we re-derive it here. -/

/-- `6δ(z)(jτ − jz) + 1728E₄(z) = 6δ(z)j(τ) + 6E₄(z)(288Δ(z) − δ(z)E₄(z)²)/Δ(z)`. -/
lemma SKX24_B_eq (τ z : UpperHalfPlane) :
    6 * Xi24delta z * (jInvariantFun τ - jInvariantFun z) + 1728 * E4Fun z
      = 6 * Xi24delta z * jInvariantFun τ
        + 6 * E4Fun z * (288 * DeltaFun z - Xi24delta z * E4Fun z ^ 2) / DeltaFun z := by
  have hDz : DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  rw [Xi24delta, jInvariantFun]
  field_simp
  ring

/-! ## The main bound -/

/-- **The `d = 24` CKMRV numerator `Ξ₂₄` below the cusp: polynomial bound at `Im z ≤ 1`.**

For `w ∈ E = KEpsilon` and `0 < s ≤ 1` with `s⁻¹ ≤ Im (S • w) − 1`, the numerator
`Ξ₂₄(w, i·s)` — equal to `c₂₄·Δ(i s)·(j w − j (i s))·(i s)^{10}·K₊^{(24)}(w, S·(i s))` — is
bounded polynomially in `scale w` and `s⁻¹`.

`Xi24_decomp` writes `Ξ₂₄(τ,z) = A·B + 1728(7R0(τ) − r0(τ))δ(z) − 1728 r1(τ)E₄(z)²r(z)/Δ(z)`
with `A = r0 + r2 − 2R0`, and `SKX24_B_eq` splits `B = 6δ(z)j(τ) + 6E₄(z)(288Δ(z) − δ(z)E₄(z)²)/Δ(z)`.
At `z = i s` the factors are `‖δ‖ ≤ Cd T^4`, `‖E₄‖ ≤ C4 T^4`, `‖E₆‖ ≤ C6 T^6`, `‖E₂‖ ≤ C2 T^2`,
`‖Δ‖⁻¹ ≤ Cinv s^{12}e^{2π/s}` (`T = 1+s⁻¹`), while `‖j w‖ ≤ Cat e^{2πH}`, `‖A‖ ≤ CA S^13 e^{−2πH}`
and `‖r1‖ ≤ Cat S^13 e^{−2πH}` with `S = scale w`, `H = Im(S•w) ≥ s⁻¹ + 1`; the exponentials
cancel and `s^{12} ≤ 1` finishes it. -/
theorem SKX24_low_bound :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (s : ℝ) (hs : 0 < s), w ∈ KEpsilon → s ≤ 1 →
        s⁻¹ ≤ (ModularGroup.S • w).im - 1 →
        ‖Xi24 w (imagAxis s hs)‖
          ≤ C * (scale w) ^ N * (1 + s⁻¹) ^ M := by
  obtain ⟨CA, hCA, hAb⟩ := Xi24_A_bound
  obtain ⟨Cat, hCat, hat⟩ := Xi24_atoms_tau_bounds
  obtain ⟨CΔ, C4, C6, C2, Cd, Ce, hCΔ, hC4, hC6, hC2, hCd, hCe, hatoms⟩ := imagAxis_atoms_bound
  obtain ⟨Cinv, hCinv, hinvb⟩ := SKX24_DeltaFun_imagAxis_inv_bound
  set Cr : ℝ := 5 * C4 ^ 2 + 7 * C4 * C2 ^ 2 + 2 * C6 * C2 with hCr
  have hCr0 : 0 < Cr := by rw [hCr]; positivity
  set K : ℝ := CA * (6 * Cd * Cat + 6 * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2))
    + 1728 * 8 * Cat * Cd + 1728 * Cat * C4 ^ 2 * Cr * Cinv + 1 with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  refine ⟨K, 13, 32, hK0, by norm_num, by norm_num, ?_⟩
  intro w s hs hw hs1 hfar
  set T : ℝ := 1 + s⁻¹ with hT
  have hT1 : (1 : ℝ) ≤ T := by rw [hT]; linarith [inv_pos.mpr hs]
  have hT32 : (0 : ℝ) ≤ T ^ 32 := by positivity
  have hT4le : T ^ 4 ≤ T ^ 32 := pow_le_pow_right₀ hT1 (by norm_num)
  have hT16le : T ^ 16 ≤ T ^ 32 := pow_le_pow_right₀ hT1 (by norm_num)
  have hs12le : s ^ 12 ≤ 1 := pow_le_one₀ hs.le hs1
  -- atom bounds at `z = i s`
  obtain ⟨hΔz, h4z, h6z, h2z, hdz, hez⟩ := hatoms s hs hs1
  have hdz' : ‖Xi24delta (imagAxis s hs)‖ ≤ Cd * T ^ 4 := by
    simpa [hT, Xi24delta] using hdz
  have h4z' : ‖E4Fun (imagAxis s hs)‖ ≤ C4 * T ^ 4 := by simpa [hT] using h4z
  have h6z' : ‖E6Fun (imagAxis s hs)‖ ≤ C6 * T ^ 6 := by simpa [hT] using h6z
  have h2z' : ‖E2Fun (imagAxis s hs)‖ ≤ C2 * T ^ 2 := by simpa [hT] using h2z
  have hΔz' : ‖DeltaFun (imagAxis s hs)‖ ≤ CΔ * T ^ 12 := by simpa [hT] using hΔz
  have hinv' : ‖DeltaFun (imagAxis s hs)‖⁻¹ ≤ Cinv * s ^ 12 * Real.exp (2 * Real.pi / s) :=
    hinvb s hs hs1
  -- `τ`-side data
  have hS3 : (3 / 2 : ℝ) ≤ (ModularGroup.S • w).im := le_trans (by norm_num) hw.2
  obtain ⟨hr0, hr2, hR0, hr1, hjt⟩ := hat w hS3
  set S : ℝ := scale w with hS
  set H : ℝ := (ModularGroup.S • w).im with hH
  have hS1 : (1 : ℝ) ≤ S := by rw [hS]; exact Work.Kernels.one_le_scale w
  have hS13 : (0 : ℝ) ≤ S ^ 13 := by positivity
  have hq : ‖qParamFun (ModularGroup.S • w)‖ = Real.exp (-(2 * Real.pi * H)) := by
    rw [hH]; exact norm_qParamFun _
  have hqpos : (0 : ℝ) < ‖qParamFun (ModularGroup.S • w)‖ :=
    norm_pos_iff.mpr (qParamFun_ne_zero' _)
  have hq_expH : ‖qParamFun (ModularGroup.S • w)‖ * Real.exp (2 * Real.pi * H) = 1 := by
    rw [hq, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hq_exps : ‖qParamFun (ModularGroup.S • w)‖ * s ^ 12
      * Real.exp (2 * Real.pi / s) ≤ 1 := by
    have h1 : ‖qParamFun (ModularGroup.S • w)‖ * Real.exp (2 * Real.pi / s) ≤ 1 := by
      rw [hq, ← Real.exp_add]
      apply Real.exp_le_one_iff.mpr
      have h2 : s⁻¹ ≤ H := by rw [hH]; linarith [hfar]
      rw [show -(2 * Real.pi * H) + 2 * Real.pi / s = 2 * Real.pi * (s⁻¹ - H) by
        rw [div_eq_mul_inv]; ring]
      nlinarith [Real.pi_pos, h2]
    have h3 : ‖qParamFun (ModularGroup.S • w)‖ * s ^ 12 * Real.exp (2 * Real.pi / s)
        = (‖qParamFun (ModularGroup.S • w)‖ * Real.exp (2 * Real.pi / s)) * s ^ 12 := by ring
    rw [h3]
    exact le_trans (mul_le_of_le_one_left (by positivity) h1) hs12le
  have hjw : ‖jInvariantFun w‖ ≤ Cat * Real.exp (2 * Real.pi * H) := by
    have h1 : ‖jInvariantFun w‖ * ‖qParamFun (ModularGroup.S • w)‖ ≤ Cat := hjt
    rw [hq] at h1
    have h2 : ‖jInvariantFun w‖ ≤ Cat / Real.exp (-(2 * Real.pi * H)) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr h1
    rwa [div_eq_mul_inv, Real.exp_neg, inv_inv] at h2
  have hA : ‖Xi24r0 w + Xi24r2 w - 2 * Xi24R0 w‖
      ≤ CA * S ^ 13 * ‖qParamFun (ModularGroup.S • w)‖ := by
    rw [hS]; exact hAb w hS3
  have hr0' : ‖Xi24r0 w‖ ≤ Cat * S ^ 13 := by rw [hS]; exact hr0
  have hr2' : ‖Xi24r2 w‖ ≤ Cat * S ^ 13 := by rw [hS]; exact hr2
  have hR0' : ‖Xi24R0 w‖ ≤ Cat * S ^ 13 := by rw [hS]; exact hR0
  have hr1' : ‖Xi24r1 w‖ ≤ Cat * S ^ 13 * ‖qParamFun (ModularGroup.S • w)‖ := by
    rw [hS]; exact hr1
  -- the `z`-side pieces
  have hBsix : ‖(6 : ℂ) * Xi24delta (imagAxis s hs) * jInvariantFun w‖
      ≤ 6 * (Cd * T ^ 4) * (Cat * Real.exp (2 * Real.pi * H)) := by
    rw [norm_mul, norm_mul]
    simp only [Complex.norm_ofNat]
    nlinarith [hdz', hjw, norm_nonneg (Xi24delta (imagAxis s hs)),
      norm_nonneg (jInvariantFun w), hCat.le, hCd.le, hT32]
  have hBnum : ‖(288 : ℂ) * DeltaFun (imagAxis s hs)
        - Xi24delta (imagAxis s hs) * E4Fun (imagAxis s hs) ^ 2‖
      ≤ (288 * CΔ + Cd * C4 ^ 2) * T ^ 12 := by
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖(288 : ℂ) * DeltaFun (imagAxis s hs)‖ ≤ 288 * (CΔ * T ^ 12) := by
      rw [norm_mul]
      simp only [Complex.norm_ofNat]
      nlinarith [hΔz', hCΔ.le, hT32]
    have h2 : ‖Xi24delta (imagAxis s hs) * E4Fun (imagAxis s hs) ^ 2‖
        ≤ (Cd * T ^ 4) * (C4 ^ 2 * T ^ 8) := by
      refine SKX24_norm_mul_le hdz' ?_
      rw [norm_pow, show C4 ^ 2 * T ^ 8 = (C4 * T ^ 4) ^ 2 by ring]
      exact pow_le_pow_left₀ (norm_nonneg _) h4z' 2
    have h3 : (Cd * T ^ 4) * (C4 ^ 2 * T ^ 8) = Cd * C4 ^ 2 * T ^ 12 := by
      rw [show (Cd * T ^ 4) * (C4 ^ 2 * T ^ 8) = Cd * C4 ^ 2 * (T ^ 4 * T ^ 8) by ring,
        show T ^ 4 * T ^ 8 = T ^ 12 by rw [← pow_add]]
    rw [h3] at h2
    nlinarith [h1, h2, hCΔ.le, hC4.le, hCd.le, hT32]
  have hBdiv : ‖((288 : ℂ) * DeltaFun (imagAxis s hs)
        - Xi24delta (imagAxis s hs) * E4Fun (imagAxis s hs) ^ 2) / DeltaFun (imagAxis s hs)‖
      ≤ ((288 * CΔ + Cd * C4 ^ 2) * T ^ 12) * (Cinv * s ^ 12 * Real.exp (2 * Real.pi / s)) := by
    rw [norm_div, div_eq_mul_inv]
    exact mul_le_mul hBnum hinv' (by positivity) (by positivity)
  have hB : ‖6 * Xi24delta (imagAxis s hs) * jInvariantFun w
        + 6 * E4Fun (imagAxis s hs)
            * (288 * DeltaFun (imagAxis s hs)
              - Xi24delta (imagAxis s hs) * E4Fun (imagAxis s hs) ^ 2)
            / DeltaFun (imagAxis s hs)‖
      ≤ 6 * Cd * T ^ 4 * (Cat * Real.exp (2 * Real.pi * H))
        + 6 * C4 * T ^ 4 * ((288 * CΔ + Cd * C4 ^ 2) * T ^ 12)
            * (Cinv * s ^ 12 * Real.exp (2 * Real.pi / s)) := by
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · calc ‖6 * Xi24delta (imagAxis s hs) * jInvariantFun w‖
          = ‖(6 : ℂ) * Xi24delta (imagAxis s hs) * jInvariantFun w‖ := by ring_nf
        _ ≤ 6 * (Cd * T ^ 4) * (Cat * Real.exp (2 * Real.pi * H)) := hBsix
        _ = 6 * Cd * T ^ 4 * (Cat * Real.exp (2 * Real.pi * H)) := by ring
    · have hE4 : ‖E4Fun (imagAxis s hs) * (((288 : ℂ) * DeltaFun (imagAxis s hs)
            - Xi24delta (imagAxis s hs) * E4Fun (imagAxis s hs) ^ 2)
            / DeltaFun (imagAxis s hs))‖
          ≤ (C4 * T ^ 4) * (((288 * CΔ + Cd * C4 ^ 2) * T ^ 12)
              * (Cinv * s ^ 12 * Real.exp (2 * Real.pi / s))) :=
        SKX24_norm_mul_le h4z' hBdiv
      calc ‖6 * E4Fun (imagAxis s hs) * (288 * DeltaFun (imagAxis s hs)
              - Xi24delta (imagAxis s hs) * E4Fun (imagAxis s hs) ^ 2)
              / DeltaFun (imagAxis s hs)‖
          = ‖(6 : ℂ) * (E4Fun (imagAxis s hs) * (((288 : ℂ) * DeltaFun (imagAxis s hs)
              - Xi24delta (imagAxis s hs) * E4Fun (imagAxis s hs) ^ 2)
              / DeltaFun (imagAxis s hs)))‖ := by ring_nf
        _ ≤ 6 * ((C4 * T ^ 4) * (((288 * CΔ + Cd * C4 ^ 2) * T ^ 12)
              * (Cinv * s ^ 12 * Real.exp (2 * Real.pi / s)))) :=
            SKX24_norm_mul_le (by norm_num) hE4
        _ = 6 * C4 * T ^ 4 * ((288 * CΔ + Cd * C4 ^ 2) * T ^ 12)
            * (Cinv * s ^ 12 * Real.exp (2 * Real.pi / s)) := by ring
  -- the `r`-bound
  have hr : ‖5 * E4Fun (imagAxis s hs) ^ 2
        - 7 * E4Fun (imagAxis s hs) * E2Fun (imagAxis s hs) ^ 2
        + 2 * E6Fun (imagAxis s hs) * E2Fun (imagAxis s hs)‖ ≤ Cr * T ^ 8 := by
    have h1 : ‖(5 : ℂ) * E4Fun (imagAxis s hs) ^ 2‖ ≤ 5 * (C4 ^ 2 * T ^ 8) := by
      rw [norm_mul]
      simp only [Complex.norm_ofNat]
      rw [norm_pow]
      have h := pow_le_pow_left₀ (norm_nonneg _) h4z' 2
      nlinarith [h, hC4.le, hT32]
    have h2 : ‖(7 : ℂ) * E4Fun (imagAxis s hs) * E2Fun (imagAxis s hs) ^ 2‖
        ≤ 7 * ((C4 * T ^ 4) * (C2 * T ^ 2) ^ 2) := by
      rw [norm_mul, norm_mul]
      simp only [Complex.norm_ofNat]
      rw [norm_pow]
      have h := pow_le_pow_left₀ (norm_nonneg _) h2z' 2
      nlinarith [h, h4z', hC2.le, hC4.le, hT32, norm_nonneg (E2Fun (imagAxis s hs)),
        norm_nonneg (E4Fun (imagAxis s hs))]
    have h3 : ‖(2 : ℂ) * E6Fun (imagAxis s hs) * E2Fun (imagAxis s hs)‖
        ≤ 2 * ((C6 * T ^ 6) * (C2 * T ^ 2)) := by
      rw [norm_mul, norm_mul]
      simp only [Complex.norm_ofNat]
      nlinarith [h6z', h2z', hC6.le, hC2.le, hT32, norm_nonneg (E2Fun (imagAxis s hs)),
        norm_nonneg (E6Fun (imagAxis s hs))]
    have h4 := norm_sub_le ((5 : ℂ) * E4Fun (imagAxis s hs) ^ 2)
      ((7 : ℂ) * E4Fun (imagAxis s hs) * E2Fun (imagAxis s hs) ^ 2
        - (2 : ℂ) * E6Fun (imagAxis s hs) * E2Fun (imagAxis s hs))
    have h5 := norm_sub_le ((7 : ℂ) * E4Fun (imagAxis s hs) * E2Fun (imagAxis s hs) ^ 2)
      ((2 : ℂ) * E6Fun (imagAxis s hs) * E2Fun (imagAxis s hs))
    rw [show (5 : ℂ) * E4Fun (imagAxis s hs) ^ 2
          - 7 * E4Fun (imagAxis s hs) * E2Fun (imagAxis s hs) ^ 2
          + 2 * E6Fun (imagAxis s hs) * E2Fun (imagAxis s hs)
        = (5 : ℂ) * E4Fun (imagAxis s hs) ^ 2
          - ((7 : ℂ) * E4Fun (imagAxis s hs) * E2Fun (imagAxis s hs) ^ 2
            - (2 : ℂ) * E6Fun (imagAxis s hs) * E2Fun (imagAxis s hs)) from by ring]
    rw [hCr]
    nlinarith [h4, h5, h1, h2, h3, hC4.le, hC2.le, hC6.le, hT32]
  -- the three terms of the decomposition
  have hterm1 : ‖(Xi24r0 w + Xi24r2 w - 2 * Xi24R0 w)
        * (6 * Xi24delta (imagAxis s hs) * jInvariantFun w
          + 6 * E4Fun (imagAxis s hs)
            * (288 * DeltaFun (imagAxis s hs)
              - Xi24delta (imagAxis s hs) * E4Fun (imagAxis s hs) ^ 2)
            / DeltaFun (imagAxis s hs))‖
      ≤ (CA * S ^ 13 * ‖qParamFun (ModularGroup.S • w)‖)
        * (6 * Cd * T ^ 4 * (Cat * Real.exp (2 * Real.pi * H))
          + 6 * C4 * T ^ 4 * ((288 * CΔ + Cd * C4 ^ 2) * T ^ 12)
              * (Cinv * s ^ 12 * Real.exp (2 * Real.pi / s))) :=
    SKX24_norm_mul_le hA hB
  have hterm2 : ‖(1728 : ℂ) * (7 * Xi24R0 w - Xi24r0 w)
        * Xi24delta (imagAxis s hs)‖
      ≤ 1728 * (7 * (Cat * S ^ 13) + Cat * S ^ 13) * (Cd * T ^ 4) := by
    have h1 : ‖(7 : ℂ) * Xi24R0 w - Xi24r0 w‖ ≤ 7 * (Cat * S ^ 13) + Cat * S ^ 13 := by
      refine le_trans (norm_sub_le _ _) ?_
      have h2 : ‖(7 : ℂ) * Xi24R0 w‖ ≤ 7 * (Cat * S ^ 13) := by
        rw [norm_mul]
        simp only [Complex.norm_ofNat]
        nlinarith [hR0', hCat.le, hS13]
      linarith [h2, hr0']
    exact SKX24_norm_mul_le (SKX24_norm_mul_le (by norm_num) h1) hdz'
  have hterm3 : ‖(1728 : ℂ) * Xi24r1 w * E4Fun (imagAxis s hs) ^ 2
        * (5 * E4Fun (imagAxis s hs) ^ 2
          - 7 * E4Fun (imagAxis s hs) * E2Fun (imagAxis s hs) ^ 2
          + 2 * E6Fun (imagAxis s hs) * E2Fun (imagAxis s hs))
        / DeltaFun (imagAxis s hs)‖
      ≤ 1728 * (Cat * S ^ 13 * ‖qParamFun (ModularGroup.S • w)‖) * (C4 ^ 2 * T ^ 8)
          * (Cr * T ^ 8) * (Cinv * s ^ 12 * Real.exp (2 * Real.pi / s)) := by
    rw [norm_div, div_eq_mul_inv]
    refine mul_le_mul ?_ hinv' (by positivity) (by positivity)
    have h4sq : ‖E4Fun (imagAxis s hs) ^ 2‖ ≤ C4 ^ 2 * T ^ 8 := by
      rw [norm_pow, show C4 ^ 2 * T ^ 8 = (C4 * T ^ 4) ^ 2 by ring]
      exact pow_le_pow_left₀ (norm_nonneg _) h4z' 2
    have h1 := SKX24_norm_mul_le (SKX24_norm_mul_le (SKX24_norm_mul_le (by norm_num : ‖(1728 : ℂ)‖ ≤ 1728) hr1')
      h4sq) hr
    refine le_trans h1 (le_of_eq ?_)
    ring
  -- the decomposition and the triangle inequality
  have htri : ‖Xi24 w (imagAxis s hs)‖
      ≤ ‖(Xi24r0 w + Xi24r2 w - 2 * Xi24R0 w)
          * (6 * Xi24delta (imagAxis s hs) * jInvariantFun w
            + 6 * E4Fun (imagAxis s hs)
              * (288 * DeltaFun (imagAxis s hs)
                - Xi24delta (imagAxis s hs) * E4Fun (imagAxis s hs) ^ 2)
              / DeltaFun (imagAxis s hs))‖
        + ‖(1728 : ℂ) * (7 * Xi24R0 w - Xi24r0 w) * Xi24delta (imagAxis s hs)‖
        + ‖(1728 : ℂ) * Xi24r1 w * E4Fun (imagAxis s hs) ^ 2
            * (5 * E4Fun (imagAxis s hs) ^ 2
              - 7 * E4Fun (imagAxis s hs) * E2Fun (imagAxis s hs) ^ 2
              + 2 * E6Fun (imagAxis s hs) * E2Fun (imagAxis s hs))
            / DeltaFun (imagAxis s hs)‖ := by
    have h := Xi24_decomp w (imagAxis s hs)
    rw [show Xi24 w (imagAxis s hs) = (Xi24r0 w + Xi24r2 w - 2 * Xi24R0 w)
          * (6 * Xi24delta (imagAxis s hs)
              * (jInvariantFun w - jInvariantFun (imagAxis s hs)) + 1728 * E4Fun (imagAxis s hs))
        + 1728 * (7 * Xi24R0 w - Xi24r0 w) * Xi24delta (imagAxis s hs)
        - 1728 * Xi24r1 w * E4Fun (imagAxis s hs) ^ 2
          * (5 * E4Fun (imagAxis s hs) ^ 2
            - 7 * E4Fun (imagAxis s hs) * E2Fun (imagAxis s hs) ^ 2
            + 2 * E6Fun (imagAxis s hs) * E2Fun (imagAxis s hs))
          / DeltaFun (imagAxis s hs) from h]
    rw [SKX24_B_eq w (imagAxis s hs)]
    refine le_trans (norm_sub_le _ _) ?_
    exact add_le_add (norm_add_le _ _) le_rfl
  -- the arithmetic
  have hsum1 : (CA * S ^ 13 * ‖qParamFun (ModularGroup.S • w)‖)
        * (6 * Cd * T ^ 4 * (Cat * Real.exp (2 * Real.pi * H))
          + 6 * C4 * T ^ 4 * ((288 * CΔ + Cd * C4 ^ 2) * T ^ 12)
              * (Cinv * s ^ 12 * Real.exp (2 * Real.pi / s)))
      ≤ (6 * CA * Cd * Cat + 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2))
          * (S ^ 13 * T ^ 32) := by
    have hfac : (CA * S ^ 13 * ‖qParamFun (ModularGroup.S • w)‖)
          * (6 * Cd * T ^ 4 * (Cat * Real.exp (2 * Real.pi * H))
            + 6 * C4 * T ^ 4 * ((288 * CΔ + Cd * C4 ^ 2) * T ^ 12)
                * (Cinv * s ^ 12 * Real.exp (2 * Real.pi / s)))
        = 6 * CA * Cd * Cat
              * (‖qParamFun (ModularGroup.S • w)‖ * Real.exp (2 * Real.pi * H))
              * (S ^ 13 * T ^ 4)
          + 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2)
              * (‖qParamFun (ModularGroup.S • w)‖ * s ^ 12 * Real.exp (2 * Real.pi / s))
              * (S ^ 13 * T ^ 16) := by ring
    rw [hfac, hq_expH, mul_one]
    have h1 : 6 * CA * Cd * Cat * (S ^ 13 * T ^ 4)
        ≤ 6 * CA * Cd * Cat * (S ^ 13 * T ^ 32) := by
      have h2 : S ^ 13 * T ^ 4 ≤ S ^ 13 * T ^ 32 := mul_le_mul_of_nonneg_left hT4le hS13
      have h3 : (6 * CA * Cd * Cat) * (S ^ 13 * T ^ 4)
          ≤ (6 * CA * Cd * Cat) * (S ^ 13 * T ^ 32) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      calc 6 * CA * Cd * Cat * (S ^ 13 * T ^ 4)
          = (6 * CA * Cd * Cat) * (S ^ 13 * T ^ 4) := by ring
        _ ≤ (6 * CA * Cd * Cat) * (S ^ 13 * T ^ 32) := h3
        _ = 6 * CA * Cd * Cat * (S ^ 13 * T ^ 32) := by ring
    have h2 : 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2)
          * (‖qParamFun (ModularGroup.S • w)‖ * s ^ 12 * Real.exp (2 * Real.pi / s))
          * (S ^ 13 * T ^ 16)
        ≤ 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2) * (S ^ 13 * T ^ 32) := by
      have hnn : (0 : ℝ) ≤ 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2) := by positivity
      have hmid : (‖qParamFun (ModularGroup.S • w)‖ * s ^ 12 * Real.exp (2 * Real.pi / s))
          * (S ^ 13 * T ^ 16) ≤ S ^ 13 * T ^ 32 := by
        have h1 := mul_le_mul_of_nonneg_right hq_exps (by positivity : (0 : ℝ) ≤ S ^ 13 * T ^ 16)
        rw [one_mul] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left hT16le hS13)
      calc 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2)
            * (‖qParamFun (ModularGroup.S • w)‖ * s ^ 12 * Real.exp (2 * Real.pi / s))
            * (S ^ 13 * T ^ 16)
          = 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2)
              * ((‖qParamFun (ModularGroup.S • w)‖ * s ^ 12 * Real.exp (2 * Real.pi / s))
                * (S ^ 13 * T ^ 16)) := by ring
        _ ≤ 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2) * (S ^ 13 * T ^ 32) :=
            mul_le_mul_of_nonneg_left hmid hnn
    have heq : 6 * CA * Cd * Cat * (S ^ 13 * T ^ 32)
          + 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2) * (S ^ 13 * T ^ 32)
        = (6 * CA * Cd * Cat + 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2))
            * (S ^ 13 * T ^ 32) := by ring
    exact (add_le_add h1 h2).trans heq.le
  have hsum2 : 1728 * (7 * (Cat * S ^ 13) + Cat * S ^ 13) * (Cd * T ^ 4)
      ≤ (1728 * 8 * Cat * Cd) * (S ^ 13 * T ^ 32) := by
    have h1 : 1728 * (7 * (Cat * S ^ 13) + Cat * S ^ 13) * (Cd * T ^ 4)
        = 1728 * 8 * Cat * Cd * (S ^ 13 * T ^ 4) := by ring
    rw [h1]
    have h2 : (0 : ℝ) ≤ 1728 * 8 * Cat * Cd := by positivity
    refine mul_le_mul_of_nonneg_left ?_ h2
    exact mul_le_mul_of_nonneg_left hT4le hS13
  have hsum3 : 1728 * (Cat * S ^ 13 * ‖qParamFun (ModularGroup.S • w)‖) * (C4 ^ 2 * T ^ 8)
        * (Cr * T ^ 8) * (Cinv * s ^ 12 * Real.exp (2 * Real.pi / s))
      ≤ (1728 * Cat * C4 ^ 2 * Cr * Cinv) * (S ^ 13 * T ^ 32) := by
    have hfac : 1728 * (Cat * S ^ 13 * ‖qParamFun (ModularGroup.S • w)‖) * (C4 ^ 2 * T ^ 8)
          * (Cr * T ^ 8) * (Cinv * s ^ 12 * Real.exp (2 * Real.pi / s))
        = 1728 * Cat * C4 ^ 2 * Cr * Cinv
            * (‖qParamFun (ModularGroup.S • w)‖ * s ^ 12 * Real.exp (2 * Real.pi / s))
            * (S ^ 13 * T ^ 16) := by ring
    rw [hfac]
    have hnn : (0 : ℝ) ≤ 1728 * Cat * C4 ^ 2 * Cr * Cinv := by positivity
    have hmid : (‖qParamFun (ModularGroup.S • w)‖ * s ^ 12 * Real.exp (2 * Real.pi / s))
        * (S ^ 13 * T ^ 16) ≤ S ^ 13 * T ^ 32 := by
      have h1 := mul_le_mul_of_nonneg_right hq_exps (by positivity : (0 : ℝ) ≤ S ^ 13 * T ^ 16)
      rw [one_mul] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hT16le hS13)
    calc 1728 * Cat * C4 ^ 2 * Cr * Cinv
          * (‖qParamFun (ModularGroup.S • w)‖ * s ^ 12 * Real.exp (2 * Real.pi / s))
          * (S ^ 13 * T ^ 16)
        = 1728 * Cat * C4 ^ 2 * Cr * Cinv
            * ((‖qParamFun (ModularGroup.S • w)‖ * s ^ 12 * Real.exp (2 * Real.pi / s))
              * (S ^ 13 * T ^ 16)) := by ring
      _ ≤ 1728 * Cat * C4 ^ 2 * Cr * Cinv * (S ^ 13 * T ^ 32) :=
          mul_le_mul_of_nonneg_left hmid hnn
  have hKK : (6 * CA * Cd * Cat + 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2))
        + (1728 * 8 * Cat * Cd) + (1728 * Cat * C4 ^ 2 * Cr * Cinv) ≤ K := by
    rw [hK]; linarith
  have hfin1 : ‖(Xi24r0 w + Xi24r2 w - 2 * Xi24R0 w)
          * (6 * Xi24delta (imagAxis s hs) * jInvariantFun w
            + 6 * E4Fun (imagAxis s hs)
              * (288 * DeltaFun (imagAxis s hs)
                - Xi24delta (imagAxis s hs) * E4Fun (imagAxis s hs) ^ 2)
              / DeltaFun (imagAxis s hs))‖
        + ‖(1728 : ℂ) * (7 * Xi24R0 w - Xi24r0 w) * Xi24delta (imagAxis s hs)‖
      ≤ ((6 * CA * Cd * Cat + 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2))
          + (1728 * 8 * Cat * Cd)) * (S ^ 13 * T ^ 32) := by
    have h := add_le_add (le_trans hterm1 hsum1) (le_trans hterm2 hsum2)
    have heq : (6 * CA * Cd * Cat + 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2))
            * (S ^ 13 * T ^ 32) + (1728 * 8 * Cat * Cd) * (S ^ 13 * T ^ 32)
        = ((6 * CA * Cd * Cat + 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2))
            + (1728 * 8 * Cat * Cd)) * (S ^ 13 * T ^ 32) := by ring
    rwa [heq] at h
  have hfin2 : ‖(Xi24r0 w + Xi24r2 w - 2 * Xi24R0 w)
          * (6 * Xi24delta (imagAxis s hs) * jInvariantFun w
            + 6 * E4Fun (imagAxis s hs)
              * (288 * DeltaFun (imagAxis s hs)
                - Xi24delta (imagAxis s hs) * E4Fun (imagAxis s hs) ^ 2)
              / DeltaFun (imagAxis s hs))‖
        + ‖(1728 : ℂ) * (7 * Xi24R0 w - Xi24r0 w) * Xi24delta (imagAxis s hs)‖
        + ‖(1728 : ℂ) * Xi24r1 w * E4Fun (imagAxis s hs) ^ 2
            * (5 * E4Fun (imagAxis s hs) ^ 2
              - 7 * E4Fun (imagAxis s hs) * E2Fun (imagAxis s hs) ^ 2
              + 2 * E6Fun (imagAxis s hs) * E2Fun (imagAxis s hs))
            / DeltaFun (imagAxis s hs)‖
      ≤ ((6 * CA * Cd * Cat + 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2))
          + (1728 * 8 * Cat * Cd) + (1728 * Cat * C4 ^ 2 * Cr * Cinv)) * (S ^ 13 * T ^ 32) := by
    have h := add_le_add hfin1 (le_trans hterm3 hsum3)
    have heq : ((6 * CA * Cd * Cat + 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2))
            + (1728 * 8 * Cat * Cd)) * (S ^ 13 * T ^ 32)
          + (1728 * Cat * C4 ^ 2 * Cr * Cinv) * (S ^ 13 * T ^ 32)
        = ((6 * CA * Cd * Cat + 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2))
            + (1728 * 8 * Cat * Cd) + (1728 * Cat * C4 ^ 2 * Cr * Cinv))
            * (S ^ 13 * T ^ 32) := by ring
    rwa [heq] at h
  have hKK : (6 * CA * Cd * Cat + 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2))
        + (1728 * 8 * Cat * Cd) + (1728 * Cat * C4 ^ 2 * Cr * Cinv) ≤ K := by
    rw [hK]; linarith
  have hlast : ((6 * CA * Cd * Cat + 6 * CA * C4 * Cinv * (288 * CΔ + Cd * C4 ^ 2))
        + (1728 * 8 * Cat * Cd) + (1728 * Cat * C4 ^ 2 * Cr * Cinv)) * (S ^ 13 * T ^ 32)
      ≤ K * S ^ 13 * T ^ 32 := by
    rw [show K * S ^ 13 * T ^ 32 = K * (S ^ 13 * T ^ 32) by ring]
    exact mul_le_mul_of_nonneg_right hKK (by positivity)
  have hfin : ‖Xi24 w (imagAxis s hs)‖ ≤ K * S ^ 13 * T ^ 32 := htri.trans (hfin2.trans hlast)
  have hgoal : K * (scale w) ^ (13:ℝ) * (1 + s⁻¹) ^ (32:ℝ) = K * S ^ 13 * T ^ 32 := by
    have h13 : (((13 : ℕ) : ℝ)) = (13 : ℝ) := by norm_num
    have h32 : (((32 : ℕ) : ℝ)) = (32 : ℝ) := by norm_num
    rw [hS, hT, ← h13, ← h32, Real.rpow_natCast, Real.rpow_natCast]
  rw [hgoal]
  exact hfin

end

end Work.Asymptotics
