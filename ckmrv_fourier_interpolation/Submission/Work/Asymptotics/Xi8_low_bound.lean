import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Xi8_bound_E
import Submission.Work.Asymptotics.EBase
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atZero
import Submission.Work.Asymptotics.DeltaFun_upper_sharp

noncomputable section
open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics

open Work.Kernels

set_option maxHeartbeats 1000000

/-! ## Elementary facts about the imaginary axis `it`

`imagAxis t ht = i t`.  We record the imaginary part, the coercion and the norm, and the
`S`-image `S • (i t) = i / t` (from `imagAxis_smul_S` in `DeltaFun_imagAxis_atZero`). -/

lemma imagAxis_im' (s : ℝ) (hs : 0 < s) : (imagAxis s hs).im = s := by simp [imagAxis]

lemma norm_imagAxis_coe' (s : ℝ) (hs : 0 < s) :
    ‖((imagAxis s hs : UpperHalfPlane) : ℂ)‖ = s := by
  rw [show ((imagAxis s hs : UpperHalfPlane) : ℂ) = (s : ℂ) * Complex.I from rfl, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]

/-! ## The two `S`-conjugation identities for the `z`-atoms

The numerators `E₄(z) - E₂(z)²` and `E₄(z)² - E₆(z)E₂(z)` transform neatly under `S`: with
`w = S • z` the powers of `w` that appear are exactly the weight defects, and the anomalous
`E₂` term contributes a single extra monomial. -/

/-- `E₄(z) - E₂(z)²` in terms of `w = S • z`. -/
lemma E4Fun_sub_sq_E2Fun_S (z : UpperHalfPlane) :
    E4Fun z - (E2Fun z) ^ 2
      = (((ModularGroup.S • z : UpperHalfPlane)) : ℂ) ^ 4 *
            (E4Fun (ModularGroup.S • z) - (E2Fun (ModularGroup.S • z)) ^ 2)
        + 12 * Complex.I * (((ModularGroup.S • z : UpperHalfPlane)) : ℂ) ^ 3 *
            E2Fun (ModularGroup.S • z) / (Real.pi : ℂ)
        + 36 * (((ModularGroup.S • z : UpperHalfPlane)) : ℂ) ^ 2 / ((Real.pi : ℂ)) ^ 2 := by
  rw [E4Fun_S_smul' z, E2Fun_S_smul' z]
  have hpi : (Real.pi : ℂ) ≠ 0 := by simp
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `E₄(z)² - E₆(z)E₂(z)` in terms of `w = S • z`. -/
lemma sq_E4Fun_sub_E6E2_S (z : UpperHalfPlane) :
    (E4Fun z) ^ 2 - E6Fun z * E2Fun z
      = (((ModularGroup.S • z : UpperHalfPlane)) : ℂ) ^ 8 *
            ((E4Fun (ModularGroup.S • z)) ^ 2
              - E6Fun (ModularGroup.S • z) * E2Fun (ModularGroup.S • z))
        + 6 * Complex.I * (((ModularGroup.S • z : UpperHalfPlane)) : ℂ) ^ 7 *
            E6Fun (ModularGroup.S • z) / (Real.pi : ℂ) := by
  rw [E4Fun_S_smul' z, E6Fun_S_smul' z, E2Fun_S_smul' z]
  have hpi : (Real.pi : ℂ) ≠ 0 := by simp
  field_simp
  ring

/-! ## The `z = i s`-atoms are polynomially bounded in `s⁻¹`

Since `S • (i s) = i/s` has imaginary part `s⁻¹ ≥ 1`, the modular forms at `i/s` are
bounded; the `S`-laws turn those bounds into powers of `s⁻¹` at `i s`. -/

theorem imagAxis_atoms_bound :
    ∃ CΔ C4 C6 C2 Cd Ce : ℝ, 0 < CΔ ∧ 0 < C4 ∧ 0 < C6 ∧ 0 < C2 ∧ 0 < Cd ∧ 0 < Ce ∧
      ∀ (s : ℝ) (hs : 0 < s), s ≤ 1 →
        ‖DeltaFun (imagAxis s hs)‖ ≤ CΔ * (1 + s⁻¹) ^ 12 ∧
        ‖E4Fun (imagAxis s hs)‖ ≤ C4 * (1 + s⁻¹) ^ 4 ∧
        ‖E6Fun (imagAxis s hs)‖ ≤ C6 * (1 + s⁻¹) ^ 6 ∧
        ‖E2Fun (imagAxis s hs)‖ ≤ C2 * (1 + s⁻¹) ^ 2 ∧
        ‖E4Fun (imagAxis s hs) - (E2Fun (imagAxis s hs)) ^ 2‖ ≤ Cd * (1 + s⁻¹) ^ 4 ∧
        ‖(E4Fun (imagAxis s hs)) ^ 2 - E6Fun (imagAxis s hs) * E2Fun (imagAxis s hs)‖
          ≤ Ce * (1 + s⁻¹) ^ 8 := by
  obtain ⟨CE2, hCE2, hE2b⟩ := E2Fun_bound
  obtain ⟨CE4, hCE4, hE4b⟩ := E4Fun_bound
  obtain ⟨CE6, hCE6, hE6b⟩ := E6Fun_bound
  obtain ⟨Cs, hCs, hd1⟩ := delta1_isBigOq
  obtain ⟨Ce, hCe, heps⟩ := eps_isBigOq
  refine ⟨2, CE4, CE6, CE2 + 6 / Real.pi, Cs + 12 * CE2 / Real.pi + 36 / Real.pi ^ 2,
    Ce + 6 * CE6 / Real.pi, by norm_num, hCE4, hCE6, by positivity, by positivity, by positivity,
    fun s hs hs1 => ?_⟩
  have hs0 : (0:ℝ) ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hsinv1 : (1:ℝ) ≤ s⁻¹ := (one_le_inv₀ hs).mpr hs1
  have hle : s⁻¹ ≤ 1 + s⁻¹ := by linarith
  set w : UpperHalfPlane := imagAxis s⁻¹ (inv_pos.mpr hs) with hwdef
  have hwim : w.im = s⁻¹ := by rw [hwdef]; exact imagAxis_im' _ _
  have hwnorm : ‖((w : UpperHalfPlane) : ℂ)‖ = s⁻¹ := by
    rw [hwdef]; exact norm_imagAxis_coe' _ _
  have hw1 : (1:ℝ) ≤ w.im := by rw [hwim]; exact hsinv1
  have hS : ModularGroup.S • imagAxis s hs = w := by rw [hwdef]; exact imagAxis_smul_S s hs
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Δ
    have hb : ‖DeltaFun w‖ ≤ 2 := by
      have hup := DeltaFun_upper_sharp w hw1
      have hexp1 : Real.exp (-(2 * Real.pi * w.im)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hw1])
      linarith
    rw [DeltaFun_S_smul' (imagAxis s hs), hS, norm_mul, norm_pow, hwnorm]
    have h1 : (s⁻¹) ^ 12 * ‖DeltaFun w‖ ≤ (s⁻¹) ^ 12 * 2 :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hs0 12)
    have h2 : (s⁻¹) ^ 12 ≤ (1 + s⁻¹) ^ 12 := pow_le_pow_left₀ hs0 hle 12
    calc (s⁻¹) ^ 12 * ‖DeltaFun w‖ ≤ (s⁻¹) ^ 12 * 2 := h1
      _ ≤ (1 + s⁻¹) ^ 12 * 2 := by nlinarith [h2]
      _ = 2 * (1 + s⁻¹) ^ 12 := by ring
  · -- E4
    have hb : ‖E4Fun w‖ ≤ CE4 := hE4b w hw1
    rw [E4Fun_S_smul' (imagAxis s hs), hS, norm_mul, norm_pow, hwnorm]
    have h1 : (s⁻¹) ^ 4 * ‖E4Fun w‖ ≤ (s⁻¹) ^ 4 * CE4 :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hs0 4)
    have h2 : (s⁻¹) ^ 4 ≤ (1 + s⁻¹) ^ 4 := pow_le_pow_left₀ hs0 hle 4
    calc (s⁻¹) ^ 4 * ‖E4Fun w‖ ≤ (s⁻¹) ^ 4 * CE4 := h1
      _ ≤ (1 + s⁻¹) ^ 4 * CE4 := mul_le_mul_of_nonneg_right h2 hCE4.le
      _ = CE4 * (1 + s⁻¹) ^ 4 := by ring
  · -- E6
    have hb : ‖E6Fun w‖ ≤ CE6 := hE6b w hw1
    rw [E6Fun_S_smul' (imagAxis s hs), hS, norm_mul, norm_pow, hwnorm]
    have h1 : (s⁻¹) ^ 6 * ‖E6Fun w‖ ≤ (s⁻¹) ^ 6 * CE6 :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hs0 6)
    have h2 : (s⁻¹) ^ 6 ≤ (1 + s⁻¹) ^ 6 := pow_le_pow_left₀ hs0 hle 6
    calc (s⁻¹) ^ 6 * ‖E6Fun w‖ ≤ (s⁻¹) ^ 6 * CE6 := h1
      _ ≤ (1 + s⁻¹) ^ 6 * CE6 := mul_le_mul_of_nonneg_right h2 hCE6.le
      _ = CE6 * (1 + s⁻¹) ^ 6 := by ring
  · -- E2
    have hb : ‖E2Fun w‖ ≤ CE2 := hE2b w hw1
    rw [E2Fun_S_smul' (imagAxis s hs), hS]
    have e1 : ‖((w : UpperHalfPlane) : ℂ) ^ 2 * E2Fun w‖ = (s⁻¹) ^ 2 * ‖E2Fun w‖ := by
      rw [norm_mul, norm_pow, hwnorm]
    have e2 : ‖6 * Complex.I * ((w : UpperHalfPlane) : ℂ) / (Real.pi : ℂ)‖
        = 6 * s⁻¹ / Real.pi := by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, hwnorm,
        Complex.norm_of_nonneg Real.pi_pos.le]
    have h1 : (s⁻¹) ^ 2 * ‖E2Fun w‖ ≤ (s⁻¹) ^ 2 * CE2 :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hs0 2)
    have h2 : (s⁻¹) ^ 2 ≤ (1 + s⁻¹) ^ 2 := pow_le_pow_left₀ hs0 hle 2
    have h3 : s⁻¹ ≤ (1 + s⁻¹) ^ 2 := by nlinarith [sq_nonneg (s⁻¹), hs0]
    have hA := mul_le_mul_of_nonneg_right h2 hCE2.le
    have hB : 6 * s⁻¹ / Real.pi ≤ 6 * (1 + s⁻¹) ^ 2 / Real.pi :=
      div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
    calc ‖((w : UpperHalfPlane) : ℂ) ^ 2 * E2Fun w
          - 6 * Complex.I * ((w : UpperHalfPlane) : ℂ) / (Real.pi : ℂ)‖
        ≤ ‖((w : UpperHalfPlane) : ℂ) ^ 2 * E2Fun w‖
            + ‖6 * Complex.I * ((w : UpperHalfPlane) : ℂ) / (Real.pi : ℂ)‖ := norm_sub_le _ _
      _ = (s⁻¹) ^ 2 * ‖E2Fun w‖ + 6 * s⁻¹ / Real.pi := by rw [e1, e2]
      _ ≤ (s⁻¹) ^ 2 * CE2 + 6 * s⁻¹ / Real.pi := by linarith [h1]
      _ ≤ (CE2 + 6 / Real.pi) * (1 + s⁻¹) ^ 2 := by
          have hexp : (CE2 + 6 / Real.pi) * (1 + s⁻¹) ^ 2
              = (1 + s⁻¹) ^ 2 * CE2 + 6 * (1 + s⁻¹) ^ 2 / Real.pi := by ring
          rw [hexp]; linarith [hA, hB]
  · -- E4 - E2^2
    have hb : ‖E4Fun w - (E2Fun w) ^ 2‖ ≤ Cs := by
      have h := hd1 w hw1
      have hq := norm_qParamFun_le_one w hw1
      rw [pow_one] at h
      nlinarith [h, hq, hCs]
    have hb2 : ‖E2Fun w‖ ≤ CE2 := hE2b w hw1
    rw [E4Fun_sub_sq_E2Fun_S (imagAxis s hs), hS]
    have e1 : ‖((w : UpperHalfPlane) : ℂ) ^ 4 * (E4Fun w - (E2Fun w) ^ 2)‖
        = (s⁻¹) ^ 4 * ‖E4Fun w - (E2Fun w) ^ 2‖ := by
      rw [norm_mul, norm_pow, hwnorm]
    have e2 : ‖12 * Complex.I * ((w : UpperHalfPlane) : ℂ) ^ 3 * E2Fun w / (Real.pi : ℂ)‖
        = 12 * (s⁻¹) ^ 3 * ‖E2Fun w‖ / Real.pi := by
      rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, hwnorm, Complex.norm_I, mul_one,
        Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le]
    have e3 : ‖36 * ((w : UpperHalfPlane) : ℂ) ^ 2 / (Real.pi : ℂ) ^ 2‖
        = 36 * (s⁻¹) ^ 2 / Real.pi ^ 2 := by
      rw [norm_div, norm_mul, norm_pow, norm_pow, hwnorm, Complex.norm_ofNat,
        Complex.norm_of_nonneg Real.pi_pos.le]
    have h1 : (s⁻¹) ^ 4 * ‖E4Fun w - (E2Fun w) ^ 2‖ ≤ (s⁻¹) ^ 4 * Cs :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hs0 4)
    have h2 : 12 * (s⁻¹) ^ 3 * ‖E2Fun w‖ / Real.pi ≤ 12 * (s⁻¹) ^ 3 * CE2 / Real.pi :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb2 (by positivity)) Real.pi_pos.le
    have hA : (s⁻¹) ^ 4 * Cs ≤ (1 + s⁻¹) ^ 4 * Cs :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs0 hle 4) hCs.le
    have hB : 12 * (s⁻¹) ^ 3 * CE2 / Real.pi ≤ 12 * (1 + s⁻¹) ^ 4 * CE2 / Real.pi := by
      have h3v : (s⁻¹) ^ 3 ≤ (1 + s⁻¹) ^ 4 := by
        have h1' : (s⁻¹) ^ 3 ≤ (1 + s⁻¹) ^ 3 := pow_le_pow_left₀ hs0 hle 3
        have hu : (1:ℝ) ≤ 1 + s⁻¹ := by linarith
        have h2' : (1 + s⁻¹) ^ 3 ≤ (1 + s⁻¹) ^ 4 :=
          pow_le_pow_right₀ hu (by norm_num : (3:ℕ) ≤ 4)
        exact le_trans h1' h2'
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hCE2.le) Real.pi_pos.le
    have hC : 36 * (s⁻¹) ^ 2 / Real.pi ^ 2 ≤ 36 * (1 + s⁻¹) ^ 4 / Real.pi ^ 2 := by
      have h2v : (s⁻¹) ^ 2 ≤ (1 + s⁻¹) ^ 4 := by
        have h2' : (s⁻¹) ^ 2 ≤ (1 + s⁻¹) ^ 2 := pow_le_pow_left₀ hs0 hle 2
        have hu : (1:ℝ) ≤ 1 + s⁻¹ := by linarith
        have h3' : (1 + s⁻¹) ^ 2 ≤ (1 + s⁻¹) ^ 4 :=
          pow_le_pow_right₀ hu (by norm_num : (2:ℕ) ≤ 4)
        exact le_trans h2' h3'
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    calc ‖((w : UpperHalfPlane) : ℂ) ^ 4 * (E4Fun w - (E2Fun w) ^ 2)
          + 12 * Complex.I * ((w : UpperHalfPlane) : ℂ) ^ 3 * E2Fun w / (Real.pi : ℂ)
          + 36 * ((w : UpperHalfPlane) : ℂ) ^ 2 / (Real.pi : ℂ) ^ 2‖
        ≤ ‖((w : UpperHalfPlane) : ℂ) ^ 4 * (E4Fun w - (E2Fun w) ^ 2)
            + 12 * Complex.I * ((w : UpperHalfPlane) : ℂ) ^ 3 * E2Fun w / (Real.pi : ℂ)‖
          + ‖36 * ((w : UpperHalfPlane) : ℂ) ^ 2 / (Real.pi : ℂ) ^ 2‖ := norm_add_le _ _
      _ ≤ (‖((w : UpperHalfPlane) : ℂ) ^ 4 * (E4Fun w - (E2Fun w) ^ 2)‖
            + ‖12 * Complex.I * ((w : UpperHalfPlane) : ℂ) ^ 3 * E2Fun w / (Real.pi : ℂ)‖)
          + ‖36 * ((w : UpperHalfPlane) : ℂ) ^ 2 / (Real.pi : ℂ) ^ 2‖ := by
          linarith [norm_add_le (((w : UpperHalfPlane) : ℂ) ^ 4 * (E4Fun w - (E2Fun w) ^ 2))
            (12 * Complex.I * ((w : UpperHalfPlane) : ℂ) ^ 3 * E2Fun w / (Real.pi : ℂ))]
      _ = ((s⁻¹) ^ 4 * ‖E4Fun w - (E2Fun w) ^ 2‖ + 12 * (s⁻¹) ^ 3 * ‖E2Fun w‖ / Real.pi)
          + 36 * (s⁻¹) ^ 2 / Real.pi ^ 2 := by rw [e1, e2, e3]
      _ ≤ ((s⁻¹) ^ 4 * Cs + 12 * (s⁻¹) ^ 3 * CE2 / Real.pi) + 36 * (s⁻¹) ^ 2 / Real.pi ^ 2 := by
          linarith [h1, h2]
      _ ≤ (Cs + 12 * CE2 / Real.pi + 36 / Real.pi ^ 2) * (1 + s⁻¹) ^ 4 := by
          have hexp : (Cs + 12 * CE2 / Real.pi + 36 / Real.pi ^ 2) * (1 + s⁻¹) ^ 4
              = (1 + s⁻¹) ^ 4 * Cs + 12 * (1 + s⁻¹) ^ 4 * CE2 / Real.pi
                + 36 * (1 + s⁻¹) ^ 4 / Real.pi ^ 2 := by ring
          rw [hexp]; linarith [hA, hB, hC]
  · -- E4^2 - E6 E2
    have hb : ‖(E4Fun w) ^ 2 - E6Fun w * E2Fun w‖ ≤ Ce := by
      have h := heps w hw1
      have hq := norm_qParamFun_le_one w hw1
      rw [pow_one] at h
      nlinarith [h, hq, hCe]
    have hb6 : ‖E6Fun w‖ ≤ CE6 := hE6b w hw1
    rw [sq_E4Fun_sub_E6E2_S (imagAxis s hs), hS]
    have e1 : ‖((w : UpperHalfPlane) : ℂ) ^ 8 * ((E4Fun w) ^ 2 - E6Fun w * E2Fun w)‖
        = (s⁻¹) ^ 8 * ‖(E4Fun w) ^ 2 - E6Fun w * E2Fun w‖ := by
      rw [norm_mul, norm_pow, hwnorm]
    have e2 : ‖6 * Complex.I * ((w : UpperHalfPlane) : ℂ) ^ 7 * E6Fun w / (Real.pi : ℂ)‖
        = 6 * (s⁻¹) ^ 7 * ‖E6Fun w‖ / Real.pi := by
      rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, hwnorm, Complex.norm_I, mul_one,
        Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le]
    have h1 : (s⁻¹) ^ 8 * ‖(E4Fun w) ^ 2 - E6Fun w * E2Fun w‖ ≤ (s⁻¹) ^ 8 * Ce :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hs0 8)
    have h2 : 6 * (s⁻¹) ^ 7 * ‖E6Fun w‖ / Real.pi ≤ 6 * (s⁻¹) ^ 7 * CE6 / Real.pi :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb6 (by positivity)) Real.pi_pos.le
    have hu : (1:ℝ) ≤ 1 + s⁻¹ := by linarith
    have h8 : (s⁻¹) ^ 8 ≤ (1 + s⁻¹) ^ 8 := pow_le_pow_left₀ hs0 hle 8
    have h7 : (s⁻¹) ^ 7 ≤ (1 + s⁻¹) ^ 8 := by
      have h1' : (s⁻¹) ^ 7 ≤ (1 + s⁻¹) ^ 7 := pow_le_pow_left₀ hs0 hle 7
      have h2' : (1 + s⁻¹) ^ 7 ≤ (1 + s⁻¹) ^ 8 :=
        pow_le_pow_right₀ hu (by norm_num : (7:ℕ) ≤ 8)
      exact le_trans h1' h2'
    have hA : (s⁻¹) ^ 8 * Ce ≤ (1 + s⁻¹) ^ 8 * Ce := mul_le_mul_of_nonneg_right h8 hCe.le
    have hB : 6 * (s⁻¹) ^ 7 * CE6 / Real.pi ≤ 6 * (1 + s⁻¹) ^ 8 * CE6 / Real.pi :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h7 (by norm_num)) hCE6.le)
        Real.pi_pos.le
    calc ‖((w : UpperHalfPlane) : ℂ) ^ 8 * ((E4Fun w) ^ 2 - E6Fun w * E2Fun w)
          + 6 * Complex.I * ((w : UpperHalfPlane) : ℂ) ^ 7 * E6Fun w / (Real.pi : ℂ)‖
        ≤ ‖((w : UpperHalfPlane) : ℂ) ^ 8 * ((E4Fun w) ^ 2 - E6Fun w * E2Fun w)‖
          + ‖6 * Complex.I * ((w : UpperHalfPlane) : ℂ) ^ 7 * E6Fun w / (Real.pi : ℂ)‖ :=
          norm_add_le _ _
      _ = (s⁻¹) ^ 8 * ‖(E4Fun w) ^ 2 - E6Fun w * E2Fun w‖
          + 6 * (s⁻¹) ^ 7 * ‖E6Fun w‖ / Real.pi := by rw [e1, e2]
      _ ≤ (s⁻¹) ^ 8 * Ce + 6 * (s⁻¹) ^ 7 * CE6 / Real.pi := by linarith [h1, h2]
      _ ≤ (Ce + 6 * CE6 / Real.pi) * (1 + s⁻¹) ^ 8 := by
          have hexp : (Ce + 6 * CE6 / Real.pi) * (1 + s⁻¹) ^ 8
              = (1 + s⁻¹) ^ 8 * Ce + 6 * (1 + s⁻¹) ^ 8 * CE6 / Real.pi := by ring
          rw [hexp]; linarith [hA, hB]

/-! ## The three pieces of the `S`-decomposition are polynomially bounded

`Xi8_S_decomposition` writes `Ξ₈(τ,z) = T₁ + T₂ - T₃` with the three pieces displayed below.
Every `w = S • τ`-factor is bounded by a power of `scale τ` (`‖S • τ‖ ≤ scale τ`), the
cusp-`0`-atoms at `w` are bounded (`E2/E4/E6Fun_bound`), the two `q`-numerators are `O(q)`
(`XiN1/XiN2_isBigOq`) and `‖q w‖ ≲ ‖Δ w‖` (`DeltaFun_lower`), so the `q w`-factors cancel in
`T₁`.  The `z`-factors are left symbolic: they are controlled by `imagAxis_atoms_bound`. -/

theorem Xi8_S_pieces_bound :
    ∃ K1 K2 K3 : ℝ, 0 < K1 ∧ 0 < K2 ∧ 0 < K3 ∧
      ∀ (τ z : UpperHalfPlane), (3/2:ℝ) ≤ (ModularGroup.S • τ).im →
        ‖DeltaFun z * (E4Fun (ModularGroup.S • τ)) ^ 2 / DeltaFun (ModularGroup.S • τ) *
            (- (((ModularGroup.S • τ : UpperHalfPlane)) : ℂ) ^ 5 * XiN1 (ModularGroup.S • τ)
              + (6 * Complex.I / (Real.pi : ℂ)) *
                  (((ModularGroup.S • τ : UpperHalfPlane)) : ℂ) ^ 4 * XiN2 (ModularGroup.S • τ))‖
          ≤ K1 * (scale τ) ^ 5 * ‖DeltaFun z‖ ∧
        ‖(((ModularGroup.S • τ : UpperHalfPlane)) : ℂ) ^ 5 * E6Fun (ModularGroup.S • τ)
            * (E4Fun z) ^ 2 * (E4Fun z - (E2Fun z) ^ 2)‖
          ≤ K2 * (scale τ) ^ 5 * ‖E4Fun z‖ ^ 2
              * ‖E4Fun z - (E2Fun z) ^ 2‖ ∧
        ‖((E4Fun z) ^ 2 - E6Fun z * E2Fun z) *
            (2 * (((ModularGroup.S • τ : UpperHalfPlane)) : ℂ) ^ 5 * E2Fun (ModularGroup.S • τ)
                * E4Fun (ModularGroup.S • τ) * E4Fun z
              - 6 * Complex.I * (((ModularGroup.S • τ : UpperHalfPlane)) : ℂ) ^ 4
                * E4Fun (ModularGroup.S • τ) * E4Fun z / (Real.pi : ℂ))‖
          ≤ K3 * (scale τ) ^ 5
              * ‖(E4Fun z) ^ 2 - E6Fun z * E2Fun z‖
              * ‖E4Fun z‖ := by
  obtain ⟨C1, hC1, hN1⟩ := XiN1_isBigOq
  obtain ⟨C2, hC2, hN2⟩ := XiN2_isBigOq
  obtain ⟨c0, hc0, hΔlow⟩ := DeltaFun_lower
  obtain ⟨CE2, hCE2, hE2b⟩ := E2Fun_bound
  obtain ⟨CE4, hCE4, hE4b⟩ := E4Fun_bound
  obtain ⟨CE6, hCE6, hE6b⟩ := E6Fun_bound
  have hK1 : 0 < CE4 ^ 2 / c0 * (C1 + 6 * C2 / Real.pi) :=
    mul_pos (div_pos (pow_pos hCE4 2) hc0)
      (add_pos hC1 (div_pos (mul_pos (by norm_num) hC2) Real.pi_pos))
  have hK3 : 0 < 2 * CE2 * CE4 + 6 * CE4 / Real.pi :=
    add_pos (mul_pos (mul_pos (by norm_num) hCE2) hCE4)
      (div_pos (mul_pos (by norm_num) hCE4) Real.pi_pos)
  refine ⟨_, CE6, _, hK1, hCE6, hK3, fun τ z hτ => ?_⟩
  set w : UpperHalfPlane := ModularGroup.S • τ with hwdef
  have hw1 : (1:ℝ) ≤ w.im := by rw [hwdef]; linarith
  have hsc0 : (0:ℝ) ≤ scale τ := (scale_pos τ).le
  have hs1 : (1:ℝ) ≤ scale τ := one_le_scale τ
  have hu : ‖((w : UpperHalfPlane) : ℂ)‖ ≤ scale τ := by
    rw [hwdef]; exact norm_coe_S_smul_le_scale τ
  have hu0 : (0:ℝ) ≤ ‖((w : UpperHalfPlane) : ℂ)‖ := norm_nonneg _
  have hu5 : ‖((w : UpperHalfPlane) : ℂ)‖ ^ 5 ≤ (scale τ) ^ 5 :=
    pow_le_pow_left₀ hu0 hu 5
  have hu4 : ‖((w : UpperHalfPlane) : ℂ)‖ ^ 4 ≤ (scale τ) ^ 5 :=
    le_trans (pow_le_pow_left₀ hu0 hu 4) (pow_le_pow_right₀ hs1 (by norm_num : (4:ℕ) ≤ 5))
  have hqw0 : 0 < ‖qParamFun w‖ := norm_pos_iff.mpr (qParamFun_ne_zero' w)
  have hN1b : ‖XiN1 w‖ ≤ C1 * ‖qParamFun w‖ := by simpa using hN1 w hw1
  have hN2b : ‖XiN2 w‖ ≤ C2 * ‖qParamFun w‖ := by simpa using hN2 w hw1
  have hΔb : c0 * ‖qParamFun w‖ ≤ ‖DeltaFun w‖ := by simpa using hΔlow w hw1
  have hE2w : ‖E2Fun w‖ ≤ CE2 := hE2b w hw1
  have hE4w : ‖E4Fun w‖ ≤ CE4 := hE4b w hw1
  have hE6w : ‖E6Fun w‖ ≤ CE6 := hE6b w hw1
  have h6pi : ‖(6 * Complex.I / (Real.pi : ℂ))‖ = 6 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_of_nonneg Real.pi_pos.le]
  have h6pi0 : (0:ℝ) ≤ 6 / Real.pi := div_nonneg (by norm_num) Real.pi_pos.le
  refine ⟨?_, ?_, ?_⟩
  · -- piece 1
    have hbr : ‖- (((w : UpperHalfPlane)) : ℂ) ^ 5 * XiN1 w
          + (6 * Complex.I / (Real.pi : ℂ)) * (((w : UpperHalfPlane)) : ℂ) ^ 4 * XiN2 w‖
        ≤ (C1 + 6 * C2 / Real.pi) * (scale τ) ^ 5 * ‖qParamFun w‖ := by
      have h1 : ‖- (((w : UpperHalfPlane)) : ℂ) ^ 5 * XiN1 w‖
          ≤ (scale τ) ^ 5 * (C1 * ‖qParamFun w‖) := by
        rw [norm_mul, norm_neg, norm_pow]
        exact mul_le_mul hu5 hN1b (norm_nonneg _) (pow_nonneg hsc0 5)
      have h2 : ‖(6 * Complex.I / (Real.pi : ℂ)) * (((w : UpperHalfPlane)) : ℂ) ^ 4 * XiN2 w‖
          ≤ (6 / Real.pi) * (scale τ) ^ 5 * (C2 * ‖qParamFun w‖) := by
        rw [norm_mul, norm_mul, norm_pow, h6pi]
        exact mul_le_mul (mul_le_mul (le_refl _) hu4 (pow_nonneg (norm_nonneg _) 4) h6pi0)
          hN2b (norm_nonneg _) (mul_nonneg h6pi0 (pow_nonneg hsc0 5))
      calc ‖- (((w : UpperHalfPlane)) : ℂ) ^ 5 * XiN1 w
            + (6 * Complex.I / (Real.pi : ℂ)) * (((w : UpperHalfPlane)) : ℂ) ^ 4 * XiN2 w‖
          ≤ ‖- (((w : UpperHalfPlane)) : ℂ) ^ 5 * XiN1 w‖
            + ‖(6 * Complex.I / (Real.pi : ℂ)) * (((w : UpperHalfPlane)) : ℂ) ^ 4
                * XiN2 w‖ := norm_add_le _ _
        _ ≤ (scale τ) ^ 5 * (C1 * ‖qParamFun w‖)
            + (6 / Real.pi) * (scale τ) ^ 5 * (C2 * ‖qParamFun w‖) := add_le_add h1 h2
        _ = (C1 + 6 * C2 / Real.pi) * (scale τ) ^ 5 * ‖qParamFun w‖ := by ring
    have hfac : ‖DeltaFun z * (E4Fun w) ^ 2 / DeltaFun w‖
        ≤ ‖DeltaFun z‖ * CE4 ^ 2 / (c0 * ‖qParamFun w‖) := by
      have hnum : ‖DeltaFun z‖ * ‖E4Fun w‖ ^ 2 ≤ ‖DeltaFun z‖ * CE4 ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hE4w 2) (norm_nonneg _)
      have hinv : (‖DeltaFun w‖)⁻¹ ≤ (c0 * ‖qParamFun w‖)⁻¹ :=
        inv_anti₀ (mul_pos hc0 hqw0) hΔb
      rw [norm_div, norm_mul, norm_pow, div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul hnum hinv (inv_nonneg.mpr (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (pow_nonneg hCE4.le 2))
    rw [norm_mul]
    have hprod : ‖DeltaFun z * (E4Fun w) ^ 2 / DeltaFun w‖
          * ‖- (((w : UpperHalfPlane)) : ℂ) ^ 5 * XiN1 w
              + (6 * Complex.I / (Real.pi : ℂ)) * (((w : UpperHalfPlane)) : ℂ) ^ 4 * XiN2 w‖
        ≤ (‖DeltaFun z‖ * CE4 ^ 2 / (c0 * ‖qParamFun w‖))
          * ((C1 + 6 * C2 / Real.pi) * (scale τ) ^ 5 * ‖qParamFun w‖) :=
      mul_le_mul hfac hbr (norm_nonneg _)
        (div_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hCE4.le 2))
          (mul_nonneg hc0.le hqw0.le))
    have halg : (‖DeltaFun z‖ * CE4 ^ 2 / (c0 * ‖qParamFun w‖))
          * ((C1 + 6 * C2 / Real.pi) * (scale τ) ^ 5 * ‖qParamFun w‖)
        = (CE4 ^ 2 / c0 * (C1 + 6 * C2 / Real.pi)) * (scale τ) ^ 5 * ‖DeltaFun z‖ := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
      field_simp
    exact le_trans hprod (le_of_eq halg)
  · -- piece 2
    have e : ‖(((w : UpperHalfPlane)) : ℂ) ^ 5 * E6Fun w * (E4Fun z) ^ 2
          * (E4Fun z - (E2Fun z) ^ 2)‖
        = ‖((w : UpperHalfPlane) : ℂ)‖ ^ 5 * ‖E6Fun w‖ * ‖E4Fun z‖ ^ 2
          * ‖E4Fun z - (E2Fun z) ^ 2‖ := by
      rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
    rw [e]
    have h1 : ‖((w : UpperHalfPlane) : ℂ)‖ ^ 5 * ‖E6Fun w‖ ≤ (scale τ) ^ 5 * CE6 :=
      mul_le_mul hu5 hE6w (norm_nonneg _) (pow_nonneg hsc0 5)
    have h2 : (‖((w : UpperHalfPlane) : ℂ)‖ ^ 5 * ‖E6Fun w‖) * ‖E4Fun z‖ ^ 2
        ≤ ((scale τ) ^ 5 * CE6) * ‖E4Fun z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg _) 2)
    calc ‖((w : UpperHalfPlane) : ℂ)‖ ^ 5 * ‖E6Fun w‖ * ‖E4Fun z‖ ^ 2
          * ‖E4Fun z - (E2Fun z) ^ 2‖
        ≤ ((scale τ) ^ 5 * CE6) * ‖E4Fun z‖ ^ 2 * ‖E4Fun z - (E2Fun z) ^ 2‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = CE6 * (scale τ) ^ 5 * ‖E4Fun z‖ ^ 2 * ‖E4Fun z - (E2Fun z) ^ 2‖ := by ring
  · -- piece 3
    have hA : ‖2 * (((w : UpperHalfPlane)) : ℂ) ^ 5 * E2Fun w * E4Fun w * E4Fun z‖
        ≤ 2 * (scale τ) ^ 5 * CE2 * CE4 * ‖E4Fun z‖ := by
      have e : ‖2 * (((w : UpperHalfPlane)) : ℂ) ^ 5 * E2Fun w * E4Fun w * E4Fun z‖
          = 2 * ‖(((w : UpperHalfPlane)) : ℂ)‖ ^ 5 * ‖E2Fun w‖ * ‖E4Fun w‖ * ‖E4Fun z‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat]
      rw [e]
      have h1 : 2 * ‖(((w : UpperHalfPlane)) : ℂ)‖ ^ 5 ≤ 2 * (scale τ) ^ 5 :=
        mul_le_mul_of_nonneg_left hu5 (by norm_num)
      have h2 : 2 * ‖(((w : UpperHalfPlane)) : ℂ)‖ ^ 5 * ‖E2Fun w‖
          ≤ 2 * (scale τ) ^ 5 * CE2 :=
        mul_le_mul h1 hE2w (norm_nonneg _) (mul_nonneg (by norm_num) (pow_nonneg hsc0 5))
      have h3 : 2 * ‖(((w : UpperHalfPlane)) : ℂ)‖ ^ 5 * ‖E2Fun w‖ * ‖E4Fun w‖
          ≤ 2 * (scale τ) ^ 5 * CE2 * CE4 :=
        mul_le_mul h2 hE4w (norm_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hsc0 5)) hCE2.le)
      exact mul_le_mul h3 (le_refl _) (norm_nonneg _)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hsc0 5)) hCE2.le) hCE4.le)
    have hB : ‖6 * Complex.I * (((w : UpperHalfPlane)) : ℂ) ^ 4 * E4Fun w * E4Fun z
          / (Real.pi : ℂ)‖ ≤ 6 * (scale τ) ^ 5 * CE4 * ‖E4Fun z‖ / Real.pi := by
      have hnorm : ‖6 * Complex.I * (((w : UpperHalfPlane)) : ℂ) ^ 4 * E4Fun w * E4Fun z
            / (Real.pi : ℂ)‖
          = 6 * ‖(((w : UpperHalfPlane)) : ℂ)‖ ^ 4 * ‖E4Fun w‖ * ‖E4Fun z‖ / Real.pi := by
        rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_I, mul_one,
          Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le]
      rw [hnorm]
      have h1 : 6 * ‖(((w : UpperHalfPlane)) : ℂ)‖ ^ 4 ≤ 6 * (scale τ) ^ 5 :=
        mul_le_mul_of_nonneg_left hu4 (by norm_num)
      have h2 : 6 * ‖(((w : UpperHalfPlane)) : ℂ)‖ ^ 4 * ‖E4Fun w‖
          ≤ 6 * (scale τ) ^ 5 * CE4 :=
        mul_le_mul h1 hE4w (norm_nonneg _) (mul_nonneg (by norm_num) (pow_nonneg hsc0 5))
      exact div_le_div_of_nonneg_right
        (mul_le_mul h2 (le_refl _) (norm_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hsc0 5)) hCE4.le))
        Real.pi_pos.le
    have hinner : ‖2 * (((w : UpperHalfPlane)) : ℂ) ^ 5 * E2Fun w * E4Fun w * E4Fun z
          - 6 * Complex.I * (((w : UpperHalfPlane)) : ℂ) ^ 4 * E4Fun w * E4Fun z
              / (Real.pi : ℂ)‖
        ≤ (2 * CE2 * CE4 + 6 * CE4 / Real.pi) * (scale τ) ^ 5 * ‖E4Fun z‖ := by
      calc ‖2 * (((w : UpperHalfPlane)) : ℂ) ^ 5 * E2Fun w * E4Fun w * E4Fun z
            - 6 * Complex.I * (((w : UpperHalfPlane)) : ℂ) ^ 4 * E4Fun w * E4Fun z
                / (Real.pi : ℂ)‖
          ≤ ‖2 * (((w : UpperHalfPlane)) : ℂ) ^ 5 * E2Fun w * E4Fun w * E4Fun z‖
            + ‖6 * Complex.I * (((w : UpperHalfPlane)) : ℂ) ^ 4 * E4Fun w * E4Fun z
                / (Real.pi : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 * (scale τ) ^ 5 * CE2 * CE4 * ‖E4Fun z‖
            + 6 * (scale τ) ^ 5 * CE4 * ‖E4Fun z‖ / Real.pi := add_le_add hA hB
        _ = (2 * CE2 * CE4 + 6 * CE4 / Real.pi) * (scale τ) ^ 5 * ‖E4Fun z‖ := by ring
    rw [norm_mul]
    calc ‖(E4Fun z) ^ 2 - E6Fun z * E2Fun z‖
          * ‖2 * (((w : UpperHalfPlane)) : ℂ) ^ 5 * E2Fun w * E4Fun w * E4Fun z
              - 6 * Complex.I * (((w : UpperHalfPlane)) : ℂ) ^ 4 * E4Fun w * E4Fun z
                  / (Real.pi : ℂ)‖
        ≤ ‖(E4Fun z) ^ 2 - E6Fun z * E2Fun z‖
            * ((2 * CE2 * CE4 + 6 * CE4 / Real.pi) * (scale τ) ^ 5 * ‖E4Fun z‖) :=
          mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
      _ = (2 * CE2 * CE4 + 6 * CE4 / Real.pi) * (scale τ) ^ 5
            * ‖(E4Fun z) ^ 2 - E6Fun z * E2Fun z‖ * ‖E4Fun z‖ := by ring

/-- **The `d = 8` CKMRV numerator `Ξ₈` below the cusp: polynomial bound at `Im z ≤ 1`.**

For `w` in the cusp-`0` tile `E = KEpsilon` and `0 < s ≤ 1` with `s⁻¹ ≤ Im (S • w) − 1` (the
"strictly below the pole height" condition `t ≤ Im (S • w) − 1` for `t = s⁻¹`), the numerator
`Ξ₈(w, i·s)` — which equals `c₈·Δ(i s)·(j w − j (i s))·(i s)²·K₊^{(8)}(w, S·(i s))` — is bounded
polynomially in `scale w` and in `s⁻¹`.

Route: `Xi8_S_decomposition` (proved, `Submission/Work/Asymptotics/Xi8_bound_E.lean`) writes
`Ξ₈(τ,z) = [Δ(z)E₄(σ)²/Δ(σ)]·(−σ⁵XiN1(σ) + (6i/π)σ⁴XiN2(σ))
  + σ⁵E₆(σ)E₄(z)²(E₄(z) − E₂(z)²) − (E₄(z)² − E₆(z)E₂(z))·(2σ⁵E₂(σ)E₄(σ)E₄(z) − 6iσ⁴E₄(σ)E₄(z)/π)`
for all `τ z`, where `σ = S • τ`.  At `τ = w ∈ E`, `σ = S • w` has `Im σ ≥ 2`, so `E₄(σ), E₆(σ), E₂(σ)`
are bounded (`E4Fun_bound`, `E6Fun_bound`, `E2Fun_bound`), `‖σ‖ ≤ scale w`
(`norm_coe_S_smul_le_scale`), `XiN1`, `XiN2` are `O(‖q σ‖)` (`XiN1_isBigOq`, `XiN2_isBigOq`) and
`‖q σ‖ ≲ ‖Δ σ‖` (`DeltaFun_lower`), so `E₄(σ)²XiN1(σ)/Δ(σ)` and `XiN2(σ)/Δ(σ)` are bounded and
every `σ`-factor contributes only powers of `scale w`.  The `z = i s`-atoms are controlled by the
`S`-laws (`Δ(i s) = (i/s)^{12}Δ(i/s)` from `DeltaFun_S_smul`, `E₄(i s) = (i/s)⁴E₄(i/s)`,
`E₆(i s) = (i/s)⁶E₆(i/s)`, `E₂(i s) = (i/s)²E₂(i/s) − 6i(i/s)/π` from `E2Fun_S_smul`), each bounded
by a power of `s⁻¹` using `DeltaFun_upper_sharp`/`E4Fun_bound`/`E6Fun_bound`/`E2Fun_bound` at
`i/s` (`Im = s⁻¹ ≥ 1`). -/
theorem Xi8_low_bound :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (s : ℝ) (hs : 0 < s), w ∈ Work.Asymptotics.KEpsilon → s ≤ 1 →
        s⁻¹ ≤ (ModularGroup.S • w).im - 1 →
        ‖Work.Asymptotics.Xi8 w (Work.Kernels.imagAxis s hs)‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + s⁻¹) ^ M := by
  obtain ⟨CΔ, C4, C6, C2, Cd, Ce, hCΔ, hC4, hC6, hC2, hCd, hCe, hatoms⟩ := imagAxis_atoms_bound
  obtain ⟨K1, K2, K3, hK1, hK2, hK3, hpieces⟩ := Xi8_S_pieces_bound
  have hC : 0 < K1 * CΔ + K2 * C4 ^ 2 * Cd + K3 * Ce * C4 :=
    add_pos (add_pos (mul_pos hK1 hCΔ) (mul_pos (mul_pos hK2 (pow_pos hC4 2)) hCd))
      (mul_pos (mul_pos hK3 hCe) hC4)
  refine ⟨K1 * CΔ + K2 * C4 ^ 2 * Cd + K3 * Ce * C4, 5, 12, hC, by norm_num, by norm_num,
    fun w s hs hwE hs1 _ => ?_⟩
  have hsw : (3 / 2 : ℝ) ≤ (ModularGroup.S • w).im := E_S_im_ge w hwE
  obtain ⟨hΔz, hE4z, hE6z, hE2z, hdz, hez⟩ := hatoms s hs hs1
  obtain ⟨hT1, hT2, hT3⟩ := hpieces w (imagAxis s hs) hsw
  have hsc0 : (0:ℝ) ≤ scale w := (scale_pos w).le
  have hu0 : (0:ℝ) ≤ 1 + s⁻¹ := by
    have := inv_nonneg.mpr hs.le
    linarith
  have hC4z : ‖E4Fun (imagAxis s hs)‖ ^ 2 ≤ C4 ^ 2 * (1 + s⁻¹) ^ 8 := by
    calc ‖E4Fun (imagAxis s hs)‖ ^ 2 ≤ (C4 * (1 + s⁻¹) ^ 4) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hE4z 2
      _ = C4 ^ 2 * (1 + s⁻¹) ^ 8 := by ring
  rw [Xi8_S_decomposition w (imagAxis s hs)]
  have key : ‖(DeltaFun (imagAxis s hs) * (E4Fun (ModularGroup.S • w)) ^ 2
            / DeltaFun (ModularGroup.S • w)) *
            (- (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) ^ 5
                * XiN1 (ModularGroup.S • w)
              + (6 * Complex.I / (Real.pi : ℂ))
                * (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) ^ 4 * XiN2 (ModularGroup.S • w))
          + (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) ^ 5 * E6Fun (ModularGroup.S • w)
              * (E4Fun (imagAxis s hs)) ^ 2
              * (E4Fun (imagAxis s hs) - (E2Fun (imagAxis s hs)) ^ 2)
          - ((E4Fun (imagAxis s hs)) ^ 2 - E6Fun (imagAxis s hs) * E2Fun (imagAxis s hs)) *
              (2 * (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) ^ 5
                  * E2Fun (ModularGroup.S • w) * E4Fun (ModularGroup.S • w)
                  * E4Fun (imagAxis s hs)
                - 6 * Complex.I * (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) ^ 4
                  * E4Fun (ModularGroup.S • w) * E4Fun (imagAxis s hs) / (Real.pi : ℂ))‖
        ≤ (K1 * CΔ + K2 * C4 ^ 2 * Cd + K3 * Ce * C4) * (scale w) ^ 5 * (1 + s⁻¹) ^ 12 := by
    set A : ℂ := (DeltaFun (imagAxis s hs) * (E4Fun (ModularGroup.S • w)) ^ 2
            / DeltaFun (ModularGroup.S • w)) *
            (- (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) ^ 5
                * XiN1 (ModularGroup.S • w)
              + (6 * Complex.I / (Real.pi : ℂ))
                * (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) ^ 4 * XiN2 (ModularGroup.S • w))
      with hA
    set B : ℂ := (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) ^ 5 * E6Fun (ModularGroup.S • w)
              * (E4Fun (imagAxis s hs)) ^ 2
              * (E4Fun (imagAxis s hs) - (E2Fun (imagAxis s hs)) ^ 2) with hB
    set C : ℂ := ((E4Fun (imagAxis s hs)) ^ 2 - E6Fun (imagAxis s hs) * E2Fun (imagAxis s hs)) *
              (2 * (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) ^ 5
                  * E2Fun (ModularGroup.S • w) * E4Fun (ModularGroup.S • w)
                  * E4Fun (imagAxis s hs)
                - 6 * Complex.I * (((ModularGroup.S • w : UpperHalfPlane)) : ℂ) ^ 4
                  * E4Fun (ModularGroup.S • w) * E4Fun (imagAxis s hs) / (Real.pi : ℂ)) with hC'
    have hA1 : ‖A‖ ≤ K1 * (scale w) ^ 5 * ‖DeltaFun (imagAxis s hs)‖ := hT1
    have hB1 : ‖B‖ ≤ K2 * (scale w) ^ 5 * ‖E4Fun (imagAxis s hs)‖ ^ 2
        * ‖E4Fun (imagAxis s hs) - (E2Fun (imagAxis s hs)) ^ 2‖ := hT2
    have hC1 : ‖C‖ ≤ K3 * (scale w) ^ 5
        * ‖(E4Fun (imagAxis s hs)) ^ 2 - E6Fun (imagAxis s hs) * E2Fun (imagAxis s hs)‖
        * ‖E4Fun (imagAxis s hs)‖ := hT3
    have hA' : ‖A‖ ≤ K1 * (scale w) ^ 5 * (CΔ * (1 + s⁻¹) ^ 12) :=
      le_trans hA1 (mul_le_mul_of_nonneg_left hΔz (mul_nonneg hK1.le (pow_nonneg hsc0 5)))
    have hB' : ‖B‖ ≤ K2 * (scale w) ^ 5 * (C4 ^ 2 * (1 + s⁻¹) ^ 8) * (Cd * (1 + s⁻¹) ^ 4) := by
      refine le_trans hB1 (mul_le_mul ?_ hdz (norm_nonneg _) ?_)
      · exact mul_le_mul_of_nonneg_left hC4z (mul_nonneg hK2.le (pow_nonneg hsc0 5))
      · exact mul_nonneg (mul_nonneg hK2.le (pow_nonneg hsc0 5))
          (mul_nonneg (pow_nonneg hC4.le 2) (pow_nonneg hu0 8))
    have hC'' : ‖C‖ ≤ K3 * (scale w) ^ 5 * (Ce * (1 + s⁻¹) ^ 8) * (C4 * (1 + s⁻¹) ^ 4) := by
      refine le_trans hC1 (mul_le_mul ?_ hE4z (norm_nonneg _) ?_)
      · exact mul_le_mul_of_nonneg_left hez (mul_nonneg hK3.le (pow_nonneg hsc0 5))
      · exact mul_nonneg (mul_nonneg hK3.le (pow_nonneg hsc0 5))
          (mul_nonneg hCe.le (pow_nonneg hu0 8))
    have htri : ‖A + B - C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ := by
      calc ‖A + B - C‖ ≤ ‖A + B‖ + ‖C‖ := norm_sub_le _ _
        _ ≤ (‖A‖ + ‖B‖) + ‖C‖ := add_le_add (norm_add_le A B) le_rfl
        _ = ‖A‖ + ‖B‖ + ‖C‖ := by ring
    calc ‖A + B - C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ := htri
      _ ≤ K1 * (scale w) ^ 5 * (CΔ * (1 + s⁻¹) ^ 12)
          + K2 * (scale w) ^ 5 * (C4 ^ 2 * (1 + s⁻¹) ^ 8) * (Cd * (1 + s⁻¹) ^ 4)
          + K3 * (scale w) ^ 5 * (Ce * (1 + s⁻¹) ^ 8) * (C4 * (1 + s⁻¹) ^ 4) := by
          linarith [hA', hB', hC'']
      _ = (K1 * CΔ + K2 * C4 ^ 2 * Cd + K3 * Ce * C4) * (scale w) ^ 5 * (1 + s⁻¹) ^ 12 := by
          ring
  refine le_trans key ?_
  rw [show (5:ℝ) = ((5:ℕ):ℝ) from by norm_num, show (12:ℝ) = ((12:ℕ):ℝ) from by norm_num,
    Real.rpow_natCast, Real.rpow_natCast]

end Work.Asymptotics
