/-
# Polynomial growth of the CKMRV kernel on the funnel window `1 ≤ t ≤ Im τ - 1`

`Work.Asymptotics.HalfFunnel.KaxisWindowPoly`: for `τ` in the CKMRV fundamental domain `𝒟`
with `Im τ ≥ 2` and `1 ≤ t ≤ Im τ - 1`, the kernel along the contour
`Kaxis (Kfun ℓ d) τ t = K^{(d)}(τ, i t)` is bounded by a polynomial in `scale τ` and `1 + t`.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KMinusFunnelAtoms
import Submission.Work.Asymptotics.Compact.kminus_bracket
import Submission.Work.Asymptotics.Compact.kplus8_tail_core
import Submission.Work.Residues.kpre_inv_axis_bound
import Submission.Work.Asymptotics.E4Fun_upper_half
import Submission.Work.Asymptotics.DeltaFun_imagAxis_lower_sharp
import Submission.Work.Asymptotics.HalfFunnel.funnelPreDeclash
import Submission.Work.Residues.KMinusCuspDefs

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics.HalfFunnel

open Work.Kernels

/-! ## Elementary helpers -/

lemma kwp_qnorm_le_one {τ : ℍ} (h : 1 ≤ τ.im) : ‖qParamFun τ‖ ≤ 1 := by
  rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
  nlinarith [Real.pi_pos, h]

lemma kwp_phiVec_zero (τ : ℍ) : phiVec τ 0 = (τ : ℂ) := rfl
lemma kwp_phiVec_one (τ : ℍ) :
    phiVec τ 1 = (τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ) := rfl
lemma kwp_phiVec_two (τ : ℍ) :
    phiVec τ 2 = (τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ := rfl

lemma kwp_phitVec_zero (z : ℍ) : phitVec z 0 = (z : ℂ) ^ 2 := rfl
lemma kwp_phitVec_one (z : ℍ) : phitVec z 1 = (z : ℂ) ^ 2 * E2S z := rfl
lemma kwp_phitVec_two (z : ℍ) : phitVec z 2 = (z : ℂ) ^ 2 * (E2S z) ^ 2 := rfl

lemma kwp_fk14 (τ : ℍ) : fk 14 τ = E14Fun τ := by simp [fk]
lemma kwp_fk12 (τ : ℍ) : fk 12 τ = DeltaFun τ := by simp [fk]
lemma kwp_fk10 (τ : ℍ) : fk 10 τ = E10Fun τ := by simp [fk]
lemma kwp_fk4 (τ : ℍ) : fk 4 τ = E4Fun τ := by simp [fk]
lemma kwp_fk2 (τ : ℍ) : fk 2 τ = E14Fun τ / DeltaFun τ := by simp [fk]
lemma kwp_fk0 (τ : ℍ) : fk 0 τ = 1 := by simp [fk]

lemma kwp_imagAxis_im (t : ℝ) (ht : 0 < t) : (imagAxis t ht).im = t := by
  simp [Work.Kernels.imagAxis]

lemma kwp_imagAxis_norm (t : ℝ) (ht : 0 < t) : ‖((imagAxis t ht : ℍ) : ℂ)‖ = t := by
  show ‖(t : ℂ) * Complex.I‖ = t
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]

lemma kwp_one_le_scale (τ : ℍ) : (1 : ℝ) ≤ scale τ := Work.Kernels.one_le_scale τ

lemma kwp_norm_le_scale (τ : ℍ) : ‖(τ : ℂ)‖ ≤ scale τ := Work.Kernels.coe_norm_le_scale τ

lemma kwp_scale_nonneg (τ : ℍ) : 0 ≤ scale τ := le_trans zero_le_one (kwp_one_le_scale τ)

lemma kwp_scale_rpow_nonneg (τ : ℍ) (N : ℝ) : 0 ≤ (scale τ) ^ N :=
  Real.rpow_nonneg (kwp_scale_nonneg τ) N

lemma kwp_one_le_scale_rpow (τ : ℍ) {N : ℝ} (hN : 0 ≤ N) : 1 ≤ (scale τ) ^ N :=
  Real.one_le_rpow (kwp_one_le_scale τ) hN

lemma kwp_scale_mono (τ : ℍ) {n m : ℝ} (h : n ≤ m) : (scale τ) ^ n ≤ (scale τ) ^ m :=
  Real.rpow_le_rpow_of_exponent_le (kwp_one_le_scale τ) h

lemma kwp_expt_le_one {a b : ℝ} (h : b ≤ a) : Real.exp (-a) * Real.exp b ≤ 1 := by
  rw [← Real.exp_add, Real.exp_le_one_iff]; linarith

lemma kwp_sub_one_two {x : ℂ} {B : ℝ} (hB : ‖x‖ ≤ B) :
    ‖x ^ 2 - 1‖ ≤ ‖x - 1‖ * (B + 1) := by
  have hsplit : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
  rw [hsplit, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖x + 1‖ ≤ ‖x‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ = ‖x‖ + 1 := by rw [norm_one]
    _ ≤ B + 1 := by linarith

lemma kwp_sub_one_three {x : ℂ} {B : ℝ} (hB : ‖x‖ ≤ B) :
    ‖x ^ 3 - 1‖ ≤ ‖x - 1‖ * (B ^ 2 + B + 1) := by
  have hsplit : x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) := by ring
  have hb : ‖x ^ 2 + x + 1‖ ≤ B ^ 2 + B + 1 := by
    have h1 : ‖x ^ 2 + x + 1‖ ≤ ‖x ^ 2 + x‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    rw [norm_one] at h1
    have h2 : ‖x ^ 2 + x‖ ≤ ‖x ^ 2‖ + ‖x‖ := norm_add_le _ _
    have h3 : ‖x ^ 2‖ = ‖x‖ ^ 2 := norm_pow x 2
    have h4 : ‖x‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hB 2
    linarith
  rw [hsplit, norm_mul]
  exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

/-! ## The cusp expansions of the modular forms -/

lemma kwp_E2_sub_one : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
    ‖E2Fun τ - 1‖ ≤ C * ‖qParamFun τ‖ := by
  obtain ⟨C, _, h⟩ := Work.Asymptotics.E2Fun_two_term
  refine ⟨C + 24, by positivity, fun τ hτ => ?_⟩
  have hq := kwp_qnorm_le_one hτ
  have hq0 : (0:ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
  have hq2 : ‖qParamFun τ‖ ^ 2 ≤ ‖qParamFun τ‖ := by nlinarith
  have h1 := h τ hτ
  have h24 : ‖(24:ℂ) * qParamFun τ‖ = 24 * ‖qParamFun τ‖ := by rw [norm_mul, Complex.norm_ofNat]
  have hsplit : E2Fun τ - 1 = (E2Fun τ - 1 + 24 * qParamFun τ) - 24 * qParamFun τ := by ring
  rw [hsplit]
  calc ‖(E2Fun τ - 1 + 24 * qParamFun τ) - 24 * qParamFun τ‖
      ≤ ‖E2Fun τ - 1 + 24 * qParamFun τ‖ + ‖(24:ℂ) * qParamFun τ‖ := norm_sub_le _ _
    _ ≤ C * ‖qParamFun τ‖ ^ 2 + 24 * ‖qParamFun τ‖ := by rw [h24]; exact add_le_add h1 le_rfl
    _ ≤ (C + 24) * ‖qParamFun τ‖ := by nlinarith

lemma kwp_E4_sub_one : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
    ‖E4Fun τ - 1‖ ≤ C * ‖qParamFun τ‖ := by
  obtain ⟨C, _, h⟩ := Work.Asymptotics.E4Fun_two_term
  refine ⟨C + 240, by positivity, fun τ hτ => ?_⟩
  have hq := kwp_qnorm_le_one hτ
  have hq0 : (0:ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
  have hq2 : ‖qParamFun τ‖ ^ 2 ≤ ‖qParamFun τ‖ := by nlinarith
  have h1 := h τ hτ
  have h240 : ‖(240:ℂ) * qParamFun τ‖ = 240 * ‖qParamFun τ‖ := by rw [norm_mul, Complex.norm_ofNat]
  have hsplit : E4Fun τ - 1 = (E4Fun τ - 1 - 240 * qParamFun τ) + 240 * qParamFun τ := by ring
  rw [hsplit]
  calc ‖(E4Fun τ - 1 - 240 * qParamFun τ) + 240 * qParamFun τ‖
      ≤ ‖E4Fun τ - 1 - 240 * qParamFun τ‖ + ‖(240:ℂ) * qParamFun τ‖ := norm_add_le _ _
    _ ≤ C * ‖qParamFun τ‖ ^ 2 + 240 * ‖qParamFun τ‖ := by rw [h240]; exact add_le_add h1 le_rfl
    _ ≤ (C + 240) * ‖qParamFun τ‖ := by nlinarith

lemma kwp_E6_sub_one : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
    ‖E6Fun τ - 1‖ ≤ C * ‖qParamFun τ‖ := by
  obtain ⟨C, _, h⟩ := Work.Asymptotics.E6Fun_two_term
  refine ⟨C + 504, by positivity, fun τ hτ => ?_⟩
  have hq := kwp_qnorm_le_one hτ
  have hq0 : (0:ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
  have hq2 : ‖qParamFun τ‖ ^ 2 ≤ ‖qParamFun τ‖ := by nlinarith
  have h1 := h τ hτ
  have h504 : ‖(504:ℂ) * qParamFun τ‖ = 504 * ‖qParamFun τ‖ := by rw [norm_mul, Complex.norm_ofNat]
  have hsplit : E6Fun τ - 1 = (E6Fun τ - 1 + 504 * qParamFun τ) - 504 * qParamFun τ := by ring
  rw [hsplit]
  calc ‖(E6Fun τ - 1 + 504 * qParamFun τ) - 504 * qParamFun τ‖
      ≤ ‖E6Fun τ - 1 + 504 * qParamFun τ‖ + ‖(504:ℂ) * qParamFun τ‖ := norm_sub_le _ _
    _ ≤ C * ‖qParamFun τ‖ ^ 2 + 504 * ‖qParamFun τ‖ := by rw [h504]; exact add_le_add h1 le_rfl
    _ ≤ (C + 504) * ‖qParamFun τ‖ := by nlinarith

lemma kwp_E2_sq_sub_one : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
    ‖E2Fun τ ^ 2 - 1‖ ≤ C * ‖qParamFun τ‖ := by
  obtain ⟨C2, hC2, h2⟩ := kwp_E2_sub_one
  obtain ⟨CE2, hCE2, hE2⟩ := Work.Asymptotics.E2Fun_bound
  refine ⟨C2 * (CE2 + 1), by positivity, fun τ hτ => ?_⟩
  have hq0 : (0:ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
  have hB := hE2 τ hτ
  have hB0 : (0:ℝ) ≤ CE2 + 1 := by linarith [le_trans (norm_nonneg _) hB]
  calc ‖E2Fun τ ^ 2 - 1‖ ≤ ‖E2Fun τ - 1‖ * (CE2 + 1) := kwp_sub_one_two hB
    _ ≤ (C2 * ‖qParamFun τ‖) * (CE2 + 1) := mul_le_mul_of_nonneg_right (h2 τ hτ) hB0
    _ = (C2 * (CE2 + 1)) * ‖qParamFun τ‖ := by ring

lemma kwp_E4_cube_sub_one : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
    ‖E4Fun τ ^ 3 - 1‖ ≤ C * ‖qParamFun τ‖ := by
  obtain ⟨C4, hC4, h4⟩ := kwp_E4_sub_one
  obtain ⟨CE4, hCE4, hE4⟩ := Work.Asymptotics.E4Fun_bound
  refine ⟨C4 * (CE4 ^ 2 + CE4 + 1), by positivity, fun τ hτ => ?_⟩
  have hq0 : (0:ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
  have hB := hE4 τ hτ
  have hB0 : (0:ℝ) ≤ CE4 ^ 2 + CE4 + 1 := by positivity
  calc ‖E4Fun τ ^ 3 - 1‖ ≤ ‖E4Fun τ - 1‖ * (CE4 ^ 2 + CE4 + 1) := kwp_sub_one_three hB
    _ ≤ (C4 * ‖qParamFun τ‖) * (CE4 ^ 2 + CE4 + 1) := mul_le_mul_of_nonneg_right (h4 τ hτ) hB0
    _ = (C4 * (CE4 ^ 2 + CE4 + 1)) * ‖qParamFun τ‖ := by ring

lemma kwp_E10_sub_one : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
    ‖E10Fun τ - 1‖ ≤ C * ‖qParamFun τ‖ := by
  obtain ⟨C4, hC4, h4⟩ := kwp_E4_sub_one
  obtain ⟨C6, hC6, h6⟩ := kwp_E6_sub_one
  obtain ⟨CE4, hCE4, hE4⟩ := Work.Asymptotics.E4Fun_bound
  refine ⟨C4 + CE4 * C6, by positivity, fun τ hτ => ?_⟩
  have hq0 : (0:ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
  have hB := hE4 τ hτ
  have hB0 : (0:ℝ) ≤ CE4 := le_trans (norm_nonneg _) hB
  have h10 : E10Fun τ - 1 = E4Fun τ * (E6Fun τ - 1) + (E4Fun τ - 1) := by
    simp only [E10Fun]; ring
  rw [h10]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖E4Fun τ * (E6Fun τ - 1)‖ ≤ CE4 * (C6 * ‖qParamFun τ‖) := by
    rw [norm_mul]
    exact mul_le_mul hB (h6 τ hτ) (norm_nonneg _) hB0
  have h2 := h4 τ hτ
  calc ‖E4Fun τ * (E6Fun τ - 1)‖ + ‖E4Fun τ - 1‖
      ≤ CE4 * (C6 * ‖qParamFun τ‖) + C4 * ‖qParamFun τ‖ := add_le_add h1 h2
    _ = (C4 + CE4 * C6) * ‖qParamFun τ‖ := by ring

lemma kwp_E14_sub_one : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
    ‖E14Fun τ - 1‖ ≤ C * ‖qParamFun τ‖ := by
  obtain ⟨C4, hC4, h4⟩ := kwp_E4_sub_one
  obtain ⟨C6, hC6, h6⟩ := kwp_E6_sub_one
  obtain ⟨CE4, hCE4, hE4⟩ := Work.Asymptotics.E4Fun_bound
  refine ⟨C4 * (CE4 + 1) + CE4 ^ 2 * C6, by positivity, fun τ hτ => ?_⟩
  have hq0 : (0:ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
  have hB := hE4 τ hτ
  have hB0 : (0:ℝ) ≤ CE4 := le_trans (norm_nonneg _) hB
  have hB1 : (0:ℝ) ≤ CE4 + 1 := by linarith
  have h14 : E14Fun τ - 1 = E4Fun τ ^ 2 * (E6Fun τ - 1) + (E4Fun τ ^ 2 - 1) := by
    simp only [E14Fun]; ring
  rw [h14]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖E4Fun τ ^ 2 * (E6Fun τ - 1)‖ ≤ CE4 ^ 2 * (C6 * ‖qParamFun τ‖) := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hB 2) (h6 τ hτ) (norm_nonneg _) (by positivity)
  have h2 : ‖E4Fun τ ^ 2 - 1‖ ≤ (C4 * (CE4 + 1)) * ‖qParamFun τ‖ := by
    calc ‖E4Fun τ ^ 2 - 1‖ ≤ ‖E4Fun τ - 1‖ * (CE4 + 1) := kwp_sub_one_two hB
      _ ≤ (C4 * ‖qParamFun τ‖) * (CE4 + 1) := mul_le_mul_of_nonneg_right (h4 τ hτ) hB1
      _ = (C4 * (CE4 + 1)) * ‖qParamFun τ‖ := by ring
  calc ‖E4Fun τ ^ 2 * (E6Fun τ - 1)‖ + ‖E4Fun τ ^ 2 - 1‖
      ≤ CE4 ^ 2 * (C6 * ‖qParamFun τ‖) + (C4 * (CE4 + 1)) * ‖qParamFun τ‖ := add_le_add h1 h2
    _ = (C4 * (CE4 + 1) + CE4 ^ 2 * C6) * ‖qParamFun τ‖ := by ring

/-! ## The cancellation bound for `6φ₀E₁₄ - 12φ₁E₄³ + 6φ₂E₁₀` -/

lemma kwp_R_id (τ : ℍ) :
    (6 : ℂ) * (τ : ℂ) * E14Fun τ - (12 : ℂ) * phiVec τ 1 * E4Fun τ ^ 3
        + (6 : ℂ) * phiVec τ 2 * E10Fun τ
      = 6 * (τ : ℂ) * (E14Fun τ - 1)
        - 12 * (((τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 3 - 1)
            + (τ : ℂ) * (E2Fun τ - 1))
        + 6 * (((τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ) * (E10Fun τ - 1)
            + (τ : ℂ) * (E2Fun τ ^ 2 - 1) - (6 * Complex.I / (Real.pi : ℂ)) * (E2Fun τ - 1)) := by
  rw [kwp_phiVec_one, kwp_phiVec_two]
  ring

/-- `‖τE₂ - 3i/π‖ ≤ CE2‖τ‖ + 3` when `‖E₂‖ ≤ CE2`. -/
lemma kwp_norm_phi1_bound {τ : ℍ} {CE2 : ℝ} (h : ‖E2Fun τ‖ ≤ CE2) :
    ‖(τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)‖ ≤ CE2 * ‖(τ : ℂ)‖ + 3 := by
  refine le_trans (norm_sub_le ((τ : ℂ) * E2Fun τ) (3 * Complex.I / (Real.pi : ℂ))) ?_
  have h1 : ‖(τ : ℂ) * E2Fun τ‖ ≤ CE2 * ‖(τ : ℂ)‖ := by
    rw [norm_mul]
    calc ‖(τ : ℂ)‖ * ‖E2Fun τ‖ ≤ ‖(τ : ℂ)‖ * CE2 :=
          mul_le_mul_of_nonneg_left h (norm_nonneg (τ : ℂ))
      _ = CE2 * ‖(τ : ℂ)‖ := by ring
  have h2 : ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 3 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [h2]
  have h3 : 3 / Real.pi ≤ 3 := by
    rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
  linarith

/-- `‖τE₂² - (6i/π)E₂‖ ≤ CE2²‖τ‖ + (6/π)CE2` when `‖E₂‖ ≤ CE2`. -/
lemma kwp_norm_phi2_bound {τ : ℍ} {CE2 : ℝ} (h : ‖E2Fun τ‖ ≤ CE2) :
    ‖(τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ‖
      ≤ CE2 ^ 2 * ‖(τ : ℂ)‖ + 6 / Real.pi * CE2 := by
  refine le_trans (norm_sub_le ((τ : ℂ) * E2Fun τ ^ 2) ((6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ)) ?_
  have h1 : ‖(τ : ℂ) * E2Fun τ ^ 2‖ ≤ CE2 ^ 2 * ‖(τ : ℂ)‖ := by
    rw [norm_mul, norm_pow]
    calc ‖(τ : ℂ)‖ * ‖E2Fun τ‖ ^ 2 ≤ ‖(τ : ℂ)‖ * CE2 ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg (E2Fun τ)) h 2)
            (norm_nonneg (τ : ℂ))
      _ = CE2 ^ 2 * ‖(τ : ℂ)‖ := by ring
  have h2 : ‖(6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ‖ = 6 / Real.pi * ‖E2Fun τ‖ := by
    rw [norm_mul, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [h2]
  have h3 : (0:ℝ) ≤ 6 / Real.pi := by positivity
  have h4 : 6 / Real.pi * ‖E2Fun τ‖ ≤ 6 / Real.pi * CE2 := mul_le_mul_of_nonneg_left h h3
  linarith

/-- Generic arithmetic step: `(a‖τ‖+b)(c q) ≤ (a+b)c (1+‖τ‖)q` for nonnegative data. -/
lemma kwp_term_le {N q a b c : ℝ} (hN : 0 ≤ N) (hq : 0 ≤ q) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) : (a * N + b) * (c * q) ≤ (a + b) * c * ((1 + N) * q) := by
  have h1 : a * N + b ≤ (a + b) * (1 + N) := by nlinarith
  calc (a * N + b) * (c * q) ≤ ((a + b) * (1 + N)) * (c * q) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hc hq)
    _ = (a + b) * c * ((1 + N) * q) := by ring

/-- Arithmetic: `‖τ‖(b q) ≤ b (1+‖τ‖)q` for nonnegative `b`. -/
lemma kwp_term_le' {N q b : ℝ} (hN : 0 ≤ N) (hq : 0 ≤ q) (hb : 0 ≤ b) :
    N * (b * q) ≤ b * ((1 + N) * q) := by
  have h1 : N * b ≤ b * (1 + N) := by nlinarith [mul_nonneg hb hN]
  calc N * (b * q) = (N * b) * q := by ring
    _ ≤ (b * (1 + N)) * q := mul_le_mul_of_nonneg_right h1 hq
    _ = b * ((1 + N) * q) := by ring

lemma kwp_R_bound : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ →
    ‖(6 : ℂ) * (τ : ℂ) * E14Fun τ - (12 : ℂ) * phiVec τ 1 * E4Fun τ ^ 3
        + (6 : ℂ) * phiVec τ 2 * E10Fun τ‖
      ≤ C * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := by
  obtain ⟨C14, hC14, h14⟩ := kwp_E14_sub_one
  obtain ⟨C43, hC43, h43⟩ := kwp_E4_cube_sub_one
  obtain ⟨C10, hC10, h10⟩ := kwp_E10_sub_one
  obtain ⟨C2, hC2, h2⟩ := kwp_E2_sub_one
  obtain ⟨C22, hC22, h22⟩ := kwp_E2_sq_sub_one
  obtain ⟨CE2, hCE2, hE2⟩ := Work.Asymptotics.E2Fun_bound
  refine ⟨6 * C14 + 12 * ((CE2 + 3) * C43 + C2)
      + 6 * ((CE2 ^ 2 + 6 / Real.pi * CE2) * C10 + C22 + 6 / Real.pi * C2) + 1,
    by positivity, fun τ hF => ?_⟩
  have hτ1 : 1 ≤ τ.im := le_trans (by norm_num) hF.2
  have hq0 : (0:ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
  have hN0 : (0:ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
  have hE2b := hE2 τ hτ1
  have hCE2n : (0:ℝ) ≤ CE2 := le_trans (norm_nonneg _) hE2b
  have hE14' := h14 τ hτ1
  have hE43' := h43 τ hτ1
  have hE10' := h10 τ hτ1
  have hE2' := h2 τ hτ1
  have hE22' := h22 τ hτ1
  have hp1 := kwp_norm_phi1_bound hE2b
  have hp2 := kwp_norm_phi2_bound hE2b
  have hT1 : ‖(6 : ℂ) * (τ : ℂ) * (E14Fun τ - 1)‖ ≤ 6 * C14 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := by
    have hsplit : (6 : ℂ) * (τ : ℂ) * (E14Fun τ - 1) = (6 : ℂ) * ((τ : ℂ) * (E14Fun τ - 1)) := by ring
    rw [hsplit, norm_mul, Complex.norm_ofNat]
    have hτe : ‖(τ : ℂ) * (E14Fun τ - 1)‖ ≤ C14 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := by
      rw [norm_mul]
      refine le_trans (mul_le_mul_of_nonneg_left hE14' hN0) ?_
      exact kwp_term_le' hN0 hq0 hC14.le
    calc 6 * ‖(τ : ℂ) * (E14Fun τ - 1)‖ ≤ 6 * (C14 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖)) := by linarith
      _ = 6 * C14 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := by ring
  have hT2 : ‖(12 : ℂ) * (((τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 3 - 1)
      + (τ : ℂ) * (E2Fun τ - 1))‖
      ≤ 12 * ((CE2 + 3) * C43 + C2) * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := by
    rw [norm_mul, Complex.norm_ofNat]
    have hinner : ‖((τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 3 - 1)
        + (τ : ℂ) * (E2Fun τ - 1)‖
        ≤ ((CE2 + 3) * C43 + C2) * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := by
      have hA1 : ‖((τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 3 - 1)‖
          ≤ (CE2 * ‖(τ : ℂ)‖ + 3) * (C43 * ‖qParamFun τ‖) := by
        rw [norm_mul]
        exact mul_le_mul hp1 hE43' (norm_nonneg _) (by positivity)
      have hA2 : (CE2 * ‖(τ : ℂ)‖ + 3) * (C43 * ‖qParamFun τ‖)
          ≤ (CE2 + 3) * C43 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) :=
        kwp_term_le hN0 hq0 hCE2n (by norm_num) hC43.le
      have hB1 : ‖(τ : ℂ) * (E2Fun τ - 1)‖ ≤ C2 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := by
        rw [norm_mul]
        refine le_trans (mul_le_mul_of_nonneg_left hE2' hN0) ?_
        exact kwp_term_le' hN0 hq0 hC2.le
      have hsum : ((CE2 + 3) * C43 + C2) * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖)
          = (CE2 + 3) * C43 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖)
            + C2 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := by ring
      have htri : ‖((τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 3 - 1)
              + (τ : ℂ) * (E2Fun τ - 1)‖
          ≤ ‖((τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 3 - 1)‖
            + ‖(τ : ℂ) * (E2Fun τ - 1)‖ :=
        norm_add_le _ _
      rw [hsum]
      linarith [htri, hA1, hA2, hB1]
    linarith
  have hT3 : ‖(6 : ℂ) * (((τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ) * (E10Fun τ - 1)
      + (τ : ℂ) * (E2Fun τ ^ 2 - 1) - (6 * Complex.I / (Real.pi : ℂ)) * (E2Fun τ - 1))‖
      ≤ 6 * ((CE2 ^ 2 + 6 / Real.pi * CE2) * C10 + C22 + 6 / Real.pi * C2)
        * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := by
    rw [norm_mul, Complex.norm_ofNat]
    have hinner : ‖((τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ) * (E10Fun τ - 1)
        + (τ : ℂ) * (E2Fun τ ^ 2 - 1) - (6 * Complex.I / (Real.pi : ℂ)) * (E2Fun τ - 1)‖
        ≤ ((CE2 ^ 2 + 6 / Real.pi * CE2) * C10 + C22 + 6 / Real.pi * C2)
          * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := by
      have hA1 : ‖((τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ) * (E10Fun τ - 1)‖
          ≤ (CE2 ^ 2 * ‖(τ : ℂ)‖ + 6 / Real.pi * CE2) * (C10 * ‖qParamFun τ‖) := by
        rw [norm_mul]
        exact mul_le_mul hp2 hE10' (norm_nonneg _) (by positivity)
      have hA2 : (CE2 ^ 2 * ‖(τ : ℂ)‖ + 6 / Real.pi * CE2) * (C10 * ‖qParamFun τ‖)
          ≤ (CE2 ^ 2 + 6 / Real.pi * CE2) * C10 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) :=
        kwp_term_le hN0 hq0 (by positivity) (by positivity) hC10.le
      have hB1 : ‖(τ : ℂ) * (E2Fun τ ^ 2 - 1)‖ ≤ C22 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := by
        rw [norm_mul]
        refine le_trans (mul_le_mul_of_nonneg_left hE22' hN0) ?_
        exact kwp_term_le' hN0 hq0 hC22.le
      have hC1 : ‖(6 * Complex.I / (Real.pi : ℂ)) * (E2Fun τ - 1)‖
          ≤ 6 / Real.pi * (C2 * ‖qParamFun τ‖) := by
        rw [norm_mul, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        have h6 : (0:ℝ) ≤ 6 / Real.pi := by positivity
        exact mul_le_mul_of_nonneg_left hE2' h6
      have hC2' : 6 / Real.pi * (C2 * ‖qParamFun τ‖)
          ≤ 6 / Real.pi * C2 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := by
        have h6 : (0:ℝ) ≤ 6 / Real.pi := by positivity
        have h11 : ‖qParamFun τ‖ ≤ (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := by
          have h12 : (1:ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith
          calc ‖qParamFun τ‖ = 1 * ‖qParamFun τ‖ := by ring
            _ ≤ (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := mul_le_mul_of_nonneg_right h12 hq0
        have h13 := mul_le_mul_of_nonneg_left h11 (mul_nonneg h6 hC2.le)
        calc 6 / Real.pi * (C2 * ‖qParamFun τ‖) = (6 / Real.pi * C2) * ‖qParamFun τ‖ := by ring
          _ ≤ (6 / Real.pi * C2) * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := h13
          _ = 6 / Real.pi * C2 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := by ring
      have hassoc : ((τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ) * (E10Fun τ - 1)
          + (τ : ℂ) * (E2Fun τ ^ 2 - 1) - (6 * Complex.I / (Real.pi : ℂ)) * (E2Fun τ - 1)
          = (((τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ) * (E10Fun τ - 1)
              + (τ : ℂ) * (E2Fun τ ^ 2 - 1)) - (6 * Complex.I / (Real.pi : ℂ)) * (E2Fun τ - 1) := by ring
      have hsum : ((CE2 ^ 2 + 6 / Real.pi * CE2) * C10 + C22 + 6 / Real.pi * C2)
            * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖)
          = (CE2 ^ 2 + 6 / Real.pi * CE2) * C10 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖)
            + C22 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖)
            + 6 / Real.pi * C2 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := by ring
      rw [hassoc]
      rw [hsum]
      have hsub := norm_sub_le (((τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ) * (E10Fun τ - 1)
              + (τ : ℂ) * (E2Fun τ ^ 2 - 1)) ((6 * Complex.I / (Real.pi : ℂ)) * (E2Fun τ - 1))
      have hab : ‖((τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ) * (E10Fun τ - 1)
          + (τ : ℂ) * (E2Fun τ ^ 2 - 1)‖
          ≤ (CE2 ^ 2 + 6 / Real.pi * CE2) * C10 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖)
            + C22 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) :=
        le_trans (norm_add_le _ _) (add_le_add (le_trans hA1 hA2) hB1)
      linarith [hsub, hab, le_trans hC1 hC2']
    linarith
  rw [kwp_R_id]
  have hsplit1 : ‖(6 : ℂ) * (τ : ℂ) * (E14Fun τ - 1)
      - 12 * (((τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 3 - 1)
          + (τ : ℂ) * (E2Fun τ - 1))‖
      ≤ ‖(6 : ℂ) * (τ : ℂ) * (E14Fun τ - 1)‖
        + ‖(12 : ℂ) * (((τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 3 - 1)
            + (τ : ℂ) * (E2Fun τ - 1))‖ :=
    norm_sub_le _ _
  have hsplit2 : ‖(6 : ℂ) * (τ : ℂ) * (E14Fun τ - 1)
        - 12 * (((τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 3 - 1)
            + (τ : ℂ) * (E2Fun τ - 1))
        + 6 * (((τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ) * (E10Fun τ - 1)
            + (τ : ℂ) * (E2Fun τ ^ 2 - 1) - (6 * Complex.I / (Real.pi : ℂ)) * (E2Fun τ - 1))‖
      ≤ ‖(6 : ℂ) * (τ : ℂ) * (E14Fun τ - 1)
          - 12 * (((τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 3 - 1)
              + (τ : ℂ) * (E2Fun τ - 1))‖
        + ‖(6 : ℂ) * (((τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ) * (E10Fun τ - 1)
            + (τ : ℂ) * (E2Fun τ ^ 2 - 1) - (6 * Complex.I / (Real.pi : ℂ)) * (E2Fun τ - 1))‖ :=
    norm_add_le _ _
  have hq11 : (0:ℝ) ≤ (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := by positivity
  have hcombine : 6 * C14 * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖)
      + 12 * ((CE2 + 3) * C43 + C2) * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖)
      + 6 * ((CE2 ^ 2 + 6 / Real.pi * CE2) * C10 + C22 + 6 / Real.pi * C2)
          * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖)
      = (6 * C14 + 12 * ((CE2 + 3) * C43 + C2)
          + 6 * ((CE2 ^ 2 + 6 / Real.pi * CE2) * C10 + C22 + 6 / Real.pi * C2))
        * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := by ring
  have hstep : ‖(6 : ℂ) * (τ : ℂ) * (E14Fun τ - 1)
        - 12 * (((τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 3 - 1)
            + (τ : ℂ) * (E2Fun τ - 1))
        + 6 * (((τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ) * (E10Fun τ - 1)
            + (τ : ℂ) * (E2Fun τ ^ 2 - 1) - (6 * Complex.I / (Real.pi : ℂ)) * (E2Fun τ - 1))‖
      ≤ (6 * C14 + 12 * ((CE2 + 3) * C43 + C2)
          + 6 * ((CE2 ^ 2 + 6 / Real.pi * CE2) * C10 + C22 + 6 / Real.pi * C2))
        * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := by
    rw [← hcombine]
    linarith [hsplit2, hsplit1, hT1, hT2, hT3]
  calc ‖(6 : ℂ) * (τ : ℂ) * (E14Fun τ - 1)
        - 12 * (((τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 3 - 1)
            + (τ : ℂ) * (E2Fun τ - 1))
        + 6 * (((τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ) * (E10Fun τ - 1)
            + (τ : ℂ) * (E2Fun τ ^ 2 - 1) - (6 * Complex.I / (Real.pi : ℂ)) * (E2Fun τ - 1))‖
      ≤ (6 * C14 + 12 * ((CE2 + 3) * C43 + C2)
          + 6 * ((CE2 ^ 2 + 6 / Real.pi * CE2) * C10 + C22 + 6 / Real.pi * C2))
        * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := hstep
    _ ≤ (6 * C14 + 12 * ((CE2 + 3) * C43 + C2)
          + 6 * ((CE2 ^ 2 + 6 / Real.pi * CE2) * C10 + C22 + 6 / Real.pi * C2) + 1)
        * ((1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num)) hq11
    _ = (6 * C14 + 12 * ((CE2 + 3) * C43 + C2)
          + 6 * ((CE2 ^ 2 + 6 / Real.pi * CE2) * C10 + C22 + 6 / Real.pi * C2) + 1)
        * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := by ring

/-! ## The expansion of `K_+^{(24)}` -/

/-- The middle matrix of `Υ_+^{(24)}` with `(j(τ)-j(z))⁻¹` left uncovered. -/
lemma kwp_v14_0 : (![14, 12, 10] : Fin 3 → ℤ) 0 = 14 := rfl
lemma kwp_v14_1 : (![14, 12, 10] : Fin 3 → ℤ) 1 = 12 := rfl
lemma kwp_v14_2 : (![14, 12, 10] : Fin 3 → ℤ) 2 = 10 := rfl
lemma kwp_w42_0 : (![4, 2, 0] : Fin 3 → ℤ) 0 = 4 := rfl
lemma kwp_w42_1 : (![4, 2, 0] : Fin 3 → ℤ) 1 = 2 := rfl
lemma kwp_w42_2 : (![4, 2, 0] : Fin 3 → ℤ) 2 = 0 := rfl

def kwpX24 (jτ J : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![6, 0, c1728 * J⁻¹ - 6;
     -12 * jτ + 5 * c1728, -2 * c1728 * J⁻¹, 12 * jτ - 7 * c1728;
     c1728 * J⁻¹ + 6, 0, -6]
lemma kwpX24_00 (a b : ℂ) : kwpX24 a b 0 0 = 6 := by simp [kwpX24]
lemma kwpX24_01 (a b : ℂ) : kwpX24 a b 0 1 = 0 := by simp [kwpX24]
lemma kwpX24_02 (a b : ℂ) : kwpX24 a b 0 2 = c1728 * b⁻¹ - 6 := by simp [kwpX24]
lemma kwpX24_10 (a b : ℂ) : kwpX24 a b 1 0 = -12 * a + 5 * c1728 := by simp [kwpX24]
lemma kwpX24_11 (a b : ℂ) : kwpX24 a b 1 1 = -2 * c1728 * b⁻¹ := by simp [kwpX24]
lemma kwpX24_12 (a b : ℂ) : kwpX24 a b 1 2 = 12 * a - 7 * c1728 := by simp [kwpX24]
lemma kwpX24_20 (a b : ℂ) : kwpX24 a b 2 0 = c1728 * b⁻¹ + 6 := by simp [kwpX24]
lemma kwpX24_21 (a b : ℂ) : kwpX24 a b 2 1 = 0 := by simp [kwpX24]
lemma kwpX24_22 (a b : ℂ) : kwpX24 a b 2 2 = -6 := by simp [kwpX24]
lemma kwp_ups24_eq (τ z : ℍ) :
    UpsilonPlus 24 τ z =
      ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * DeltaFun z)⁻¹ •
        (PiMat (![14, 12, 10] : Fin 3 → ℤ) τ
          * kwpX24 (jInvariantFun τ) (jInvariantFun τ - jInvariantFun z)
          * PiMat (![4, 2, 0] : Fin 3 → ℤ) z) := rfl
lemma kwp_PiMat_mul_entry (a b : Fin 3 → ℤ) (M : Matrix (Fin 3) (Fin 3) ℂ) (x y : ℍ) (i j : Fin 3) :
    (PiMat a x * M * PiMat b y) i j = fk (a i) x * M i j * fk (b j) y := by
  simp only [PiMat]
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring
lemma kwp_ups24_entry (τ z : ℍ) (i j : Fin 3) :
    UpsilonPlus 24 τ z i j =
      ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * DeltaFun z)⁻¹ *
        (fk ((![14, 12, 10] : Fin 3 → ℤ) i) τ
          * kwpX24 (jInvariantFun τ) (jInvariantFun τ - jInvariantFun z) i j
          * fk ((![4, 2, 0] : Fin 3 → ℤ) j) z) := by
  rw [kwp_ups24_eq, Matrix.smul_apply, smul_eq_mul, kwp_PiMat_mul_entry]
def kwpY0 (τ z : ℍ) : ℂ :=
  6 * phiVec τ 0 * E14Fun τ
    + phiVec τ 1 * DeltaFun τ * (-12 * jInvariantFun τ + 8640)
    + phiVec τ 2 * E10Fun τ * (c1728 * (jInvariantFun τ - jInvariantFun z)⁻¹ + 6)
def kwpY1 (τ z : ℍ) : ℂ :=
  phiVec τ 1 * DeltaFun τ * (-3456 * (jInvariantFun τ - jInvariantFun z)⁻¹)
def kwpY2 (τ z : ℍ) : ℂ :=
  phiVec τ 0 * E14Fun τ * (c1728 * (jInvariantFun τ - jInvariantFun z)⁻¹ - 6)
    + phiVec τ 1 * DeltaFun τ * (12 * jInvariantFun τ - 12096)
    + phiVec τ 2 * E10Fun τ * (-6)
lemma phidelta1 (τ : ℍ) :
    phiVec τ 1 * DeltaFun τ * (-12 * jInvariantFun τ + 8640)
      = -12 * (phiVec τ 1 * E4Fun τ ^ 3) + 8640 * (phiVec τ 1 * DeltaFun τ) := by
  linear_combination (-12 * phiVec τ 1) * (Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ)
lemma phidelta2 (τ : ℍ) :
    phiVec τ 1 * DeltaFun τ * (12 * jInvariantFun τ - 12096)
      = 12 * (phiVec τ 1 * E4Fun τ ^ 3) - 12096 * (phiVec τ 1 * DeltaFun τ) := by
  linear_combination (12 * phiVec τ 1) * (Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ)
lemma kwpY0_eq (τ z : ℍ) :
    kwpY0 τ z
      = ((6 : ℂ) * (τ : ℂ) * E14Fun τ - 12 * phiVec τ 1 * E4Fun τ ^ 3
          + 6 * phiVec τ 2 * E10Fun τ)
        + (8640 * phiVec τ 1 * DeltaFun τ
            + 1728 * phiVec τ 2 * E10Fun τ * (jInvariantFun τ - jInvariantFun z)⁻¹) := by
  set W : ℂ := (jInvariantFun τ - jInvariantFun z)⁻¹ with hW
  simp only [c1728, kwpY0, kwp_phiVec_zero, ← hW]
  rw [phidelta1 τ]
  ring
lemma kwpY2_eq (τ z : ℍ) :
    kwpY2 τ z
      = -((6 : ℂ) * (τ : ℂ) * E14Fun τ - 12 * phiVec τ 1 * E4Fun τ ^ 3
          + 6 * phiVec τ 2 * E10Fun τ)
        + (1728 * phiVec τ 0 * E14Fun τ * (jInvariantFun τ - jInvariantFun z)⁻¹
            - 12096 * phiVec τ 1 * DeltaFun τ) := by
  set W : ℂ := (jInvariantFun τ - jInvariantFun z)⁻¹ with hW
  simp only [c1728, kwpY2, kwp_phiVec_zero, ← hW]
  rw [phidelta2 τ]
  ring
lemma kwpY1_eq (τ z : ℍ) :
    kwpY1 τ z = -3456 * phiVec τ 1 * DeltaFun τ * (jInvariantFun τ - jInvariantFun z)⁻¹ := by
  simp only [kwpY1]; ring
lemma kwp_KPlus_entry (τ z : ℍ) (i j : Fin 3) :
    phiVec τ i * UpsilonPlus 24 τ z i j * phitVec z j
      = ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * DeltaFun z)⁻¹ *
        (phiVec τ i * (fk ((![14, 12, 10] : Fin 3 → ℤ) i) τ
          * kwpX24 (jInvariantFun τ) (jInvariantFun τ - jInvariantFun z) i j
          * fk ((![4, 2, 0] : Fin 3 → ℤ) j) z) * phitVec z j) := by
  rw [kwp_ups24_entry]
  ring_nf
lemma kwp_KPlus_sum (τ z : ℍ) :
    (∑ i : Fin 3, ∑ j : Fin 3, phiVec τ i
        * (fk ((![14, 12, 10] : Fin 3 → ℤ) i) τ
          * kwpX24 (jInvariantFun τ) (jInvariantFun τ - jInvariantFun z) i j
          * fk ((![4, 2, 0] : Fin 3 → ℤ) j) z) * phitVec z j)
      = kwpY0 τ z * (E4Fun z * phitVec z 0)
        + kwpY1 τ z * ((E14Fun z / DeltaFun z) * phitVec z 1)
        + kwpY2 τ z * (phitVec z 2) := by
  set J : ℂ := jInvariantFun τ - jInvariantFun z with hJ
  set jt : ℂ := jInvariantFun τ with hjt
  set jz : ℂ := jInvariantFun z with hjz
  set W : ℂ := (jInvariantFun τ - jInvariantFun z)⁻¹ with hW
  simp only [Fin.sum_univ_three, ← hjt, ← hjz, ← hJ, ← hW]
  simp only [kwp_v14_0, kwp_v14_1, kwp_v14_2, kwp_w42_0, kwp_w42_1, kwp_w42_2, kwp_fk14, kwp_fk12,
    kwp_fk10, kwp_fk4, kwp_fk2, kwp_fk0, kwpX24_00, kwpX24_01, kwpX24_02, kwpX24_10, kwpX24_11,
    kwpX24_12, kwpX24_20, kwpX24_21, kwpX24_22, c1728]
  simp only [kwp_phiVec_zero, kwp_phiVec_one, kwp_phiVec_two, kwp_phitVec_zero, kwp_phitVec_one,
    kwp_phitVec_two, kwpY0, kwpY1, kwpY2, c1728, ← hjt, ← hjz, ← hJ, ← hW]
  ring
lemma kwp_KPlus_eq (τ z : ℍ) :
    KPlus 24 τ z =
      ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * DeltaFun z)⁻¹ *
        (kwpY0 τ z * (E4Fun z * phitVec z 0)
          + kwpY1 τ z * ((E14Fun z / DeltaFun z) * phitVec z 1)
          + kwpY2 τ z * (phitVec z 2)) := by
  have h1 : KPlus 24 τ z =
      ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * DeltaFun z)⁻¹ *
        (∑ i : Fin 3, ∑ j : Fin 3, phiVec τ i * (fk ((![14, 12, 10] : Fin 3 → ℤ) i) τ
          * kwpX24 (jInvariantFun τ) (jInvariantFun τ - jInvariantFun z) i j
          * fk ((![4, 2, 0] : Fin 3 → ℤ) j) z) * phitVec z j) := by
    rw [KPlus]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact kwp_KPlus_entry τ z i j
  rw [h1, kwp_KPlus_sum]


/-! ## Spliced cusp estimates for the imaginary axis -/

lemma kwp_invDelta_z (t : ℝ) (ht : 0 < t) (ht1 : 1 ≤ t) :
    ‖(DeltaFun (imagAxis t ht))⁻¹‖ ≤ 2 * Real.exp (2 * Real.pi * t) := by
  have hlow := Work.Asymptotics.DeltaFun_imagAxis_lower_sharp t ht ht1
  have hb : (0:ℝ) < 2 * Real.exp (2 * Real.pi * t) := by positivity
  have ha : (0:ℝ) < ‖DeltaFun (imagAxis t ht)‖ :=
    norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)
  rw [norm_inv, inv_le_comm₀ ha hb]
  calc (2 * Real.exp (2 * Real.pi * t))⁻¹ = (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * t)) := by
        rw [Real.exp_neg]; field_simp
    _ ≤ ‖DeltaFun (imagAxis t ht)‖ := hlow

lemma kwp_E4_lower (z : ℍ) (hz : 2 ≤ z.im) : (1 / 2 : ℝ) ≤ ‖E4Fun z‖ := by
  have h := Work.FunnelNumerics.E4_sub_one_le z hz
  have h3 := norm_sub_le (E4Fun z) (E4Fun z - 1)
  rw [show E4Fun z - (E4Fun z - 1) = 1 by ring, norm_one] at h3
  linarith

/-- The inverse of the divisor `j(τ) - j(i t)` is bounded by `C q`, `q = e^{-2π Im τ}`. -/
lemma kwp_Jinv_bound (τ : ℍ) (t : ℝ) (ht : 0 < t) (hτ : 2 ≤ τ.im) (ht1 : 1 ≤ t)
    (htle : t ≤ τ.im - 1) :
    ‖(jInvariantFun τ - jInvariantFun (imagAxis t ht))⁻¹‖
      ≤ (1 / 16 - 27 / 4 * Real.exp (-(2 * Real.pi)))⁻¹
          * Real.exp (-(2 * Real.pi * τ.im)) := by
  by_cases hJ0 : jInvariantFun τ - jInvariantFun (imagAxis t ht) = 0
  · rw [hJ0]
    simp only [_root_.inv_zero, norm_zero]
    exact mul_nonneg (le_of_lt (inv_pos.mpr Work.Residues.kpre_axis_const_pos)) (Real.exp_pos _).le
  · rw [norm_inv]
    have hdiff := Work.Residues.jInvariant_axis_diff_lower
      (fun τ hτ => Work.Asymptotics.DeltaFun_upper_sharp τ hτ)
      (fun t ht ht1 => Work.Asymptotics.DeltaFun_imagAxis_lower_sharp t ht ht1)
      (fun z hz => Work.Asymptotics.E4Fun_upper_half z hz)
      (A := 2) (fun z hz => kwp_E4_lower z hz)
    have hτ2 : max 2 1 ≤ τ.im := by rw [max_eq_left (by norm_num)]; exact hτ
    have hlow := hdiff τ t ht hτ2 ht1 htle
    have hb : 0 < (1 / 16 - 27 / 4 * Real.exp (-(2 * Real.pi)))⁻¹
        * Real.exp (-(2 * Real.pi * τ.im)) :=
      mul_pos (inv_pos.mpr Work.Residues.kpre_axis_const_pos) (Real.exp_pos _)
    rw [inv_le_comm₀ (norm_pos_iff.mpr hJ0) hb]
    rw [show ((1 / 16 - 27 / 4 * Real.exp (-(2 * Real.pi)))⁻¹
          * Real.exp (-(2 * Real.pi * τ.im)))⁻¹
        = (1 / 16 - 27 / 4 * Real.exp (-(2 * Real.pi))) * Real.exp (2 * Real.pi * τ.im) from by
      rw [_root_.mul_inv_rev, inv_inv, ← Real.exp_neg]
      ring]
    exact hlow

/-! ## Elementary scale and `𝒫` estimates on the imaginary axis -/

lemma kwp_imagAxis_scale_le (t : ℝ) (ht : 0 < t) (ht1 : 1 ≤ t) :
    scale (imagAxis t ht) ≤ 3 * (1 + t) := by
  have him := kwp_imagAxis_im t ht
  have hnorm := kwp_imagAxis_norm t ht
  have hinv : (t)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ ht]; exact ht1
  rw [Work.Kernels.scale, him, hnorm]
  linarith

lemma kwp_InP_imagAxis {F : ℍ → ℂ} (hF : Work.Kernels.InP F) :
    ∃ A N : ℝ, 0 < A ∧ 0 ≤ N ∧ ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
      ‖F (imagAxis t ht)‖ ≤ A * (1 + t) ^ N := by
  obtain ⟨α, N, hα, hN, hb⟩ := (Work.Kernels.moderateGrowthOn_iff_scale _ _).mp hF.2
  refine ⟨α * 3 ^ N + 1, N, by positivity, hN, fun t ht ht1 => ?_⟩
  have hsc := kwp_imagAxis_scale_le t ht ht1
  have h1 : ‖F (imagAxis t ht)‖ ≤ α * (scale (imagAxis t ht)) ^ N := hb _ (Set.mem_univ _)
  have h2 : (scale (imagAxis t ht)) ^ N ≤ (3 * (1 + t)) ^ N :=
    Real.rpow_le_rpow (Work.Kernels.scale_pos _).le hsc hN
  have h3 : (3 * (1 + t)) ^ N = 3 ^ N * (1 + t) ^ N :=
    Real.mul_rpow (by norm_num) (by linarith)
  have h4 : α * (scale (imagAxis t ht)) ^ N ≤ α * (3 ^ N * (1 + t) ^ N) :=
    mul_le_mul_of_nonneg_left (h2.trans (le_of_eq h3)) hα
  have h6 : (0:ℝ) ≤ (1 + t) ^ N := Real.rpow_nonneg (by linarith) _
  have h5 : α * (3 ^ N * (1 + t) ^ N) ≤ (α * 3 ^ N + 1) * (1 + t) ^ N := by
    nlinarith [h6, hα]
  linarith

open Work.Residues in
/-- `‖j z‖ ≤ C e^{2π Im z}` on the imaginary axis. -/
lemma kwp_jz_imagAxis :
    ∃ CJ : ℝ, 0 < CJ ∧ ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
      ‖jInvariantFun (imagAxis t ht)‖ ≤ CJ * Real.exp (2 * Real.pi * t) := by
  refine ⟨27 / 4 + 1, by norm_num, fun t ht ht1 => ?_⟩
  have hE4 := Work.Asymptotics.E4Fun_upper_half (imagAxis t ht)
    (by rw [kwp_imagAxis_im t ht]; exact ht1)
  have hDinv := kwp_invDelta_z t ht ht1
  rw [norm_inv] at hDinv
  have h1 : ‖E4Fun (imagAxis t ht)‖ ^ 3 ≤ (3 / 2 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg _) hE4 3
  rw [jInvariantFun, div_eq_mul_inv, norm_mul, norm_inv, norm_pow]
  calc ‖E4Fun (imagAxis t ht)‖ ^ 3 * ‖DeltaFun (imagAxis t ht)‖⁻¹
      ≤ (3 / 2 : ℝ) ^ 3 * (2 * Real.exp (2 * Real.pi * t)) :=
        mul_le_mul h1 hDinv (inv_nonneg.mpr (norm_nonneg _)) (by norm_num)
    _ ≤ (27 / 4 + 1) * Real.exp (2 * Real.pi * t) := by
        have := Real.exp_pos (2 * Real.pi * t); nlinarith

/-- `‖(E₁₀/Δ)(i t)‖ ≤ C e^{2π t}`. -/
lemma kwp_E10_div_imagAxis :
    ∃ CE : ℝ, 0 < CE ∧ ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
      ‖E10Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)‖
        ≤ CE * Real.exp (2 * Real.pi * t) := by
  obtain ⟨B, hB1, hB⟩ := Work.Asymptotics.Compact.imagAxis_cusp_bounds
  refine ⟨2 * (B ^ 2 + 1), by positivity, fun t ht ht1 => ?_⟩
  obtain ⟨-, -, -, -, -, hE4b, hE6b, -⟩ := hB t ht ht1
  have hDinv := kwp_invDelta_z t ht ht1
  have hE10 : ‖E10Fun (imagAxis t ht)‖ ≤ B ^ 2 := by
    rw [show E10Fun (imagAxis t ht) = E4Fun (imagAxis t ht) * E6Fun (imagAxis t ht) from rfl,
      norm_mul]
    calc ‖E4Fun (imagAxis t ht)‖ * ‖E6Fun (imagAxis t ht)‖ ≤ B * B :=
          mul_le_mul hE4b hE6b (norm_nonneg _) (by linarith)
      _ = B ^ 2 := by ring
  have hB0 : (0:ℝ) ≤ B := by linarith
  rw [div_eq_mul_inv, norm_mul]
  calc ‖E10Fun (imagAxis t ht)‖ * ‖(DeltaFun (imagAxis t ht))⁻¹‖
      ≤ B ^ 2 * (2 * Real.exp (2 * Real.pi * t)) :=
        mul_le_mul hE10 hDinv (norm_nonneg _) (by positivity)
    _ ≤ (2 * (B ^ 2 + 1)) * Real.exp (2 * Real.pi * t) := by
        have := Real.exp_pos (2 * Real.pi * t); nlinarith [hB0]

/-- `‖(E₁₄/Δ)(i t)‖ ≤ C e^{2π t}`. -/
lemma kwp_E14_div_imagAxis :
    ∃ CF : ℝ, 0 < CF ∧ ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
      ‖E14Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)‖
        ≤ CF * Real.exp (2 * Real.pi * t) := by
  obtain ⟨B, hB1, hB⟩ := Work.Asymptotics.Compact.imagAxis_cusp_bounds
  refine ⟨2 * (B ^ 3 + 1), by positivity, fun t ht ht1 => ?_⟩
  obtain ⟨-, -, -, -, -, hE4b, hE6b, -⟩ := hB t ht ht1
  have hDinv := kwp_invDelta_z t ht ht1
  have hE14 : ‖E14Fun (imagAxis t ht)‖ ≤ B ^ 3 := by
    rw [show E14Fun (imagAxis t ht) = E4Fun (imagAxis t ht) ^ 2 * E6Fun (imagAxis t ht)
      from rfl, norm_mul, norm_pow]
    calc ‖E4Fun (imagAxis t ht)‖ ^ 2 * ‖E6Fun (imagAxis t ht)‖ ≤ B ^ 2 * B :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hE4b 2) hE6b (norm_nonneg _)
            (by positivity)
      _ = B ^ 3 := by ring
  have hB0 : (0:ℝ) ≤ B := by linarith
  rw [div_eq_mul_inv, norm_mul]
  calc ‖E14Fun (imagAxis t ht)‖ * ‖(DeltaFun (imagAxis t ht))⁻¹‖
      ≤ B ^ 3 * (2 * Real.exp (2 * Real.pi * t)) :=
        mul_le_mul hE14 hDinv (norm_nonneg _) (by positivity)
    _ ≤ (2 * (B ^ 3 + 1)) * Real.exp (2 * Real.pi * t) := by
        have := Real.exp_pos (2 * Real.pi * t); nlinarith [hB0]

/-- `‖ℓ.L (i t)‖ ≤ C (1+t)`. -/
lemma kwp_Lz_imagAxis (ℓ : Work.Kernels.LogLambdaData) :
    ∃ CLz : ℝ, 0 < CLz ∧ ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
      ‖ℓ.L (imagAxis t ht)‖ ≤ CLz * (1 + t) := by
  obtain ⟨C, hC, h⟩ := (Work.Residues.LogLambdaBound ℓ).1
  refine ⟨C + Real.pi + 1, by positivity, fun t ht ht1 => ?_⟩
  have h1 := h (imagAxis t ht) (by rw [kwp_imagAxis_im t ht]; exact ht1)
  have h2 : ‖(Real.pi : ℂ) * Complex.I * ((imagAxis t ht : ℍ) : ℂ)‖
      = Real.pi * ‖((imagAxis t ht : ℍ) : ℂ)‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_I, mul_one]
  have h3 : ‖((imagAxis t ht : ℍ) : ℂ)‖ = t := kwp_imagAxis_norm t ht
  have h4 : ‖ℓ.L (imagAxis t ht)‖
      ≤ ‖ℓ.L (imagAxis t ht) - (Real.pi : ℂ) * Complex.I * ((imagAxis t ht : ℍ) : ℂ)‖
        + Real.pi * t := by
    have := norm_le_insert' (ℓ.L (imagAxis t ht))
      ((Real.pi : ℂ) * Complex.I * ((imagAxis t ht : ℍ) : ℂ))
    rw [h2, h3] at this
    linarith [this]
  have h5 : Real.pi * t ≤ Real.pi * (1 + t) := by nlinarith [Real.pi_pos]
  nlinarith [h1, h4, h5, Real.pi_pos]

/-- `‖U(z)² - V(z)²‖` is polynomially bounded on the imaginary axis. -/
lemma kwp_U2V2_imagAxis :
    ∃ CU NU : ℝ, 0 < CU ∧ 0 ≤ NU ∧ ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
      ‖UFun (imagAxis t ht) ^ 2 - VFun (imagAxis t ht) ^ 2‖ ≤ CU * (1 + t) ^ NU := by
  have hU := kwp_InP_imagAxis (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.pow 4 |>.pow 2)
  have hV := kwp_InP_imagAxis (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.pow 4 |>.pow 2)
  obtain ⟨AU, NU, hAU, hNU, hbU⟩ := hU
  obtain ⟨AV, NV, hAV, hNV, hbV⟩ := hV
  refine ⟨AU + AV + 1, max NU NV, by positivity, le_max_of_le_left hNU, fun t ht ht1 => ?_⟩
  have h1 := hbU t ht ht1
  have h2 := hbV t ht ht1
  have hU' : UFun (imagAxis t ht) ^ 2 = theta00Fun (imagAxis t ht) ^ 8 := by
    simp only [UFun]; ring
  have hV' : VFun (imagAxis t ht) ^ 2 = theta10Fun (imagAxis t ht) ^ 8 := by
    simp only [VFun]; ring
  have hN1 : NU ≤ max NU NV := le_max_left _ _
  have hN2 : NV ≤ max NU NV := le_max_right _ _
  have ht1' : (1:ℝ) ≤ 1 + t := by linarith
  have hT0 : (0:ℝ) ≤ (1 + t) ^ max NU NV := Real.rpow_nonneg (by linarith) _
  have hA1 : AU * (1 + t) ^ NU ≤ AU * (1 + t) ^ max NU NV :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1' hN1) hAU.le
  have hA2 : AV * (1 + t) ^ NV ≤ AV * (1 + t) ^ max NU NV :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1' hN2) hAV.le
  rw [hU', hV']
  refine le_trans (norm_sub_le _ _) ?_
  calc ‖theta00Fun (imagAxis t ht) ^ 8‖ + ‖theta10Fun (imagAxis t ht) ^ 8‖
      = ‖UFun (imagAxis t ht) ^ 2‖ + ‖VFun (imagAxis t ht) ^ 2‖ := by rw [← hU', ← hV']
    _ ≤ (AU + AV + 1) * (1 + t) ^ max NU NV := by
        nlinarith [h1, h2, hA1, hA2, hAU.le, hAV.le, hT0]






/-! ## Elementary monotone-combination lemmas -/

lemma kwp_le_T1 {a A K N J t2 : ℝ} (ha : a ≤ A * (1 + N) * t2) (hA : A ≤ K) (hA0 : 0 ≤ A)
    (hN : 0 ≤ 1 + N) (hJ : 1 ≤ 1 + J) (ht2 : 0 ≤ t2) :
    a ≤ K * (1 + N) * (1 + J) * t2 := by
  have hK0 : 0 ≤ K := le_trans hA0 hA
  have h1 : A * (1 + N) * t2 ≤ K * (1 + N) * t2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hN) ht2
  have h2 : K * (1 + N) * t2 ≤ K * (1 + N) * (1 + J) * t2 := by
    have h3 : (0:ℝ) ≤ K * (1 + N) * t2 := by positivity
    have h4 : K * (1 + N) * t2 * 1 ≤ K * (1 + N) * t2 * (1 + J) :=
      mul_le_mul_of_nonneg_left hJ h3
    calc K * (1 + N) * t2 = K * (1 + N) * t2 * 1 := by ring
      _ ≤ K * (1 + N) * t2 * (1 + J) := h4
      _ = K * (1 + N) * (1 + J) * t2 := by ring
  linarith

lemma kwp_le_T2 {a A K N J t2 : ℝ} (ha : a ≤ A * J * (1 + N) * t2) (hA : A ≤ K) (hA0 : 0 ≤ A)
    (hN : 0 ≤ 1 + N) (hJ0 : 0 ≤ J) (ht2 : 0 ≤ t2) :
    a ≤ K * (1 + N) * (1 + J) * t2 := by
  have hK0 : 0 ≤ K := le_trans hA0 hA
  have h1 : A * J * (1 + N) * t2 ≤ K * J * (1 + N) * t2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hJ0) hN) ht2
  have h2 : K * J * (1 + N) * t2 ≤ K * (1 + N) * (1 + J) * t2 := by
    have h3 : (0:ℝ) ≤ K * (1 + N) * t2 := by positivity
    have h4 : J * (K * (1 + N) * t2) ≤ (1 + J) * (K * (1 + N) * t2) :=
      mul_le_mul_of_nonneg_right (by linarith) h3
    calc K * J * (1 + N) * t2 = J * (K * (1 + N) * t2) := by ring
      _ ≤ (1 + J) * (K * (1 + N) * t2) := h4
      _ = K * (1 + N) * (1 + J) * t2 := by ring
  linarith

lemma kwp_norm4 {a b c d : ℂ} {A B C D : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C)
    (hd : ‖d‖ ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ‖a * b * (c * d)‖ ≤ A * B * (C * D) := by
  rw [norm_mul, norm_mul, norm_mul]
  have h1 : ‖a‖ * ‖b‖ ≤ A * B := mul_le_mul ha hb (norm_nonneg _) hA
  have h2 : ‖c‖ * ‖d‖ ≤ C * D := mul_le_mul hc hd (norm_nonneg _) hC
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-! ## The sharp bound for `B'` -/

set_option maxHeartbeats 4000000 in
open Work.Residues in
lemma kwp_Bprime_sharp (ℓ : LogLambdaData) :
    ∃ H K : ℝ, 0 ≤ H ∧ 0 < K ∧
      ∀ z τ : ℍ, H ≤ τ.im → 1 ≤ z.im →
        ‖Bprimefun ℓ z τ‖
          ≤ K * (1 + ‖(τ : ℂ)‖) * (1 + ‖jInvariantFun z‖) * (tpar τ) ^ 2 := by
  obtain ⟨HL, CL, hCL, hL⟩ := L_cusp ℓ
  obtain ⟨HS, CS, hCS, hS⟩ := LS_cusp ℓ
  obtain ⟨HB, CB, hCB, hB⟩ := B0core_cusp
  obtain ⟨HC, CC, hCC, hC⟩ := Ccore_cusp ℓ
  obtain ⟨HX, CX, hCX, hX⟩ := X_cusp
  obtain ⟨HY, CY, hCY, hY⟩ := Y_cusp
  obtain ⟨HD, CD, hCD, hD⟩ := Delta_cusp
  refine ⟨max HL (max HS (max HB (max HC (max HX (max HY (max HD 1)))))), 
    CL * CB + 2 * CL * CX + CC + 2 * CS * CY + 3456 * CD + 1, ?_, ?_, ?_⟩
  · have h1 : (1:ℝ) ≤ max HD 1 := le_max_right _ _
    have h2 : max HD 1 ≤ max HY (max HD 1) := le_max_right _ _
    have h3 : max HY (max HD 1) ≤ max HX (max HY (max HD 1)) := le_max_right _ _
    have h4 : max HX (max HY (max HD 1)) ≤ max HC (max HX (max HY (max HD 1))) := le_max_right _ _
    have h5 : max HC (max HX (max HY (max HD 1))) ≤ max HB (max HC (max HX (max HY (max HD 1)))) := le_max_right _ _
    have h6 : max HB (max HC (max HX (max HY (max HD 1)))) ≤ max HS (max HB (max HC (max HX (max HY (max HD 1))))) := le_max_right _ _
    have h7 : max HS (max HB (max HC (max HX (max HY (max HD 1))))) ≤ max HL (max HS (max HB (max HC (max HX (max HY (max HD 1)))))) := le_max_right _ _
    linarith
  · have h1 : (0:ℝ) ≤ CL * CB := mul_nonneg hCL.le hCB.le
    have h2 : (0:ℝ) ≤ 2 * CL * CX := by positivity
    have h3 : (0:ℝ) ≤ 2 * CS * CY := by positivity
    have h4 : (0:ℝ) ≤ 3456 * CD := by positivity
    have h5 : (0:ℝ) ≤ CC := hCC.le
    linarith
  · intro z τ hτ hz
    have hτS : HS ≤ τ.im := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hτ)
    have hτB : HB ≤ τ.im := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hτ))
    have hτC : HC ≤ τ.im := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hτ)))
    have hτX : HX ≤ τ.im := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hτ))))
    have hτY : HY ≤ τ.im := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hτ)))))
    have hτD : HD ≤ τ.im := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hτ))))))
    have hτL : HL ≤ τ.im := le_trans (le_max_left _ _) hτ
    have h1 : ‖ℓ.L τ‖ ≤ CL * (1 + ‖(τ : ℂ)‖) := by simpa using hL τ hτL
    have h2 : ‖ℓ.L_S τ‖ ≤ CS * tpar τ := by simpa using hS τ hτS
    have h3 : ‖B0core τ‖ ≤ CB * tpar τ ^ 2 := by simpa using hB τ hτB
    have h4 : ‖Ccore ℓ τ‖ ≤ CC * tpar τ ^ 2 := by simpa using hC τ hτC
    have h5 : ‖Xfun τ‖ ≤ CX * tpar τ ^ 2 := by simpa using hX τ hτX
    have h6 : ‖Yfun τ‖ ≤ CY * tpar τ := by simpa using hY τ hτY
    have h7 : ‖DeltaFun τ‖ ≤ CD * tpar τ ^ 2 := by simpa using hD τ hτD
    set N : ℝ := ‖(τ : ℂ)‖ with hN
    set J : ℝ := ‖jInvariantFun z‖ with hJ
    set tt : ℝ := tpar τ with htt
    set t2 : ℝ := tt ^ 2 with ht2def
    have h1' : ‖ℓ.L τ‖ ≤ CL * (1 + N) := by rw [hN]; exact h1
    have h2' : ‖ℓ.L_S τ‖ ≤ CS * tt := by rw [htt]; exact h2
    have h3' : ‖B0core τ‖ ≤ CB * tt ^ 2 := by rw [htt]; exact h3
    have h4' : ‖Ccore ℓ τ‖ ≤ CC * tt ^ 2 := by rw [htt]; exact h4
    have h5' : ‖Xfun τ‖ ≤ CX * tt ^ 2 := by rw [htt]; exact h5
    have h6' : ‖Yfun τ‖ ≤ CY * tt := by rw [htt]; exact h6
    have h7' : ‖DeltaFun τ‖ ≤ CD * tt ^ 2 := by rw [htt]; exact h7
    have hJinv : ‖jInvariantFun z‖ = J := by rw [hJ]
    have ht2 : t2 = tpar τ ^ 2 := by rw [ht2def, htt]
    have hN0 : (0:ℝ) ≤ 1 + N := by positivity
    have hNn : (0:ℝ) ≤ N := by rw [hN]; positivity
    have hJ0 : (0:ℝ) ≤ J := by rw [hJ]; positivity
    have hJ1 : (1:ℝ) ≤ 1 + J := by linarith
    have ht20 : (0:ℝ) ≤ t2 := by rw [ht2def]; positivity
    have hKpos : (0:ℝ) < CL * CB + 2 * CL * CX + CC + 2 * CS * CY + 3456 * CD + 1 := by
      have h1 : (0:ℝ) ≤ CL * CB := mul_nonneg hCL.le hCB.le
      have h2 : (0:ℝ) ≤ 2 * CL * CX := by positivity
      have h3 : (0:ℝ) ≤ 2 * CS * CY := by positivity
      have h4 : (0:ℝ) ≤ 3456 * CD := by positivity
      have h5 : (0:ℝ) ≤ CC := hCC.le
      linarith
    set K : ℝ := CL * CB + 2 * CL * CX + CC + 2 * CS * CY + 3456 * CD + 1 with hK
    have hCLn : (0:ℝ) ≤ CL := hCL.le
    have hCSn : (0:ℝ) ≤ CS := hCS.le
    have hCBn : (0:ℝ) ≤ CB := hCB.le
    have hCCn : (0:ℝ) ≤ CC := hCC.le
    have hCXn : (0:ℝ) ≤ CX := hCX.le
    have hCYn : (0:ℝ) ≤ CY := hCY.le
    have hCDn : (0:ℝ) ≤ CD := hCD.le
    have hKCB : CL * CB ≤ K := by rw [hK]; nlinarith [hCLn, hCBn, hCCn, hCSn, hCYn, hCDn, hCXn]
    have hKCX : 2 * CL * CX ≤ K := by rw [hK]; nlinarith [hCLn, hCBn, hCCn, hCSn, hCYn, hCDn, hCXn]
    have hKCC : CC ≤ K := by rw [hK]; nlinarith [hCLn, hCBn, hCCn, hCSn, hCYn, hCDn, hCXn]
    have hKCY : 2 * CS * CY ≤ K := by rw [hK]; nlinarith [hCLn, hCBn, hCCn, hCSn, hCYn, hCDn, hCXn]
    have hKCD : 3456 * CD ≤ K := by rw [hK]; nlinarith [hCLn, hCBn, hCCn, hCSn, hCYn, hCDn, hCXn]
    -- the five terms, each against its own coefficient
    have e1 : ‖ℓ.L τ * B0core τ‖ ≤ CL * CB * (1 + N) * (1 + J) * t2 := by
      refine kwp_le_T1 (A := CL * CB) (K := CL * CB) ?_ le_rfl (mul_nonneg hCLn hCBn) hN0 hJ1 ht20
      calc ‖ℓ.L τ * B0core τ‖ ≤ (CL * (1 + N)) * (CB * tt ^ 2) := by
            rw [norm_mul]
            exact mul_le_mul h1' h3' (norm_nonneg _) (mul_nonneg hCLn hN0)
        _ = CL * CB * (1 + N) * t2 := by rw [ht2def, htt]; ring
    have e2 : ‖(2:ℂ) * jInvariantFun z * (ℓ.L τ * Xfun τ)‖ ≤ 2 * CL * CX * (1 + N) * (1 + J) * t2 := by
      refine kwp_le_T2 (A := 2 * CL * CX) (K := 2 * CL * CX) ?_ le_rfl (by positivity) hN0 hJ0 ht20
      have hprod := kwp_norm4 (a := (2:ℂ)) (b := jInvariantFun z) (c := ℓ.L τ) (d := Xfun τ)
        (A := 2) (B := J) (C := CL * (1 + N)) (D := CX * tt ^ 2)
        (by simp) hJinv.le h1' h5' (by norm_num) hJ0 (mul_nonneg hCLn hN0) (by positivity)
      calc ‖(2:ℂ) * jInvariantFun z * (ℓ.L τ * Xfun τ)‖ ≤ 2 * J * ((CL * (1 + N)) * (CX * tt ^ 2)) := hprod
        _ = 2 * CL * CX * J * (1 + N) * t2 := by rw [ht2def, htt]; ring
    have e3 : ‖Ccore ℓ τ‖ ≤ CC * (1 + N) * (1 + J) * t2 := by
      refine kwp_le_T1 (A := CC) (K := CC) ?_ le_rfl hCCn hN0 hJ1 ht20
      calc ‖Ccore ℓ τ‖ ≤ CC * tt ^ 2 := h4'
        _ = CC * t2 := by rw [ht2def]
        _ ≤ CC * (1 + N) * t2 := by
            have h5' : t2 ≤ (1 + N) * t2 := by nlinarith [hNn, ht20]
            calc CC * t2 ≤ CC * ((1 + N) * t2) := mul_le_mul_of_nonneg_left h5' hCCn
              _ = CC * (1 + N) * t2 := by ring
    have e4 : ‖(2:ℂ) * jInvariantFun z * (ℓ.L_S τ * Yfun τ)‖ ≤ 2 * CS * CY * (1 + N) * (1 + J) * t2 := by
      refine kwp_le_T2 (A := 2 * CS * CY) (K := 2 * CS * CY) ?_ le_rfl (by positivity) hN0 hJ0 ht20
      have hprod := kwp_norm4 (a := (2:ℂ)) (b := jInvariantFun z) (c := ℓ.L_S τ) (d := Yfun τ)
        (A := 2) (B := J) (C := CS * tt) (D := CY * tt)
        (by simp) hJinv.le h2' h6' (by norm_num) hJ0 (mul_nonneg hCSn (by rw [htt]; exact tpar_nonneg τ))
        (mul_nonneg hCYn (by rw [htt]; exact tpar_nonneg τ))
      calc ‖(2:ℂ) * jInvariantFun z * (ℓ.L_S τ * Yfun τ)‖ ≤ 2 * J * ((CS * tt) * (CY * tt)) := hprod
        _ = 2 * CS * CY * J * t2 := by rw [ht2def, htt]; ring
        _ ≤ 2 * CS * CY * J * (1 + N) * t2 := by
            have h5' : t2 ≤ (1 + N) * t2 := by nlinarith [hNn, ht20]
            have h6' : (0:ℝ) ≤ 2 * CS * CY * J := by positivity
            calc 2 * CS * CY * J * t2 ≤ 2 * CS * CY * J * ((1 + N) * t2) :=
                  mul_le_mul_of_nonneg_left h5' h6'
              _ = 2 * CS * CY * J * (1 + N) * t2 := by ring
    have e5 : ‖(3456:ℂ) * DeltaFun τ * jInvariantFun z‖ ≤ 3456 * CD * (1 + N) * (1 + J) * t2 := by
      refine kwp_le_T2 (A := 3456 * CD) (K := 3456 * CD) ?_ le_rfl (by positivity) hN0 hJ0 ht20
      have h3456 : ‖(3456:ℂ) * DeltaFun τ‖ ≤ 3456 * CD * tt ^ 2 := by
        rw [norm_mul, Complex.norm_ofNat]
        calc 3456 * ‖DeltaFun τ‖ ≤ 3456 * (CD * tt ^ 2) :=
              mul_le_mul_of_nonneg_left h7' (by norm_num)
          _ = 3456 * CD * tt ^ 2 := by ring
      have hstep1 : ‖(3456:ℂ) * DeltaFun τ * jInvariantFun z‖ ≤ (3456 * CD * tt ^ 2) * J := by
        rw [norm_mul, hJinv]
        exact mul_le_mul h3456 (le_refl J) (norm_nonneg _) (by positivity)
      have hstep2 : (3456 * CD * tt ^ 2) * J ≤ 3456 * CD * J * (1 + N) * t2 := by
        have h5' : t2 ≤ (1 + N) * t2 := by nlinarith [hNn, ht20]
        have h6' : (0:ℝ) ≤ 3456 * CD * J := by positivity
        have heq : (3456 * CD * tt ^ 2) * J = 3456 * CD * J * t2 := by rw [ht2def]; ring
        rw [heq]
        calc 3456 * CD * J * t2 ≤ 3456 * CD * J * ((1 + N) * t2) :=
              mul_le_mul_of_nonneg_left h5' h6'
          _ = 3456 * CD * J * (1 + N) * t2 := by ring
      exact le_trans hstep1 hstep2
    have hsplit : ‖Bprimefun ℓ z τ‖
        ≤ ‖ℓ.L τ * B0core τ‖ + ‖(2:ℂ) * jInvariantFun z * (ℓ.L τ * Xfun τ)‖
          + ‖Ccore ℓ τ‖ + ‖(2:ℂ) * jInvariantFun z * (ℓ.L_S τ * Yfun τ)‖
          + ‖(3456:ℂ) * DeltaFun τ * jInvariantFun z‖ := by
      rw [Bprimefun]
      exact norm_add5_le _ _ _ _ _
    have hsum : ‖ℓ.L τ * B0core τ‖ + ‖(2:ℂ) * jInvariantFun z * (ℓ.L τ * Xfun τ)‖
          + ‖Ccore ℓ τ‖ + ‖(2:ℂ) * jInvariantFun z * (ℓ.L_S τ * Yfun τ)‖
          + ‖(3456:ℂ) * DeltaFun τ * jInvariantFun z‖
        ≤ (CL * CB + 2 * CL * CX + CC + 2 * CS * CY + 3456 * CD) * (1 + N) * (1 + J) * t2 := by
      have h := add_le_add (add_le_add (add_le_add (add_le_add e1 e2) e3) e4) e5
      have heq : CL * CB * (1 + N) * (1 + J) * t2
            + (2 * CL * CX * (1 + N) * (1 + J) * t2
              + (CC * (1 + N) * (1 + J) * t2
                + (2 * CS * CY * (1 + N) * (1 + J) * t2
                  + 3456 * CD * (1 + N) * (1 + J) * t2)))
          = (CL * CB + 2 * CL * CX + CC + 2 * CS * CY + 3456 * CD) * (1 + N) * (1 + J) * t2 := by
        ring
      linarith [h, heq.le, heq.ge]
    have hgoal : K * (1 + ‖(τ : ℂ)‖) * (1 + ‖jInvariantFun z‖) * tpar τ ^ 2
        = K * (1 + N) * (1 + J) * t2 := by rw [hN, hJ, ht2def, htt]
    have hfac : (0:ℝ) ≤ (1 + N) * (1 + J) * t2 := by positivity
    rw [hgoal, hK]
    linarith [hsplit, hsum, hfac]


lemma kwp_norm_add_sub3_le (a b c : ℂ) : ‖a + b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  calc ‖a + b - c‖ ≤ ‖a + b‖ + ‖c‖ := norm_sub_le _ _
    _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by linarith [norm_add_le a b]
    _ = ‖a‖ + ‖b‖ + ‖c‖ := by ring


/- `‖ψ₄E₈ - ψ₂E₁₀‖ ≤ K (1+‖τ‖) tpar τ²`. -/
set_option maxHeartbeats 4000000 in
open Work.Residues in
lemma kwp_P_sharp (ℓ : LogLambdaData) :
    ∃ H K : ℝ, 0 ≤ H ∧ 0 < K ∧ ∀ τ : ℍ, H ≤ τ.im →
      ‖psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ‖
        ≤ K * (1 + ‖(τ : ℂ)‖) * (tpar τ) ^ 2 := by
  obtain ⟨HL, CL, hCL, hL⟩ := L_cusp ℓ
  obtain ⟨HS, CS, hCS, hS⟩ := LS_cusp ℓ
  obtain ⟨HX, CX, hCX, hX⟩ := X_cusp
  obtain ⟨HY, CY, hCY, hY⟩ := Y_cusp
  refine ⟨max HL (max HS (max HX (max HY 1))), CL * CX + CS * CY + 1, ?_, ?_, ?_⟩
  · -- `0 ≤ H`
    have a1 : (1:ℝ) ≤ max HY 1 := le_max_right _ _
    have a2 : max HY 1 ≤ max HX (max HY 1) := le_max_right _ _
    have a3 : max HX (max HY 1) ≤ max HS (max HX (max HY 1)) := le_max_right _ _
    have a4 : max HS (max HX (max HY 1)) ≤ max HL (max HS (max HX (max HY 1))) := le_max_right _ _
    linarith
  · -- `0 < K`
    have h1 : (0:ℝ) ≤ CL * CX := mul_nonneg hCL.le hCX.le
    have h2 : (0:ℝ) ≤ CS * CY := mul_nonneg hCS.le hCY.le
    linarith
  · intro τ hτ
    have hτL : HL ≤ τ.im := le_trans (le_max_left _ _) hτ
    have hτS : HS ≤ τ.im := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hτ)
    have hτX : HX ≤ τ.im := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hτ))
    have hτY : HY ≤ τ.im := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hτ)))
    have h1 : ‖ℓ.L τ‖ ≤ CL * (1 + ‖(τ : ℂ)‖) := by simpa using hL τ hτL
    have h2 : ‖ℓ.L_S τ‖ ≤ CS * tpar τ := by simpa using hS τ hτS
    have h3 : ‖Xfun τ‖ ≤ CX * tpar τ ^ 2 := by simpa using hX τ hτX
    have h4 : ‖Yfun τ‖ ≤ CY * tpar τ := by simpa using hY τ hτY
    have hS0 : (0:ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by positivity
    have ht0 : (0:ℝ) ≤ tpar τ := tpar_nonneg τ
    have ht2 : (0:ℝ) ≤ tpar τ ^ 2 := by positivity
    have hLX : ‖ℓ.L τ * Xfun τ‖ ≤ CL * CX * (1 + ‖(τ : ℂ)‖) * tpar τ ^ 2 := by
      rw [norm_mul]
      calc ‖ℓ.L τ‖ * ‖Xfun τ‖ ≤ (CL * (1 + ‖(τ : ℂ)‖)) * (CX * tpar τ ^ 2) :=
            mul_le_mul h1 h3 (norm_nonneg _) (mul_nonneg hCL.le hS0)
        _ = CL * CX * (1 + ‖(τ : ℂ)‖) * tpar τ ^ 2 := by ring
    have hLSY : ‖ℓ.L_S τ * Yfun τ‖ ≤ CS * CY * (1 + ‖(τ : ℂ)‖) * tpar τ ^ 2 := by
      rw [norm_mul]
      have hstep : (CS * tpar τ) * (CY * tpar τ) ≤ CS * CY * (1 + ‖(τ : ℂ)‖) * tpar τ ^ 2 := by
        have h5 : tpar τ ^ 2 ≤ (1 + ‖(τ : ℂ)‖) * tpar τ ^ 2 := by
          have h6 : (1:ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by
            have := norm_nonneg (τ : ℂ); linarith
          calc tpar τ ^ 2 = 1 * tpar τ ^ 2 := by ring
            _ ≤ (1 + ‖(τ : ℂ)‖) * tpar τ ^ 2 := mul_le_mul_of_nonneg_right h6 ht2
        calc (CS * tpar τ) * (CY * tpar τ) = CS * CY * tpar τ ^ 2 := by ring
          _ ≤ CS * CY * ((1 + ‖(τ : ℂ)‖) * tpar τ ^ 2) :=
                mul_le_mul_of_nonneg_left h5 (mul_nonneg hCS.le hCY.le)
          _ = CS * CY * (1 + ‖(τ : ℂ)‖) * tpar τ ^ 2 := by ring
      exact le_trans (mul_le_mul h2 h4 (norm_nonneg _) (mul_nonneg hCS.le ht0)) hstep
    rw [psi4E8_sub ℓ τ]
    refine le_trans (norm_add_le _ _) ?_
    have hsum : CL * CX * (1 + ‖(τ : ℂ)‖) * tpar τ ^ 2 + CS * CY * (1 + ‖(τ : ℂ)‖) * tpar τ ^ 2
        ≤ (CL * CX + CS * CY + 1) * (1 + ‖(τ : ℂ)‖) * tpar τ ^ 2 := by
      have h5 : (0:ℝ) ≤ (1 + ‖(τ : ℂ)‖) * tpar τ ^ 2 := by positivity
      have heq : CL * CX * (1 + ‖(τ : ℂ)‖) * tpar τ ^ 2 + CS * CY * (1 + ‖(τ : ℂ)‖) * tpar τ ^ 2
          = (CL * CX + CS * CY) * ((1 + ‖(τ : ℂ)‖) * tpar τ ^ 2) := by ring
      rw [heq]
      calc (CL * CX + CS * CY) * ((1 + ‖(τ : ℂ)‖) * tpar τ ^ 2)
          ≤ (CL * CX + CS * CY + 1) * ((1 + ‖(τ : ℂ)‖) * tpar τ ^ 2) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num)) h5
        _ = (CL * CX + CS * CY + 1) * (1 + ‖(τ : ℂ)‖) * tpar τ ^ 2 := by ring
    exact le_trans (add_le_add hLX hLSY) hsum

/-! ## The bracket bound on the window -/

set_option maxHeartbeats 8000000 in
open Work.Residues in
lemma kwp_bracket24_sharp (ℓ : LogLambdaData) :
    ∃ H K M : ℝ, 0 ≤ H ∧ 0 < K ∧ 0 ≤ M ∧
      ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t), H ≤ τ.im → 1 ≤ t →
        ‖bracket24 ℓ (imagAxis t ht) τ‖
          ≤ K * (1 + ‖(τ : ℂ)‖) * (1 + t) ^ M * Real.exp (2 * Real.pi * t)
              * (tpar τ) ^ 2 := by
  obtain ⟨HB, KB, hHB, hKB, hB⟩ := kwp_Bprime_sharp ℓ
  obtain ⟨HP, KP, hHP, hKP, hP⟩ := kwp_P_sharp ℓ
  obtain ⟨HD, CD, hCD, hD⟩ := Delta_cusp
  obtain ⟨CE, hCE, hE10D⟩ := kwp_E10_div_imagAxis
  obtain ⟨CF, hCF, hE14D⟩ := kwp_E14_div_imagAxis
  obtain ⟨CU, NU, hCU, hNU, hU2V2⟩ := kwp_U2V2_imagAxis
  obtain ⟨CW, NW, hCW, hNW, hW⟩ := kwp_InP_imagAxis
    (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.pow 4)
  obtain ⟨CJ, hCJ, hjz⟩ := kwp_jz_imagAxis
  obtain ⟨CLz, hCLz, hLz⟩ := kwp_Lz_imagAxis ℓ
  refine ⟨max HB (max HP (max HD 1)), 
    CW * KB * (1 + CJ) + CE * CU * KP + 3456 * CD * CF * CLz + 1, max NW (max NU 1),
    ?_, ?_, ?_, ?_⟩
  · have a1 : (1:ℝ) ≤ max HD 1 := le_max_right _ _
    have a2 : max HD 1 ≤ max HP (max HD 1) := le_max_right _ _
    have a3 : max HP (max HD 1) ≤ max HB (max HP (max HD 1)) := le_max_right _ _
    linarith
  · have h1 : (0:ℝ) ≤ CW * KB * (1 + CJ) := mul_nonneg (mul_nonneg hCW.le hKB.le) (by linarith)
    have h2 : (0:ℝ) ≤ CE * CU * KP := mul_nonneg (mul_nonneg hCE.le hCU.le) hKP.le
    have h3 : (0:ℝ) ≤ 3456 * CD * CF * CLz :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCD.le) hCF.le) hCLz.le
    linarith
  · exact le_trans (le_trans hNU (le_max_left NU 1)) (le_max_right NW (max NU 1))
  · intro τ t ht hτ ht1
    have hτB : HB ≤ τ.im := le_trans (le_max_left _ _) hτ
    have hτP : HP ≤ τ.im := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hτ)
    have hτD : HD ≤ τ.im := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hτ))
    have hz1 : (1:ℝ) ≤ (imagAxis t ht).im := by rw [kwp_imagAxis_im t ht]; exact ht1
    have hb := hB (imagAxis t ht) τ hτB hz1
    have hp := hP τ hτP
    have hd : ‖DeltaFun τ‖ ≤ CD * tpar τ ^ 2 := by simpa using hD τ hτD
    have hW := hW t ht ht1
    have hU := hU2V2 t ht ht1
    have hE10 := hE10D t ht ht1
    have hE14 := hE14D t ht ht1
    have hJ := hjz t ht ht1
    have hL := hLz t ht ht1
    set E : ℝ := Real.exp (2 * Real.pi * t) with hE
    have hE1 : (1:ℝ) ≤ E := by rw [hE]; rw [Real.one_le_exp_iff]; positivity
    have hE0 : (0:ℝ) ≤ E := le_trans zero_le_one hE1
    set N : ℝ := ‖(τ : ℂ)‖ with hN
    set TT : ℝ := tpar τ with hTT
    have hN0 : (0:ℝ) ≤ 1 + N := by positivity
    have hNn : (0:ℝ) ≤ N := by rw [hN]; positivity
    have hN1 : (1:ℝ) ≤ 1 + N := by linarith
    have hS1 : (1:ℝ) ≤ 1 + t := by linarith
    have hS0 : (0:ℝ) ≤ 1 + t := by linarith
    have hTT0 : (0:ℝ) ≤ TT := by rw [hTT]; exact tpar_nonneg τ
    have hTT2 : (0:ℝ) ≤ TT ^ 2 := by positivity
    have hb' : ‖Bprimefun ℓ (imagAxis t ht) τ‖
        ≤ KB * (1 + N) * (1 + ‖jInvariantFun (imagAxis t ht)‖) * TT ^ 2 := by
      rw [hN, hTT]; exact hb
    have hp' : ‖psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ‖ ≤ KP * (1 + N) * TT ^ 2 := by
      rw [hN, hTT]; exact hp
    have hd' : ‖DeltaFun τ‖ ≤ CD * TT ^ 2 := by rw [hTT]; exact hd
    have hJ' : ‖jInvariantFun (imagAxis t ht)‖ ≤ CJ * E := by rw [hE]; exact hJ
    have hE10' : ‖E10Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)‖ ≤ CE * E := by
      rw [hE]; exact hE10
    have hE14' : ‖E14Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)‖ ≤ CF * E := by
      rw [hE]; exact hE14
    have hfj : 1 + ‖jInvariantFun (imagAxis t ht)‖ ≤ (1 + CJ) * E := by
      have h2 : ‖jInvariantFun (imagAxis t ht)‖ ≤ CJ * E := hJ'
      have h3 : (0:ℝ) ≤ CJ := hCJ.le
      nlinarith [hE1, h2, h3]
    have tA : ‖WFun (imagAxis t ht) * Bprimefun ℓ (imagAxis t ht) τ‖
        ≤ CW * KB * (1 + CJ) * (1 + N) * (1 + t) ^ NW * E * TT ^ 2 := by
      rw [norm_mul]
      calc ‖WFun (imagAxis t ht)‖ * ‖Bprimefun ℓ (imagAxis t ht) τ‖
          ≤ (CW * (1 + t) ^ NW) * (KB * (1 + N) * ((1 + CJ) * E) * TT ^ 2) := by
            refine mul_le_mul hW ?_ (norm_nonneg _) (by positivity)
            calc ‖Bprimefun ℓ (imagAxis t ht) τ‖
                ≤ KB * (1 + N) * (1 + ‖jInvariantFun (imagAxis t ht)‖) * TT ^ 2 := hb'
              _ ≤ KB * (1 + N) * ((1 + CJ) * E) * TT ^ 2 := by
                  have h6 : (0:ℝ) ≤ KB * (1 + N) * TT ^ 2 := mul_nonneg (mul_nonneg hKB.le hN0) hTT2
                  have h7 := mul_le_mul_of_nonneg_left hfj h6
                  calc KB * (1 + N) * (1 + ‖jInvariantFun (imagAxis t ht)‖) * TT ^ 2
                      = (KB * (1 + N) * TT ^ 2) * (1 + ‖jInvariantFun (imagAxis t ht)‖) := by ring
                    _ ≤ (KB * (1 + N) * TT ^ 2) * ((1 + CJ) * E) := h7
                    _ = KB * (1 + N) * ((1 + CJ) * E) * TT ^ 2 := by ring
        _ = CW * KB * (1 + CJ) * (1 + N) * (1 + t) ^ NW * E * TT ^ 2 := by ring
    have tB : ‖(E10Fun (imagAxis t ht) / DeltaFun (imagAxis t ht))
          * (UFun (imagAxis t ht) ^ 2 - VFun (imagAxis t ht) ^ 2)
          * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
        ≤ CE * CU * KP * (1 + N) * (1 + t) ^ NU * E * TT ^ 2 := by
      have hprod := kwp_norm4 (a := E10Fun (imagAxis t ht) / DeltaFun (imagAxis t ht))
        (b := (UFun (imagAxis t ht) ^ 2 - VFun (imagAxis t ht) ^ 2))
        (c := (1 : ℂ)) (d := (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))
        (A := CE * E) (B := CU * (1 + t) ^ NU) (C := 1) (D := KP * (1 + N) * TT ^ 2)
        hE10' hU (by norm_num) hp' (by positivity) (by positivity) (by norm_num) (by positivity)
      have heq : ‖E10Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)
            * (UFun (imagAxis t ht) ^ 2 - VFun (imagAxis t ht) ^ 2)
            * (1 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))‖
          = ‖(E10Fun (imagAxis t ht) / DeltaFun (imagAxis t ht))
              * (UFun (imagAxis t ht) ^ 2 - VFun (imagAxis t ht) ^ 2)
              * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖ := by rw [one_mul]
      rw [← heq]
      calc ‖E10Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)
            * (UFun (imagAxis t ht) ^ 2 - VFun (imagAxis t ht) ^ 2)
            * (1 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))‖
          ≤ (CE * E) * (CU * (1 + t) ^ NU) * (1 * (KP * (1 + N) * TT ^ 2)) := hprod
        _ = CE * CU * KP * (1 + N) * (1 + t) ^ NU * E * TT ^ 2 := by ring
    have tC : ‖(3456:ℂ) * DeltaFun τ * (E14Fun (imagAxis t ht) / DeltaFun (imagAxis t ht))
          * ℓ.L (imagAxis t ht)‖
        ≤ 3456 * CD * CF * CLz * (1 + N) * (1 + t) * E * TT ^ 2 := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
      have h3456 : 3456 * ‖DeltaFun τ‖ * ‖E14Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)‖
            * ‖ℓ.L (imagAxis t ht)‖
          ≤ 3456 * (CD * TT ^ 2) * (CF * E) * (CLz * (1 + t)) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hd' (by norm_num)) hE14'
          (norm_nonneg _) (by positivity)) hL (norm_nonneg _) (by positivity)
      calc 3456 * ‖DeltaFun τ‖ * ‖E14Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)‖
            * ‖ℓ.L (imagAxis t ht)‖
          ≤ 3456 * (CD * TT ^ 2) * (CF * E) * (CLz * (1 + t)) := h3456
        _ = 3456 * CD * CF * CLz * TT ^ 2 * E * (1 + t) := by ring
        _ ≤ 3456 * CD * CF * CLz * (1 + N) * (1 + t) * E * TT ^ 2 := by
            have h7 : TT ^ 2 * (1 + t) ≤ (1 + N) * (1 + t) * TT ^ 2 := by
              have h6 : (1:ℝ) ≤ 1 + N := by linarith
              calc TT ^ 2 * (1 + t) = 1 * (TT ^ 2 * (1 + t)) := by ring
                _ ≤ (1 + N) * (TT ^ 2 * (1 + t)) :=
                      mul_le_mul_of_nonneg_right h6 (by positivity)
                _ = (1 + N) * (1 + t) * TT ^ 2 := by ring
            calc 3456 * CD * CF * CLz * TT ^ 2 * E * (1 + t)
                = (3456 * CD * CF * CLz * E) * (TT ^ 2 * (1 + t)) := by ring
              _ ≤ (3456 * CD * CF * CLz * E) * ((1 + N) * (1 + t) * TT ^ 2) :=
                    mul_le_mul_of_nonneg_left h7 (by positivity)
              _ = 3456 * CD * CF * CLz * (1 + N) * (1 + t) * E * TT ^ 2 := by ring
    have hbr : ‖bracket24 ℓ (imagAxis t ht) τ‖
        ≤ ‖WFun (imagAxis t ht) * Bprimefun ℓ (imagAxis t ht) τ‖
          + ‖(E10Fun (imagAxis t ht) / DeltaFun (imagAxis t ht))
              * (UFun (imagAxis t ht) ^ 2 - VFun (imagAxis t ht) ^ 2)
              * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
          + ‖(3456:ℂ) * DeltaFun τ * (E14Fun (imagAxis t ht) / DeltaFun (imagAxis t ht))
              * ℓ.L (imagAxis t ht)‖ := by
      rw [Work.Residues.bracket24, ← Work.Residues.Bprimefun_eq]
      exact kwp_norm_add_sub3_le _ _ _
    have htarget : ‖bracket24 ℓ (imagAxis t ht) τ‖
        ≤ (CW * KB * (1 + CJ) + CE * CU * KP + 3456 * CD * CF * CLz + 1)
            * (1 + N) * (1 + t) ^ max NW (max NU 1) * E * TT ^ 2 := by
      have hA : CW * KB * (1 + CJ) * (1 + N) * (1 + t) ^ NW * E * TT ^ 2
          ≤ CW * KB * (1 + CJ) * (1 + N) * (1 + t) ^ max NW (max NU 1) * E * TT ^ 2 := by
        have h6 : (0:ℝ) ≤ CW * KB * (1 + CJ) * (1 + N) * E * TT ^ 2 := by positivity
        have h7 : NW ≤ max NW (max NU 1) := le_max_left _ _
        calc CW * KB * (1 + CJ) * (1 + N) * (1 + t) ^ NW * E * TT ^ 2
            = (1 + t) ^ NW * (CW * KB * (1 + CJ) * (1 + N) * E * TT ^ 2) := by ring
          _ ≤ (1 + t) ^ max NW (max NU 1) * (CW * KB * (1 + CJ) * (1 + N) * E * TT ^ 2) :=
              mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hS1 h7) h6
          _ = CW * KB * (1 + CJ) * (1 + N) * (1 + t) ^ max NW (max NU 1) * E * TT ^ 2 := by ring
      have hB : CE * CU * KP * (1 + N) * (1 + t) ^ NU * E * TT ^ 2
          ≤ CE * CU * KP * (1 + N) * (1 + t) ^ max NW (max NU 1) * E * TT ^ 2 := by
        have h6 : (0:ℝ) ≤ CE * CU * KP * (1 + N) * E * TT ^ 2 := by positivity
        have h7 : NU ≤ max NW (max NU 1) := le_trans (le_max_left _ _) (le_max_right _ _)
        calc CE * CU * KP * (1 + N) * (1 + t) ^ NU * E * TT ^ 2
            = (1 + t) ^ NU * (CE * CU * KP * (1 + N) * E * TT ^ 2) := by ring
          _ ≤ (1 + t) ^ max NW (max NU 1) * (CE * CU * KP * (1 + N) * E * TT ^ 2) :=
              mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hS1 h7) h6
          _ = CE * CU * KP * (1 + N) * (1 + t) ^ max NW (max NU 1) * E * TT ^ 2 := by ring
      have hC : 3456 * CD * CF * CLz * (1 + N) * (1 + t) * E * TT ^ 2
          ≤ 3456 * CD * CF * CLz * (1 + N) * (1 + t) ^ max NW (max NU 1) * E * TT ^ 2 := by
        have h6 : (0:ℝ) ≤ 3456 * CD * CF * CLz * (1 + N) * E * TT ^ 2 := by positivity
        have h7 : (1:ℝ) ≤ max NW (max NU 1) := by
          have h8 : (1:ℝ) ≤ max NU 1 := le_max_right _ _
          exact le_trans h8 (le_max_right _ _)
        have h8 : (1 + t) ^ (1:ℝ) ≤ (1 + t) ^ max NW (max NU 1) :=
          Real.rpow_le_rpow_of_exponent_le hS1 h7
        rw [Real.rpow_one] at h8
        calc 3456 * CD * CF * CLz * (1 + N) * (1 + t) * E * TT ^ 2
            = (1 + t) * (3456 * CD * CF * CLz * (1 + N) * E * TT ^ 2) := by ring
          _ ≤ (1 + t) ^ max NW (max NU 1) * (3456 * CD * CF * CLz * (1 + N) * E * TT ^ 2) :=
              mul_le_mul_of_nonneg_right h8 h6
          _ = 3456 * CD * CF * CLz * (1 + N) * (1 + t) ^ max NW (max NU 1) * E * TT ^ 2 := by ring
      have hfirst := le_trans tA hA
      have hsecond := le_trans tB hB
      have hthird := le_trans tC hC
      have h := add_le_add (add_le_add hfirst hsecond) hthird
      refine le_trans (le_trans hbr h) ?_
      calc CW * KB * (1 + CJ) * (1 + N) * (1 + t) ^ max NW (max NU 1) * E * TT ^ 2
            + CE * CU * KP * (1 + N) * (1 + t) ^ max NW (max NU 1) * E * TT ^ 2
            + 3456 * CD * CF * CLz * (1 + N) * (1 + t) ^ max NW (max NU 1) * E * TT ^ 2
          = (CW * KB * (1 + CJ) + CE * CU * KP + 3456 * CD * CF * CLz)
              * (1 + N) * (1 + t) ^ max NW (max NU 1) * E * TT ^ 2 := by ring
        _ ≤ (CW * KB * (1 + CJ) + CE * CU * KP + 3456 * CD * CF * CLz + 1)
              * (1 + N) * (1 + t) ^ max NW (max NU 1) * E * TT ^ 2 := by
            have h6 : (0:ℝ) ≤ (1 + N) * (1 + t) ^ max NW (max NU 1) * E * TT ^ 2 := by positivity
            nlinarith [h6]
    have hgoal : (CW * KB * (1 + CJ) + CE * CU * KP + 3456 * CD * CF * CLz + 1)
          * (1 + ‖(τ : ℂ)‖) * (1 + t) ^ max NW (max NU 1) * Real.exp (2 * Real.pi * t)
          * (tpar τ) ^ 2
        = (CW * KB * (1 + CJ) + CE * CU * KP + 3456 * CD * CF * CLz + 1)
          * (1 + N) * (1 + t) ^ max NW (max NU 1) * E * TT ^ 2 := by
      rw [hN, hE, hTT]
    rw [hgoal]
    exact htarget



/-! ## `K_-^{(24)}` and `K_+^{(24)}` are polynomially bounded on the window -/

/-- `(e^{2πt} tpar τ²)² ≤ 1` for `t ≤ Im τ`. -/
lemma kwp_QE_sq_le_one {τ : ℍ} {t : ℝ} (ht : t ≤ τ.im) :
    ((Work.Residues.tpar τ) ^ 2 * Real.exp (2 * Real.pi * t)) ^ 2 ≤ 1 := by
  have h1 : (Work.Residues.tpar τ) ^ 2 = Real.exp (-(2 * Real.pi * τ.im)) :=
    Work.Residues.tpar_pow_two τ
  have h2 : Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * t)
      = Real.exp (2 * Real.pi * t - 2 * Real.pi * τ.im) := by
    rw [← Real.exp_add]; ring_nf
  calc ((Work.Residues.tpar τ) ^ 2 * Real.exp (2 * Real.pi * t)) ^ 2
      = (Real.exp (2 * Real.pi * t - 2 * Real.pi * τ.im)) ^ 2 := by rw [h1, h2]
    _ = Real.exp (2 * (2 * Real.pi * t - 2 * Real.pi * τ.im)) := by
        rw [pow_two, ← Real.exp_add]; ring_nf
    _ ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [Real.pi_pos, ht]

set_option maxHeartbeats 4000000 in
open Work.Residues in
lemma kwp_KMinus24_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ H C N M : ℝ, 0 ≤ H ∧ 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t), H ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 →
        ‖KMinus ℓ 24 τ (imagAxis t ht)‖ ≤ C * (scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨HB, KB, MB, hHB, hKB, hMB, hbr⟩ := kwp_bracket24_sharp ℓ
  obtain ⟨Hk, Kk, hKk, hHk, hk⟩ := Work.Residues.kpre_inv_axis_bound
    (fun τ hτ => Work.Asymptotics.DeltaFun_upper_sharp τ hτ)
    (fun t ht ht1 => Work.Asymptotics.DeltaFun_imagAxis_lower_sharp t ht ht1)
    (fun τ hτ => Work.Asymptotics.E4Fun_upper_half τ hτ)
  refine ⟨max HB Hk, (KB * Kk + 1) * 2, 1, MB, le_max_of_le_left hHB,
    by have h1 : (0:ℝ) < KB * Kk := mul_pos hKB hKk; linarith, by norm_num, hMB, ?_⟩
  intro τ t ht hτ ht1 htle
  have hτB : HB ≤ τ.im := le_trans (le_max_left _ _) hτ
  have hτk : Hk ≤ τ.im := le_trans (le_max_right _ _) hτ
  have hτt : t ≤ τ.im := by linarith
  have hbr' := hbr τ t ht hτB ht1
  have hk' := hk τ t ht hτk ht1 htle
  set E : ℝ := Real.exp (2 * Real.pi * t) with hE
  set Q : ℝ := (Work.Residues.tpar τ) ^ 2 with hQ
  have hQ0 : (0:ℝ) < Q := by
    rw [hQ, Work.Residues.tpar_pow_two]; positivity
  have hE0 : (0:ℝ) < E := by rw [hE]; positivity
  have hQEsq : (Q * E) ^ 2 ≤ 1 := by
    have h1 := kwp_QE_sq_le_one (τ := τ) (t := t) hτt
    have h2 : (Q * E) ^ 2 = ((Work.Residues.tpar τ) ^ 2 * Real.exp (2 * Real.pi * t)) ^ 2 := by
      rw [hQ, hE]
    rw [h2]; exact h1
  have hQE : Q * E ≤ 1 := by
    nlinarith [hQEsq, hQ0, hE0, mul_nonneg hQ0.le hE0.le]
  have hKm : KMinus ℓ 24 τ (imagAxis t ht)
      = (kpre (imagAxis t ht) τ)⁻¹ * bracket24 ℓ (imagAxis t ht) τ := by
    rw [Work.Asymptotics.Compact.KMinus24_eq ℓ τ (imagAxis t ht)]
    congr 1
    show Work.Residues.bracket24e ℓ (imagAxis t ht) τ = Work.Residues.bracket24 ℓ (imagAxis t ht) τ
    exact (Work.Residues.bracket24_eq ℓ (imagAxis t ht) τ).symm
  rw [hKm]
  have h1 : ‖bracket24 ℓ (imagAxis t ht) τ‖
      ≤ KB * (1 + ‖(τ : ℂ)‖) * (1 + t) ^ MB * E * Q := by
    rw [hQ, hE]; exact hbr'
  have h2 : ‖(kpre (imagAxis t ht) τ)⁻¹‖ ≤ Kk * E * Q := by
    rw [hQ, hE, Work.Residues.tpar_pow_two]; exact hk'
  have hscale : (1 + ‖(τ : ℂ)‖) ≤ 2 * scale τ := by
    have h1 := Work.Kernels.one_le_scale τ
    have h2 := Work.Kernels.coe_norm_le_scale τ
    linarith
  rw [norm_mul]
  calc ‖(kpre (imagAxis t ht) τ)⁻¹‖ * ‖bracket24 ℓ (imagAxis t ht) τ‖
      ≤ (Kk * E * Q) * (KB * (1 + ‖(τ : ℂ)‖) * (1 + t) ^ MB * E * Q) :=
        mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
    _ = KB * Kk * (1 + ‖(τ : ℂ)‖) * (1 + t) ^ MB * (Q * E) ^ 2 := by ring
    _ ≤ KB * Kk * (1 + ‖(τ : ℂ)‖) * (1 + t) ^ MB * 1 := by
        have h5 : (0:ℝ) ≤ KB * Kk * (1 + ‖(τ : ℂ)‖) * (1 + t) ^ MB := by
          have h7 := norm_nonneg (τ : ℂ)
          have h8 : (0:ℝ) ≤ (1 + t) ^ MB := Real.rpow_nonneg (by linarith) _
          positivity
        nlinarith [hQEsq, h5]
    _ ≤ (KB * Kk + 1) * (2 * scale τ) * (1 + t) ^ MB := by
        have h6 : (0:ℝ) ≤ (1 + t) ^ MB := Real.rpow_nonneg (by linarith) _
        have h7 : KB * Kk ≤ KB * Kk + 1 := by linarith
        have h8 : (0:ℝ) ≤ KB * Kk := mul_nonneg hKB.le hKk.le
        have hA : KB * Kk * (1 + ‖(τ : ℂ)‖) * (1 + t) ^ MB
            ≤ (KB * Kk + 1) * (1 + ‖(τ : ℂ)‖) * (1 + t) ^ MB := by
          have h10 : (0:ℝ) ≤ (1 + ‖(τ : ℂ)‖) * (1 + t) ^ MB := by
            have h11 : (0:ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by
              have := norm_nonneg (τ : ℂ); linarith
            exact mul_nonneg h11 h6
          calc KB * Kk * (1 + ‖(τ : ℂ)‖) * (1 + t) ^ MB
              = (KB * Kk) * ((1 + ‖(τ : ℂ)‖) * (1 + t) ^ MB) := by ring
            _ ≤ (KB * Kk + 1) * ((1 + ‖(τ : ℂ)‖) * (1 + t) ^ MB) :=
                mul_le_mul_of_nonneg_right (by linarith) h10
            _ = (KB * Kk + 1) * (1 + ‖(τ : ℂ)‖) * (1 + t) ^ MB := by ring
        have hB : (KB * Kk + 1) * (1 + ‖(τ : ℂ)‖) * (1 + t) ^ MB
            ≤ (KB * Kk + 1) * (2 * scale τ) * (1 + t) ^ MB := by
          have h10 : (0:ℝ) ≤ KB * Kk + 1 := by linarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale h10) h6
        linarith [hA, hB]
    _ = ((KB * Kk + 1) * 2) * (scale τ) ^ (1:ℝ) * (1 + t) ^ MB := by
        rw [Real.rpow_one]; ring

/-! ## The `K_+^{(24)}` bound -/

set_option maxHeartbeats 4000000 in
lemma kwp_KPlus24_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t), Work.Asymptotics.Funnel τ → 1 ≤ t →
        t ≤ τ.im - 1 →
        ‖KPlus 24 τ (imagAxis t ht)‖ ≤ C * (scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨CR, hCR, hRb⟩ := kwp_R_bound
  obtain ⟨CB, hCB1, hCB⟩ := Work.Asymptotics.Compact.imagAxis_cusp_bounds
  obtain ⟨CE2, hCE2, hE2b⟩ := Work.Asymptotics.E2Fun_bound
  obtain ⟨CE6, hCE6, hE6b⟩ := Work.Asymptotics.E6Fun_bound
  set CW : ℝ := (1 / 16 - 27 / 4 * Real.exp (-(2 * Real.pi)))⁻¹ with hCW
  have hCW0 : (0:ℝ) < CW := by rw [hCW]; exact inv_pos.mpr Work.Residues.kpre_axis_const_pos
  have hCE2n : (0:ℝ) ≤ CE2 := hCE2.le
  have hCE6n : (0:ℝ) ≤ CE6 := hCE6.le
  set KY0 : ℝ := CR + 17280 * (CE2 + 3)
      + 1728 * (CE2 ^ 2 + 6 / Real.pi * CE2) * (3 / 2 * CE6) * CW with hKY0
  set KY1 : ℝ := 6912 * (CE2 + 3) * CW with hKY1
  set KY2 : ℝ := CR + 1728 * (27 / 8 * CE6) * CW + 24192 * (CE2 + 3) with hKY2
  set KD : ℝ := (2 / (36 * 1728 * (Real.pi : ℝ) ^ (-2 : ℤ))) with hKD
  have hKD0 : (0:ℝ) < KD := by rw [hKD]; positivity
  have hKY0n : (0:ℝ) ≤ KY0 := by
    rw [hKY0]; have h1 := hCR.le; have h2 := hCW0.le; positivity
  have hKY1n : (0:ℝ) ≤ KY1 := by
    rw [hKY1]; have h1 := hCW0.le; positivity
  have hKY2n : (0:ℝ) ≤ KY2 := by
    rw [hKY2]; have h1 := hCR.le; have h2 := hCW0.le; positivity
  set KK : ℝ := KD * ((3 / 2) * KY0 + 2 * CB ^ 4 * KY1 + CB * KY2) with hKK
  have hKK0 : (0:ℝ) ≤ KK := by
    rw [hKK]
    refine mul_nonneg hKD0.le ?_
    have h1 : (0:ℝ) ≤ (3 / 2) * KY0 := by linarith [hKY0n]
    have h2 : (0:ℝ) ≤ 2 * CB ^ 4 * KY1 := by
      have h3 : (0:ℝ) ≤ CB ^ 4 := by
        have h4 : (0:ℝ) ≤ CB := by linarith
        positivity
      exact mul_nonneg (mul_nonneg (by norm_num) h3) hKY1n
    have h3 : (0:ℝ) ≤ CB * KY2 := by
      have h4 : (0:ℝ) ≤ CB := by linarith
      exact mul_nonneg h4 hKY2n
    linarith
  refine ⟨2 * KK + 1, 1, 2, by linarith, by norm_num, by norm_num, ?_⟩
  intro τ t ht hF ht1 htle
  have hτ1 : 1 ≤ τ.im := le_trans (by norm_num) hF.2
  have hτ2 : 2 ≤ τ.im := hF.2
  have hτt : t ≤ τ.im := by linarith
  set W : ℂ := (jInvariantFun τ - jInvariantFun (imagAxis t ht))⁻¹ with hW
  set N : ℝ := ‖(τ : ℂ)‖ with hN
  set Q : ℝ := (Work.Residues.tpar τ) ^ 2 with hQ
  set E : ℝ := Real.exp (2 * Real.pi * t) with hE
  have hQ0 : (0:ℝ) < Q := by rw [hQ, Work.Residues.tpar_pow_two]; positivity
  have hE0 : (0:ℝ) < E := by rw [hE]; positivity
  have hN0 : (0:ℝ) ≤ 1 + N := by rw [hN]; have := norm_nonneg (τ : ℂ); linarith
  have hCBn : (0:ℝ) ≤ CB := by linarith
  have hT0 : (0:ℝ) ≤ (1 + t) ^ 2 := by positivity
  have hQEsq : (Q * E) ^ 2 ≤ 1 := by
    have h1 := kwp_QE_sq_le_one (τ := τ) (t := t) hτt
    have h2 : (Q * E) ^ 2 = ((Work.Residues.tpar τ) ^ 2 * Real.exp (2 * Real.pi * t)) ^ 2 := by
      rw [hQ, hE]
    rw [h2]; exact h1
  have hQE : Q * E ≤ 1 := by nlinarith [hQEsq, hQ0, hE0, mul_nonneg hQ0.le hE0.le]
  have hQ2E2 : Q ^ 2 * E ^ 2 ≤ 1 := by
    have h1 := kwp_QE_sq_le_one (τ := τ) (t := t) hτt
    have h2 : Q ^ 2 * E ^ 2 = ((Work.Residues.tpar τ) ^ 2 * Real.exp (2 * Real.pi * t)) ^ 2 := by
      rw [hQ, hE, mul_pow]
    rw [h2]; exact h1
  have hscale : (1 + N) ≤ 2 * scale τ := by
    rw [hN]
    have h2 := Work.Kernels.one_le_scale τ
    have h3 := Work.Kernels.coe_norm_le_scale τ
    linarith
  have hqnorm : ‖qParamFun τ‖ = Q := by
    rw [Work.Asymptotics.norm_qParamFun, hQ, Work.Residues.tpar_pow_two]
  -- τ-side atoms
  have hE4τ : ‖E4Fun τ‖ ≤ 3 / 2 := Work.Asymptotics.E4Fun_upper_half τ hτ1
  have hE6τ : ‖E6Fun τ‖ ≤ CE6 := hE6b τ hτ1
  have hΔτ : ‖DeltaFun τ‖ ≤ 2 * Q := by
    rw [hQ, Work.Residues.tpar_pow_two]; exact Work.Asymptotics.DeltaFun_upper_sharp τ hτ1
  have hphi0 : ‖phiVec τ 0‖ ≤ 1 + N := by
    rw [kwp_phiVec_zero, hN]
    have := norm_nonneg (τ : ℂ); linarith
  have hphi1 : ‖phiVec τ 1‖ ≤ (CE2 + 3) * (1 + N) := by
    have h := kwp_norm_phi1_bound (hE2b τ hτ1)
    rw [kwp_phiVec_one]
    rw [hN]
    nlinarith [h, norm_nonneg (τ : ℂ), hCE2n]
  have hphi2 : ‖phiVec τ 2‖ ≤ (CE2 ^ 2 + 6 / Real.pi * CE2) * (1 + N) := by
    have h := kwp_norm_phi2_bound (hE2b τ hτ1)
    rw [kwp_phiVec_two]
    refine le_trans h ?_
    have h6 : CE2 ^ 2 * ‖(τ : ℂ)‖ ≤ (CE2 ^ 2 + 6 / Real.pi * CE2) * ‖(τ : ℂ)‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have h7 : (0:ℝ) ≤ 6 / Real.pi * CE2 := mul_nonneg (by positivity) hCE2n
      linarith
    have h7 : (0:ℝ) ≤ CE2 ^ 2 + 6 / Real.pi * CE2 := by
      have h8 : (0:ℝ) ≤ 6 / Real.pi * CE2 := mul_nonneg (by positivity) hCE2n
      have h9 : (0:ℝ) ≤ CE2 ^ 2 := by positivity
      linarith
    have h8 : (0:ℝ) ≤ 6 / Real.pi * CE2 := mul_nonneg (by positivity) hCE2n
    calc CE2 ^ 2 * ‖(τ : ℂ)‖ + 6 / Real.pi * CE2
        ≤ (CE2 ^ 2 + 6 / Real.pi * CE2) * ‖(τ : ℂ)‖ + 6 / Real.pi * CE2 := by linarith [h6]
      _ ≤ (CE2 ^ 2 + 6 / Real.pi * CE2) * (1 + ‖(τ : ℂ)‖) := by
          nlinarith [h7, h8, norm_nonneg (τ : ℂ)]
      _ = (CE2 ^ 2 + 6 / Real.pi * CE2) * (1 + N) := by rw [hN]
  have hWb : ‖W‖ ≤ CW * Q := by
    rw [hW, hCW, hQ, Work.Residues.tpar_pow_two]
    exact kwp_Jinv_bound τ t ht hτ2 ht1 htle
  have hE10τ : ‖E10Fun τ‖ ≤ 3 / 2 * CE6 := by
    rw [show E10Fun τ = E4Fun τ * E6Fun τ from rfl, norm_mul]
    exact mul_le_mul hE4τ hE6τ (norm_nonneg _) (by linarith)
  have hE14τ : ‖E14Fun τ‖ ≤ 27 / 8 * CE6 := by
    rw [show E14Fun τ = E4Fun τ ^ 2 * E6Fun τ from rfl, norm_mul, norm_pow]
    have h2 : ‖E4Fun τ‖ ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hE4τ 2
    have h3 : ‖E4Fun τ‖ ^ 2 * ‖E6Fun τ‖ ≤ (3 / 2 : ℝ) ^ 2 * CE6 :=
      mul_le_mul h2 hE6τ (norm_nonneg _) (by norm_num)
    have h4 : ((3:ℝ) / 2) ^ 2 * CE6 ≤ 27 / 8 * CE6 :=
      mul_le_mul_of_nonneg_right (by norm_num) hCE6n
    linarith
  -- nonnegativity facts used repeatedly
  have hN3 : (0:ℝ) ≤ CE2 + 3 := by linarith
  have hN4 : (0:ℝ) ≤ CE2 ^ 2 + 6 / Real.pi * CE2 := by
    have h8 : (0:ℝ) ≤ 6 / Real.pi * CE2 := mul_nonneg (by positivity) hCE2n
    have h9 : (0:ℝ) ≤ CE2 ^ 2 := by positivity
    linarith
  have hN5 : (0:ℝ) ≤ 27 / 8 * CE6 := by positivity
  have hN6 : (0:ℝ) ≤ 3 / 2 * CE6 := by positivity
  have hp1n : (0:ℝ) ≤ (CE2 + 3) * (1 + N) := mul_nonneg hN3 hN0
  have hp2n : (0:ℝ) ≤ (CE2 ^ 2 + 6 / Real.pi * CE2) * (1 + N) := mul_nonneg hN4 hN0
  have hCB4n : (0:ℝ) ≤ CB ^ 4 := by positivity
  have hQn : (0:ℝ) ≤ Q := hQ0.le
  have hEn : (0:ℝ) ≤ E := hE0.le
  have hWn : (0:ℝ) ≤ ‖W‖ := norm_nonneg _
  -- the three `Y`-bounds
  have hY0 : ‖kwpY0 τ (imagAxis t ht)‖ ≤ KY0 * (1 + N) * Q := by
    rw [kwpY0_eq τ (imagAxis t ht), hKY0]
    have hR : ‖(6 : ℂ) * (τ : ℂ) * E14Fun τ - (12 : ℂ) * phiVec τ 1 * E4Fun τ ^ 3
        + (6 : ℂ) * phiVec τ 2 * E10Fun τ‖ ≤ CR * (1 + N) * Q := by
      have h0 := hRb τ hF
      rw [hqnorm, ← hN] at h0
      exact h0
    have hA : ‖(8640:ℂ) * phiVec τ 1 * DeltaFun τ‖ ≤ 17280 * (CE2 + 3) * ((1 + N) * Q) := by
      rw [show (8640:ℂ) * phiVec τ 1 * DeltaFun τ = (8640:ℂ) * (phiVec τ 1 * DeltaFun τ) by ring,
        norm_mul, Complex.norm_ofNat, norm_mul]
      have h1 : (CE2 + 3) * (1 + N) * (2 * Q) = (CE2 + 3) * ((1 + N) * (2 * Q)) := by ring
      have h2 : ‖phiVec τ 1‖ * ‖DeltaFun τ‖ ≤ (CE2 + 3) * ((1 + N) * (2 * Q)) := by
        rw [← h1]
        exact mul_le_mul hphi1 hΔτ (norm_nonneg _) hp1n
      calc 8640 * (‖phiVec τ 1‖ * ‖DeltaFun τ‖)
          ≤ 8640 * ((CE2 + 3) * ((1 + N) * (2 * Q))) := by linarith [h2]
        _ = 17280 * (CE2 + 3) * ((1 + N) * Q) := by ring
    have hB : ‖(1728:ℂ) * phiVec τ 2 * E10Fun τ * W‖
        ≤ 1728 * (CE2 ^ 2 + 6 / Real.pi * CE2) * (3 / 2 * CE6) * CW * ((1 + N) * Q) := by
      rw [show (1728:ℂ) * phiVec τ 2 * E10Fun τ * W
          = (1728:ℂ) * ((phiVec τ 2 * E10Fun τ) * W) by ring,
        norm_mul, Complex.norm_ofNat, norm_mul, norm_mul]
      have h2 : ‖phiVec τ 2‖ * ‖E10Fun τ‖ ≤ ((CE2 ^ 2 + 6 / Real.pi * CE2) * (1 + N))
          * (3 / 2 * CE6) := mul_le_mul hphi2 hE10τ (norm_nonneg _) hp2n
      have h3 : (‖phiVec τ 2‖ * ‖E10Fun τ‖) * ‖W‖
          ≤ (((CE2 ^ 2 + 6 / Real.pi * CE2) * (1 + N)) * (3 / 2 * CE6)) * (CW * Q) :=
        mul_le_mul h2 hWb (norm_nonneg _) (mul_nonneg hp2n hN6)
      calc 1728 * ((‖phiVec τ 2‖ * ‖E10Fun τ‖) * ‖W‖)
          ≤ 1728 * ((((CE2 ^ 2 + 6 / Real.pi * CE2) * (1 + N)) * (3 / 2 * CE6))
              * (CW * Q)) := by linarith [h3]
        _ = 1728 * (CE2 ^ 2 + 6 / Real.pi * CE2) * (3 / 2 * CE6) * CW * ((1 + N) * Q) := by ring
    have h7 : (0:ℝ) ≤ (1 + N) * Q := mul_nonneg hN0 hQn
    have h9 : (0:ℝ) ≤ 17280 * (CE2 + 3) := by positivity
    have h10 : (0:ℝ) ≤ 1728 * (CE2 ^ 2 + 6 / Real.pi * CE2) * (3 / 2 * CE6) * CW :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hN4) hN6) hCW0.le
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add hR (le_trans (norm_add_le _ _) (add_le_add hA hB))) ?_
    have heq : CR * (1 + N) * Q
          + (17280 * (CE2 + 3) * ((1 + N) * Q)
            + 1728 * (CE2 ^ 2 + 6 / Real.pi * CE2) * (3 / 2 * CE6) * CW * ((1 + N) * Q))
        = (CR + 17280 * (CE2 + 3)
            + 1728 * (CE2 ^ 2 + 6 / Real.pi * CE2) * (3 / 2 * CE6) * CW) * ((1 + N) * Q) := by
      ring
    linarith [heq.le, heq.ge]
  have hY1 : ‖kwpY1 τ (imagAxis t ht)‖ ≤ KY1 * (1 + N) * (Q ^ 2) := by
    rw [kwpY1_eq τ (imagAxis t ht), hKY1]
    rw [show -3456 * phiVec τ 1 * DeltaFun τ * W
        = -((3456:ℂ) * (phiVec τ 1 * (DeltaFun τ * W))) by ring]
    simp only [norm_neg, norm_mul, Complex.norm_ofNat]
    have h1 : ‖phiVec τ 1‖ * (‖DeltaFun τ‖ * ‖W‖)
        ≤ (CE2 + 3) * (1 + N) * ((2 * Q) * (CW * Q)) := by
      have h2 : ‖DeltaFun τ‖ * ‖W‖ ≤ (2 * Q) * (CW * Q) :=
        mul_le_mul hΔτ hWb (norm_nonneg _) (mul_nonneg (by norm_num) hQn)
      have h3 : ‖phiVec τ 1‖ * (‖DeltaFun τ‖ * ‖W‖)
          ≤ ((CE2 + 3) * (1 + N)) * ((2 * Q) * (CW * Q)) :=
        mul_le_mul hphi1 h2 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hp1n
      calc ‖phiVec τ 1‖ * (‖DeltaFun τ‖ * ‖W‖)
          ≤ ((CE2 + 3) * (1 + N)) * ((2 * Q) * (CW * Q)) := h3
        _ = (CE2 + 3) * (1 + N) * ((2 * Q) * (CW * Q)) := by ring
    calc 3456 * (‖phiVec τ 1‖ * (‖DeltaFun τ‖ * ‖W‖))
        ≤ 3456 * ((CE2 + 3) * (1 + N) * ((2 * Q) * (CW * Q))) := by linarith [h1]
      _ = 6912 * (CE2 + 3) * CW * (1 + N) * (Q ^ 2) := by ring
  have hY2 : ‖kwpY2 τ (imagAxis t ht)‖ ≤ KY2 * (1 + N) * Q := by
    rw [kwpY2_eq τ (imagAxis t ht), hKY2]
    have hA : ‖-((6 : ℂ) * (τ : ℂ) * E14Fun τ - (12 : ℂ) * phiVec τ 1 * E4Fun τ ^ 3
        + (6 : ℂ) * phiVec τ 2 * E10Fun τ)‖ ≤ CR * (1 + N) * Q := by
      rw [norm_neg]
      have h0 := hRb τ hF
      rw [hqnorm, ← hN] at h0
      exact h0
    have hB : ‖(1728:ℂ) * phiVec τ 0 * E14Fun τ * W - 12096 * phiVec τ 1 * DeltaFun τ‖
        ≤ (1728 * (27 / 8 * CE6) * CW + 24192 * (CE2 + 3)) * ((1 + N) * Q) := by
      have h1 : ‖(1728:ℂ) * phiVec τ 0 * E14Fun τ * W‖
          ≤ 1728 * (27 / 8 * CE6) * CW * ((1 + N) * Q) := by
        rw [show (1728:ℂ) * phiVec τ 0 * E14Fun τ * W
            = (1728:ℂ) * ((phiVec τ 0 * E14Fun τ) * W) by ring,
          norm_mul, Complex.norm_ofNat, norm_mul, norm_mul]
        have h2 : ‖phiVec τ 0‖ * ‖E14Fun τ‖ ≤ (1 + N) * (27 / 8 * CE6) :=
          mul_le_mul hphi0 hE14τ (norm_nonneg _) hN0
        have h3 : (‖phiVec τ 0‖ * ‖E14Fun τ‖) * ‖W‖ ≤ ((1 + N) * (27 / 8 * CE6)) * (CW * Q) :=
          mul_le_mul h2 hWb (norm_nonneg _) (mul_nonneg hN0 hN5)
        calc 1728 * ((‖phiVec τ 0‖ * ‖E14Fun τ‖) * ‖W‖)
            ≤ 1728 * (((1 + N) * (27 / 8 * CE6)) * (CW * Q)) := by linarith [h3]
          _ = 1728 * (27 / 8 * CE6) * CW * ((1 + N) * Q) := by ring
      have h2 : ‖(12096:ℂ) * phiVec τ 1 * DeltaFun τ‖ ≤ 24192 * (CE2 + 3) * ((1 + N) * Q) := by
        rw [show (12096:ℂ) * phiVec τ 1 * DeltaFun τ
            = (12096:ℂ) * (phiVec τ 1 * DeltaFun τ) by ring, norm_mul, Complex.norm_ofNat,
          norm_mul]
        have h3 : ‖phiVec τ 1‖ * ‖DeltaFun τ‖ ≤ (CE2 + 3) * ((1 + N) * (2 * Q)) := by
          have h4 : (CE2 + 3) * (1 + N) * (2 * Q) = (CE2 + 3) * ((1 + N) * (2 * Q)) := by ring
          rw [← h4]
          exact mul_le_mul hphi1 hΔτ (norm_nonneg _) hp1n
        calc 12096 * (‖phiVec τ 1‖ * ‖DeltaFun τ‖)
            ≤ 12096 * ((CE2 + 3) * ((1 + N) * (2 * Q))) := by linarith [h3]
          _ = 24192 * (CE2 + 3) * ((1 + N) * Q) := by ring
      refine le_trans (norm_sub_le _ _) ?_
      have h7 : (0:ℝ) ≤ (1 + N) * Q := mul_nonneg hN0 hQn
      have hsum : 1728 * (27 / 8 * CE6) * CW * ((1 + N) * Q)
            + 24192 * (CE2 + 3) * ((1 + N) * Q)
          = (1728 * (27 / 8 * CE6) * CW + 24192 * (CE2 + 3)) * ((1 + N) * Q) := by ring
      linarith [h1, h2, hsum.le, hsum.ge]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add hA hB) ?_
    have h7 : (0:ℝ) ≤ (1 + N) * Q := mul_nonneg hN0 hQn
    have h9 : (0:ℝ) ≤ 1728 * (27 / 8 * CE6) * CW :=
      mul_nonneg (mul_nonneg (by norm_num) hN5) hCW0.le
    have h10 : (0:ℝ) ≤ 24192 * (CE2 + 3) := by positivity
    have heq : CR * (1 + N) * Q
          + (1728 * (27 / 8 * CE6) * CW + 24192 * (CE2 + 3)) * ((1 + N) * Q)
        = (CR + 1728 * (27 / 8 * CE6) * CW + 24192 * (CE2 + 3)) * ((1 + N) * Q) := by ring
    linarith [heq.le, heq.ge]
  -- z-side atoms
  obtain ⟨_, _, _, _, _, hE4zb, hE6zb, hp1b, hp2b⟩ := hCB t ht ht1
  have hE4z3 : ‖E4Fun (imagAxis t ht)‖ ≤ 3 / 2 :=
    Work.Asymptotics.E4Fun_upper_half (imagAxis t ht) (by rw [kwp_imagAxis_im t ht]; exact ht1)
  have hphit0 : ‖phitVec (imagAxis t ht) 0‖ ≤ (1 + t) ^ 2 := by
    rw [kwp_phitVec_zero, norm_pow, kwp_imagAxis_norm t ht]
    have h1 : (1:ℝ) ≤ 1 + t := by linarith
    nlinarith [h1]
  have hDinv : ‖(((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
      * DeltaFun (imagAxis t ht)))⁻¹‖ ≤ KD * E := by
    rw [hKD, hE]
    rw [norm_inv]
    have h1 : ‖(36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
        * DeltaFun (imagAxis t ht)‖
        = 36 * 1728 * (Real.pi : ℝ) ^ (-2 : ℤ) * ‖DeltaFun (imagAxis t ht)‖ := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
      rw [show ‖c1728‖ = 1728 from by simp [c1728]]
      rw [show ‖(Real.pi : ℂ) ^ (-2 : ℤ)‖ = (Real.pi : ℝ) ^ (-2 : ℤ) from by
        rw [norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]]
      rw [Complex.norm_I, mul_one]
    rw [h1]
    have hDp : (0:ℝ) < ‖DeltaFun (imagAxis t ht)‖ :=
      norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)
    have hca : (0:ℝ) < 36 * 1728 * (Real.pi : ℝ) ^ (-2 : ℤ) * ‖DeltaFun (imagAxis t ht)‖ := by
      have h1 : (0:ℝ) < 36 * 1728 * (Real.pi : ℝ) ^ (-2 : ℤ) := by positivity
      exact mul_pos h1 hDp
    have hcb : (0:ℝ) < 2 / (36 * 1728 * (Real.pi : ℝ) ^ (-2 : ℤ)) * Real.exp (2 * Real.pi * t) := by
      have h2 : (0:ℝ) < 2 / (36 * 1728 * (Real.pi : ℝ) ^ (-2 : ℤ)) := by positivity
      exact mul_pos h2 (Real.exp_pos _)
    rw [inv_le_comm₀ hca hcb]
    rw [show ((2 / (36 * 1728 * (Real.pi : ℝ) ^ (-2 : ℤ))) * Real.exp (2 * Real.pi * t))⁻¹
        = (36 * 1728 * (Real.pi : ℝ) ^ (-2 : ℤ)) / 2 * Real.exp (-(2 * Real.pi * t)) from by
      rw [_root_.mul_inv_rev, inv_div, ← Real.exp_neg]; ring]
    have hlow := Work.Asymptotics.DeltaFun_imagAxis_lower_sharp t ht ht1
    calc (36 * 1728 * (Real.pi : ℝ) ^ (-2 : ℤ)) / 2 * Real.exp (-(2 * Real.pi * t))
        = (36 * 1728 * (Real.pi : ℝ) ^ (-2 : ℤ))
            * ((1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * t))) := by ring
      _ ≤ 36 * 1728 * (Real.pi : ℝ) ^ (-2 : ℤ) * ‖DeltaFun (imagAxis t ht)‖ :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
  have hr : ‖E14Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)‖ ≤ CB ^ 3 * (2 * E) := by
    rw [div_eq_mul_inv, norm_mul, norm_inv]
    have hDinv2 : ‖DeltaFun (imagAxis t ht)‖⁻¹ ≤ 2 * E := by
      rw [hE]
      have h := kwp_invDelta_z t ht ht1
      rwa [norm_inv] at h
    have h1 : ‖E14Fun (imagAxis t ht)‖ ≤ CB ^ 3 := by
      rw [show E14Fun (imagAxis t ht) = E4Fun (imagAxis t ht) ^ 2 * E6Fun (imagAxis t ht)
        from rfl, norm_mul, norm_pow]
      have h2 : ‖E4Fun (imagAxis t ht)‖ ^ 2 ≤ CB ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg (E4Fun (imagAxis t ht))) hE4zb 2
      have h4 : (0:ℝ) ≤ ‖E6Fun (imagAxis t ht)‖ := norm_nonneg _
      have h5 : (0:ℝ) ≤ CB ^ 2 := by positivity
      calc ‖E4Fun (imagAxis t ht)‖ ^ 2 * ‖E6Fun (imagAxis t ht)‖ ≤ CB ^ 2 * CB :=
            mul_le_mul h2 hE6zb h4 h5
        _ = CB ^ 3 := by ring
    have h6 : (0:ℝ) ≤ ‖DeltaFun (imagAxis t ht)‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    have h7 : (0:ℝ) ≤ CB ^ 3 := by positivity
    exact mul_le_mul h1 hDinv2 h6 h7
  -- the three terms
  have hterm0 : ‖(((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
        * DeltaFun (imagAxis t ht)))⁻¹
      * (kwpY0 τ (imagAxis t ht) * (E4Fun (imagAxis t ht) * phitVec (imagAxis t ht) 0))‖
      ≤ (3 / 2) * KY0 * KD * (1 + N) * (1 + t) ^ 2 := by
    rw [norm_mul]
    have hz0 : ‖E4Fun (imagAxis t ht) * phitVec (imagAxis t ht) 0‖ ≤ (3 / 2) * (1 + t) ^ 2 := by
      rw [norm_mul]
      exact mul_le_mul hE4z3 hphit0 (norm_nonneg _) (by norm_num)
    have h1 : ‖kwpY0 τ (imagAxis t ht)
          * (E4Fun (imagAxis t ht) * phitVec (imagAxis t ht) 0)‖
        ≤ (KY0 * (1 + N) * Q) * ((3 / 2) * (1 + t) ^ 2) := by
      rw [norm_mul]
      exact mul_le_mul hY0 hz0 (norm_nonneg _) (mul_nonneg (mul_nonneg hKY0n hN0) hQn)
    have h2 : KD * E * ((KY0 * (1 + N) * Q) * ((3 / 2) * (1 + t) ^ 2))
        = (3 / 2) * KY0 * KD * (1 + N) * (1 + t) ^ 2 * (Q * E) := by ring
    have h3 : (0:ℝ) ≤ (3 / 2) * KY0 * KD * (1 + N) * (1 + t) ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKY0n) hKD0.le) hN0) hT0
    calc ‖(((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
            * DeltaFun (imagAxis t ht)))⁻¹‖
          * ‖kwpY0 τ (imagAxis t ht) * (E4Fun (imagAxis t ht) * phitVec (imagAxis t ht) 0)‖
        ≤ (KD * E) * ((KY0 * (1 + N) * Q) * ((3 / 2) * (1 + t) ^ 2)) :=
          mul_le_mul hDinv h1 (norm_nonneg _) (mul_nonneg hKD0.le hEn)
      _ = (3 / 2) * KY0 * KD * (1 + N) * (1 + t) ^ 2 * (Q * E) := h2
      _ ≤ (3 / 2) * KY0 * KD * (1 + N) * (1 + t) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hQE h3
      _ = (3 / 2) * KY0 * KD * (1 + N) * (1 + t) ^ 2 := by ring
  have hterm1 : ‖(((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
        * DeltaFun (imagAxis t ht)))⁻¹
      * (kwpY1 τ (imagAxis t ht)
          * ((E14Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)) * phitVec (imagAxis t ht) 1))‖
      ≤ 2 * CB ^ 4 * KY1 * KD * (1 + N) * (1 + t) ^ 2 := by
    rw [norm_mul]
    have hz1 : ‖(E14Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)) * phitVec (imagAxis t ht) 1‖
        ≤ (2 * CB ^ 4 * E) * (1 + t) ^ 2 := by
      rw [norm_mul]
      have h1 : ‖E14Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)‖ ≤ 2 * CB ^ 3 * E := by
        linarith [hr]
      have hCB3n : (0:ℝ) ≤ CB ^ 3 := by positivity
      have h4 : (0:ℝ) ≤ 2 * CB ^ 3 * E :=
        mul_nonneg (mul_nonneg (by norm_num) hCB3n) hEn
      calc ‖E14Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)‖
            * ‖phitVec (imagAxis t ht) 1‖
          ≤ (2 * CB ^ 3 * E) * (CB * (1 + t) ^ 2) :=
            mul_le_mul h1 hp1b (norm_nonneg _) h4
        _ = (2 * CB ^ 4 * E) * (1 + t) ^ 2 := by ring
    have h1 : ‖kwpY1 τ (imagAxis t ht)
          * ((E14Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)) * phitVec (imagAxis t ht) 1)‖
        ≤ (KY1 * (1 + N) * Q ^ 2) * ((2 * CB ^ 4 * E) * (1 + t) ^ 2) := by
      rw [norm_mul]
      have h5 : (0:ℝ) ≤ KY1 * (1 + N) * Q ^ 2 :=
        mul_nonneg (mul_nonneg hKY1n hN0) (pow_nonneg hQn 2)
      exact mul_le_mul hY1 hz1 (norm_nonneg _) h5
    have h2 : KD * E * ((KY1 * (1 + N) * Q ^ 2) * ((2 * CB ^ 4 * E) * (1 + t) ^ 2))
        = 2 * CB ^ 4 * KY1 * KD * (1 + N) * (1 + t) ^ 2 * (Q ^ 2 * E ^ 2) := by ring
    have h3 : (0:ℝ) ≤ 2 * CB ^ 4 * KY1 * KD * (1 + N) * (1 + t) ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCB4n) hKY1n)
        hKD0.le) hN0) hT0
    calc ‖(((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
            * DeltaFun (imagAxis t ht)))⁻¹‖
          * ‖kwpY1 τ (imagAxis t ht)
              * ((E14Fun (imagAxis t ht) / DeltaFun (imagAxis t ht))
                  * phitVec (imagAxis t ht) 1)‖
        ≤ (KD * E) * ((KY1 * (1 + N) * Q ^ 2) * ((2 * CB ^ 4 * E) * (1 + t) ^ 2)) :=
          mul_le_mul hDinv h1 (norm_nonneg _) (mul_nonneg hKD0.le hEn)
      _ = 2 * CB ^ 4 * KY1 * KD * (1 + N) * (1 + t) ^ 2 * (Q ^ 2 * E ^ 2) := h2
      _ ≤ 2 * CB ^ 4 * KY1 * KD * (1 + N) * (1 + t) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hQ2E2 h3
      _ = 2 * CB ^ 4 * KY1 * KD * (1 + N) * (1 + t) ^ 2 := by ring
  have hterm2 : ‖(((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
        * DeltaFun (imagAxis t ht)))⁻¹
      * (kwpY2 τ (imagAxis t ht) * phitVec (imagAxis t ht) 2)‖
      ≤ CB * KY2 * KD * (1 + N) * (1 + t) ^ 2 := by
    rw [norm_mul]
    have h1 : ‖kwpY2 τ (imagAxis t ht) * phitVec (imagAxis t ht) 2‖
        ≤ (KY2 * (1 + N) * Q) * (CB * (1 + t) ^ 2) := by
      rw [norm_mul]
      exact mul_le_mul hY2 hp2b (norm_nonneg _) (mul_nonneg (mul_nonneg hKY2n hN0) hQn)
    have h2 : KD * E * ((KY2 * (1 + N) * Q) * (CB * (1 + t) ^ 2))
        = CB * KY2 * KD * (1 + N) * (1 + t) ^ 2 * (Q * E) := by ring
    have h3 : (0:ℝ) ≤ CB * KY2 * KD * (1 + N) * (1 + t) ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCBn hKY2n) hKD0.le) hN0) hT0
    calc ‖(((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
            * DeltaFun (imagAxis t ht)))⁻¹‖
          * ‖kwpY2 τ (imagAxis t ht) * phitVec (imagAxis t ht) 2‖
        ≤ (KD * E) * ((KY2 * (1 + N) * Q) * (CB * (1 + t) ^ 2)) :=
          mul_le_mul hDinv h1 (norm_nonneg _) (mul_nonneg hKD0.le hEn)
      _ = CB * KY2 * KD * (1 + N) * (1 + t) ^ 2 * (Q * E) := h2
      _ ≤ CB * KY2 * KD * (1 + N) * (1 + t) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hQE h3
      _ = CB * KY2 * KD * (1 + N) * (1 + t) ^ 2 := by ring
  -- assembly
  rw [kwp_KPlus_eq τ (imagAxis t ht)]
  have hsplit3 : ∀ a b c : ℂ, ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
    intro a b c
    have h1 := norm_add_le (a + b) c
    have h2 := norm_add_le a b
    linarith
  have hsplit : ‖(((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
        * DeltaFun (imagAxis t ht)))⁻¹
      * (kwpY0 τ (imagAxis t ht) * (E4Fun (imagAxis t ht) * phitVec (imagAxis t ht) 0)
        + kwpY1 τ (imagAxis t ht)
            * ((E14Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)) * phitVec (imagAxis t ht) 1)
        + kwpY2 τ (imagAxis t ht) * (phitVec (imagAxis t ht) 2))‖
      ≤ ‖(((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
        * DeltaFun (imagAxis t ht)))⁻¹
        * (kwpY0 τ (imagAxis t ht) * (E4Fun (imagAxis t ht) * phitVec (imagAxis t ht) 0))‖
      + ‖(((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
        * DeltaFun (imagAxis t ht)))⁻¹
        * (kwpY1 τ (imagAxis t ht)
            * ((E14Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)) * phitVec (imagAxis t ht) 1))‖
      + ‖(((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
        * DeltaFun (imagAxis t ht)))⁻¹
        * (kwpY2 τ (imagAxis t ht) * (phitVec (imagAxis t ht) 2))‖ := by
    rw [show (((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
        * DeltaFun (imagAxis t ht)))⁻¹
        * (kwpY0 τ (imagAxis t ht) * (E4Fun (imagAxis t ht) * phitVec (imagAxis t ht) 0)
          + kwpY1 τ (imagAxis t ht)
              * ((E14Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)) * phitVec (imagAxis t ht) 1)
          + kwpY2 τ (imagAxis t ht) * (phitVec (imagAxis t ht) 2))
        = (((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
          * DeltaFun (imagAxis t ht)))⁻¹
          * (kwpY0 τ (imagAxis t ht) * (E4Fun (imagAxis t ht) * phitVec (imagAxis t ht) 0))
        + (((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
          * DeltaFun (imagAxis t ht)))⁻¹
          * (kwpY1 τ (imagAxis t ht)
              * ((E14Fun (imagAxis t ht) / DeltaFun (imagAxis t ht)) * phitVec (imagAxis t ht) 1))
        + (((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I
          * DeltaFun (imagAxis t ht)))⁻¹
          * (kwpY2 τ (imagAxis t ht) * (phitVec (imagAxis t ht) 2)) by ring]
    exact hsplit3 _ _ _
  have hsum := add_le_add (add_le_add hterm0 hterm1) hterm2
  have hfin : (3 / 2) * KY0 * KD * (1 + N) * (1 + t) ^ 2
        + 2 * CB ^ 4 * KY1 * KD * (1 + N) * (1 + t) ^ 2
        + CB * KY2 * KD * (1 + N) * (1 + t) ^ 2
      ≤ (2 * KK + 1) * (scale τ) ^ (1:ℝ) * (1 + t) ^ (2:ℝ) := by
    rw [Real.rpow_one, Real.rpow_two]
    have h9 : (0:ℝ) ≤ (3 / 2) * KY0 * KD := mul_nonneg (mul_nonneg (by norm_num) hKY0n) hKD0.le
    have h10 : (0:ℝ) ≤ 2 * CB ^ 4 * KY1 * KD :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCB4n) hKY1n) hKD0.le
    have h11 : (0:ℝ) ≤ CB * KY2 * KD := mul_nonneg (mul_nonneg hCBn hKY2n) hKD0.le
    have heq : (3 / 2) * KY0 * KD * (1 + N) * (1 + t) ^ 2
          + 2 * CB ^ 4 * KY1 * KD * (1 + N) * (1 + t) ^ 2
          + CB * KY2 * KD * (1 + N) * (1 + t) ^ 2
        = ((3 / 2) * KY0 * KD + 2 * CB ^ 4 * KY1 * KD + CB * KY2 * KD)
            * ((1 + N) * (1 + t) ^ 2) := by ring
    rw [heq]
    have hscale' : (1 + N) ≤ 2 * scale τ := hscale
    have h14 : ((3 / 2) * KY0 * KD + 2 * CB ^ 4 * KY1 * KD + CB * KY2 * KD) * (1 + N)
        * (1 + t) ^ 2
        ≤ ((3 / 2) * KY0 * KD + 2 * CB ^ 4 * KY1 * KD + CB * KY2 * KD) * (2 * scale τ)
        * (1 + t) ^ 2 := by
      have h15 : (0:ℝ) ≤ (1 + t) ^ 2 := hT0
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscale' (by linarith)) h15
    have hKK2 : KD * ((3 / 2) * KY0 + 2 * CB ^ 4 * KY1 + CB * KY2)
        = (3 / 2) * KY0 * KD + 2 * CB ^ 4 * KY1 * KD + CB * KY2 * KD := by rw [← hKK]; ring
    calc ((3 / 2) * KY0 * KD + 2 * CB ^ 4 * KY1 * KD + CB * KY2 * KD) * ((1 + N) * (1 + t) ^ 2)
        = ((3 / 2) * KY0 * KD + 2 * CB ^ 4 * KY1 * KD + CB * KY2 * KD) * (1 + N)
            * (1 + t) ^ 2 := by ring
      _ ≤ ((3 / 2) * KY0 * KD + 2 * CB ^ 4 * KY1 * KD + CB * KY2 * KD) * (2 * scale τ)
          * (1 + t) ^ 2 := h14
      _ = KK * (2 * scale τ) * (1 + t) ^ 2 := by rw [← hKK2]
      _ ≤ (2 * KK + 1) * (scale τ) * (1 + t) ^ 2 := by
          have h16 : (0:ℝ) ≤ 2 * ((1 + t) ^ 2) := by positivity
          have hfc : (0:ℝ) ≤ scale τ := (Work.Kernels.scale_pos τ).le
          nlinarith [hKK0, hfc, h16]
  have hnorm := hsplit
  linarith [hnorm, hsum, hfin]


/-! ## The target theorem -/

theorem KaxisWindowPoly (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        1 ≤ t → t ≤ τ.im - 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  rcases hd with rfl | rfl
  · -- `d = 8`: the exponential factor in the funnel bound is `e^0 = 1`
    obtain ⟨C8, N8, M8, hC8, hN8, hM8, hb8⟩ :=
      (Work.Asymptotics.HalfFunnel.funnelPreDeclash ℓ 8 (Or.inl rfl)).1
    refine ⟨C8, N8, M8, hC8, hN8, hM8, ?_⟩
    intro τ t hτ hτ2 ht1 htle
    have ht0 : 0 < t := by linarith
    rw [Work.Kernels.Kaxis, dif_pos ht0]
    have h := hb8 τ t hτ hτ2 ht1 htle
    rw [if_pos rfl] at h
    rw [Work.Kernels.Kaxis, dif_pos ht0] at h
    simpa only [zero_mul, Real.exp_zero, mul_one] using h
  · -- `d = 24`
    obtain ⟨C8, N8, M8, hC8, hN8, hM8, hb8⟩ :=
      (Work.Asymptotics.HalfFunnel.funnelPreDeclash ℓ 24 (Or.inr rfl)).1
    obtain ⟨Cp, Np, Mp, hCp, hNp, hMp, hbp⟩ := kwp_KPlus24_bound ℓ
    obtain ⟨Hm, Cm, Nm, Mm, hHm, hCm, hNm, hMm, hbm⟩ := kwp_KMinus24_bound ℓ
    set H : ℝ := Hm with hH
    set HB : ℝ := C8 * Real.exp (2 * Real.pi * (H - 1)) + 1 with hHB
    refine ⟨max (Cp + Cm) HB, max Np (max Nm N8), max Mp (max Mm M8), ?_, ?_, ?_, ?_⟩
    · have h1 : (0:ℝ) < Cp + Cm := by linarith
      exact lt_of_lt_of_le h1 (le_max_left _ _)
    · exact le_trans hNp (le_max_left _ _)
    · exact le_trans hMp (le_max_left _ _)
    · intro τ t hτ hτ2 ht1 htle
      have ht0 : 0 < t := by linarith
      rw [Work.Kernels.Kaxis, dif_pos ht0]
      have hscale1 : (1:ℝ) ≤ scale τ := Work.Kernels.one_le_scale τ
      have hT1 : (1:ℝ) ≤ 1 + t := by linarith
      have hF : Work.Asymptotics.Funnel τ := ⟨hτ, hτ2⟩
      have hNle : max Np (max Nm N8) = max Np (max Nm N8) := rfl
      by_cases hcase : H ≤ τ.im
      · -- in the regime where both kernel halves are controlled
        have hmH : Hm ≤ τ.im := by rw [hH] at hcase; exact hcase
        have hp := hbp τ t ht0 hF ht1 htle
        have hm := hbm τ t ht0 hmH ht1 htle
        have hKfun : Kfun ℓ 24 τ (imagAxis t ht0) = (KPlus 24 τ (imagAxis t ht0)
            + KMinus ℓ 24 τ (imagAxis t ht0)) / 2 := rfl
        rw [hKfun]
        have hsplit : ‖(KPlus 24 τ (imagAxis t ht0) + KMinus ℓ 24 τ (imagAxis t ht0)) / 2‖
            ≤ (Cp * (scale τ) ^ Np * (1 + t) ^ Mp + Cm * (scale τ) ^ Nm * (1 + t) ^ Mm) := by
          rw [norm_div, show ‖(2:ℂ)‖ = 2 from by simp]
          have h2 : (‖KPlus 24 τ (imagAxis t ht0)‖ + ‖KMinus ℓ 24 τ (imagAxis t ht0)‖) / 2
              ≤ Cp * (scale τ) ^ Np * (1 + t) ^ Mp + Cm * (scale τ) ^ Nm * (1 + t) ^ Mm := by
            have h3 := add_le_add hp hm
            rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
            have h4 : (0:ℝ) ≤ Cp * (scale τ) ^ Np * (1 + t) ^ Mp
                + Cm * (scale τ) ^ Nm * (1 + t) ^ Mm := by
              have h6 : (0:ℝ) ≤ (scale τ) ^ Np :=
                Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _
              have h7 : (0:ℝ) ≤ (1 + t) ^ Mp := Real.rpow_nonneg (by linarith) _
              have h8 : (0:ℝ) ≤ (scale τ) ^ Nm :=
                Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _
              have h9 : (0:ℝ) ≤ (1 + t) ^ Mm := Real.rpow_nonneg (by linarith) _
              have h10 : (0:ℝ) ≤ Cp * (scale τ) ^ Np * (1 + t) ^ Mp := by positivity
              have h11 : (0:ℝ) ≤ Cm * (scale τ) ^ Nm * (1 + t) ^ Mm := by positivity
              linarith
            linarith [h3, h4]
          refine le_trans ?_ h2
          exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
        -- monotone collapse
        have hN1 : Np ≤ max Np (max Nm N8) := le_max_left _ _
        have hN2 : Nm ≤ max Np (max Nm N8) := le_trans (le_max_left _ _) (le_max_right _ _)
        have hN3 : N8 ≤ max Np (max Nm N8) := le_trans (le_max_right _ _) (le_max_right _ _)
        have hM1 : Mp ≤ max Mp (max Mm M8) := le_max_left _ _
        have hM2 : Mm ≤ max Mp (max Mm M8) := le_trans (le_max_left _ _) (le_max_right _ _)
        have hM3 : M8 ≤ max Mp (max Mm M8) := le_trans (le_max_right _ _) (le_max_right _ _)
        have hsN : (0:ℝ) ≤ scale τ := (Work.Kernels.scale_pos τ).le
        have hsN' : (0:ℝ) ≤ (scale τ) ^ max Np (max Nm N8) := Real.rpow_nonneg hsN _
        have hTm : (0:ℝ) ≤ (1 + t) ^ max Mp (max Mm M8) := Real.rpow_nonneg (by linarith) _
        have hs1 : Cp * (scale τ) ^ Np * (1 + t) ^ Mp
            ≤ Cp * (scale τ) ^ max Np (max Nm N8) * (1 + t) ^ max Mp (max Mm M8) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ hCp.le) ?_ (Real.rpow_nonneg (by linarith) _)
            (mul_nonneg hCp.le hsN')
          · exact Real.rpow_le_rpow_of_exponent_le hscale1 hN1
          · exact Real.rpow_le_rpow_of_exponent_le hT1 hM1
        have hs2 : Cm * (scale τ) ^ Nm * (1 + t) ^ Mm
            ≤ Cm * (scale τ) ^ max Np (max Nm N8) * (1 + t) ^ max Mp (max Mm M8) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ hCm.le) ?_ (Real.rpow_nonneg (by linarith) _)
            (mul_nonneg hCm.le hsN')
          · exact Real.rpow_le_rpow_of_exponent_le hscale1 hN2
          · exact Real.rpow_le_rpow_of_exponent_le hT1 hM2
        have hfinal : (Cp * (scale τ) ^ Np * (1 + t) ^ Mp + Cm * (scale τ) ^ Nm * (1 + t) ^ Mm)
            ≤ max (Cp + Cm) HB * (scale τ) ^ max Np (max Nm N8) * (1 + t) ^ max Mp (max Mm M8) := by
          have hsum : (Cp * (scale τ) ^ Np * (1 + t) ^ Mp + Cm * (scale τ) ^ Nm * (1 + t) ^ Mm)
              ≤ (Cp + Cm) * (scale τ) ^ max Np (max Nm N8) * (1 + t) ^ max Mp (max Mm M8) := by
            have heq : (Cp + Cm) * (scale τ) ^ max Np (max Nm N8) * (1 + t) ^ max Mp (max Mm M8)
                = Cp * (scale τ) ^ max Np (max Nm N8) * (1 + t) ^ max Mp (max Mm M8)
                  + Cm * (scale τ) ^ max Np (max Nm N8) * (1 + t) ^ max Mp (max Mm M8) := by
              ring
            linarith [hs1, hs2, heq.le, heq.ge]
          have hle : Cp + Cm ≤ max (Cp + Cm) HB := le_max_left _ _
          have hpos : (0:ℝ) ≤ (scale τ) ^ max Np (max Nm N8) * (1 + t) ^ max Mp (max Mm M8) :=
            mul_nonneg hsN' hTm
          calc (Cp * (scale τ) ^ Np * (1 + t) ^ Mp + Cm * (scale τ) ^ Nm * (1 + t) ^ Mm)
              ≤ (Cp + Cm) * (scale τ) ^ max Np (max Nm N8) * (1 + t) ^ max Mp (max Mm M8) := hsum
            _ = (Cp + Cm) * ((scale τ) ^ max Np (max Nm N8) * (1 + t) ^ max Mp (max Mm M8)) := by ring
            _ ≤ max (Cp + Cm) HB * ((scale τ) ^ max Np (max Nm N8)
                  * (1 + t) ^ max Mp (max Mm M8)) :=
                mul_le_mul_of_nonneg_right hle hpos
            _ = max (Cp + Cm) HB * (scale τ) ^ max Np (max Nm N8)
                  * (1 + t) ^ max Mp (max Mm M8) := by ring
        exact le_trans hsplit hfinal
      · -- otherwise `Im τ ≤ H`, where the exponential funnel bound is controlled
        have hτH : τ.im ≤ H := le_of_lt (not_le.mp hcase)
        have hb := hb8 τ t hτ hτ2 ht1 htle
        rw [if_neg (by norm_num : ¬ ((24 : ℕ) = 8))] at hb
        rw [Work.Kernels.Kaxis, dif_pos ht0] at hb
        have htleH : t ≤ H - 1 := by linarith
        have hexp : Real.exp (2 * Real.pi * t) ≤ Real.exp (2 * Real.pi * (H - 1)) :=
          Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, htleH])
        have hbound : C8 * (scale τ) ^ N8 * (1 + t) ^ M8 * Real.exp (2 * Real.pi * t)
            ≤ max (Cp + Cm) HB * (scale τ) ^ max Np (max Nm N8)
              * (1 + t) ^ max Mp (max Mm M8) := by
          have hN1 : Np ≤ max Np (max Nm N8) := le_max_left _ _
          have hN2 : Nm ≤ max Np (max Nm N8) := le_trans (le_max_left _ _) (le_max_right _ _)
          have hN3 : N8 ≤ max Np (max Nm N8) := le_trans (le_max_right _ _) (le_max_right _ _)
          have hM1 : Mp ≤ max Mp (max Mm M8) := le_max_left _ _
          have hM2 : Mm ≤ max Mp (max Mm M8) := le_trans (le_max_left _ _) (le_max_right _ _)
          have hM3 : M8 ≤ max Mp (max Mm M8) := le_trans (le_max_right _ _) (le_max_right _ _)
          have hsN : (0:ℝ) ≤ scale τ := (Work.Kernels.scale_pos τ).le
          have hsN' : (0:ℝ) ≤ (scale τ) ^ max Np (max Nm N8) := Real.rpow_nonneg hsN _
          have hTm : (0:ℝ) ≤ (1 + t) ^ max Mp (max Mm M8) := Real.rpow_nonneg (by linarith) _
          have hsC : C8 * (scale τ) ^ N8 ≤ C8 * (scale τ) ^ max Np (max Nm N8) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hscale1 hN3) hC8.le
          have hCT : C8 * (scale τ) ^ max Np (max Nm N8) * (1 + t) ^ M8
              ≤ C8 * (scale τ) ^ max Np (max Nm N8) * (1 + t) ^ max Mp (max Mm M8) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT1 hM3)
              (mul_nonneg hC8.le hsN')
          have hmain : C8 * (scale τ) ^ N8 * (1 + t) ^ M8
              ≤ C8 * (scale τ) ^ max Np (max Nm N8) * (1 + t) ^ max Mp (max Mm M8) := by
            have heq1 : C8 * (scale τ) ^ N8 * (1 + t) ^ M8
                = (C8 * (scale τ) ^ N8) * (1 + t) ^ M8 := by ring
            have heq2 : C8 * (scale τ) ^ max Np (max Nm N8) * (1 + t) ^ max Mp (max Mm M8)
                = (C8 * (scale τ) ^ max Np (max Nm N8)) * (1 + t) ^ max Mp (max Mm M8) := by ring
            rw [heq1, heq2]
            exact mul_le_mul hsC (Real.rpow_le_rpow_of_exponent_le hT1 hM3)
              (Real.rpow_nonneg (by linarith) _) (mul_nonneg hC8.le hsN')
          have hHB' : C8 * Real.exp (2 * Real.pi * (H - 1)) ≤ HB := by
            rw [hHB]; linarith
          have hpos : (0:ℝ) ≤ C8 * (scale τ) ^ max Np (max Nm N8)
              * (1 + t) ^ max Mp (max Mm M8) :=
            mul_nonneg (mul_nonneg hC8.le hsN') hTm
          calc C8 * (scale τ) ^ N8 * (1 + t) ^ M8 * Real.exp (2 * Real.pi * t)
              = (C8 * (scale τ) ^ N8 * (1 + t) ^ M8) * Real.exp (2 * Real.pi * t) := by ring
            _ ≤ (C8 * (scale τ) ^ max Np (max Nm N8) * (1 + t) ^ max Mp (max Mm M8))
                  * Real.exp (2 * Real.pi * (H - 1)) :=
                mul_le_mul hmain hexp (Real.exp_pos _).le hpos
            _ = (C8 * Real.exp (2 * Real.pi * (H - 1)))
                  * (scale τ) ^ max Np (max Nm N8) * (1 + t) ^ max Mp (max Mm M8) := by ring
            _ ≤ HB * (scale τ) ^ max Np (max Nm N8) * (1 + t) ^ max Mp (max Mm M8) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hHB' hsN') hTm
            _ ≤ max (Cp + Cm) HB * (scale τ) ^ max Np (max Nm N8) * (1 + t) ^ max Mp (max Mm M8) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hsN') hTm
        exact le_trans hb hbound

end Work.Asymptotics.HalfFunnel
