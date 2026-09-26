/-
# Size bounds for the regrouped pieces `P`, `Q`, `N₁`

`P(τ) = (τE₆(τ)-2φ₀(τ)E₄(τ))E₄(τ) + φ₂(τ)E₆(τ)` vanishes at the cusp `τ → i∞`
(`E₂ = E₄ = E₆ = 1`), `Q(τ,z) = θ₁(τ,z) - (τE₆(τ)-2φ₀(τ)E₄(τ))E₄(σ)³` vanishes at the cusp
`z → i0` (`σ = S•z`), and consequently `N₁ = Δ(σ)E₄(τ)²P(τ) + Δ(τ)Q(τ,z)` is *doubly*
exponentially small: `‖N₁(τ,z)‖ ≤ C(1+‖τ‖)‖q(τ)‖‖q(σ)‖`.
-/
import Mathlib
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.CuspDecay.Core

set_option maxHeartbeats 1000000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics.CuspDecay

open Work.Kernels

lemma norm_qParamFun_eq (τ : UpperHalfPlane) :
    ‖qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := norm_qParamFun τ

lemma exp_neg_two_pi_le_one (x : ℝ) (hx : 0 ≤ x) : Real.exp (-(2 * Real.pi * x)) ≤ 1 := by
  rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos]

/-- From a two-term cusp expansion `f = 1 + c·q + O(q²)` deduce `f = 1 + O(q)`. -/
lemma dev_bound (f : ℍ → ℂ) (c : ℂ) (A : ℝ) (hA : 0 < A)
    (h : ∀ τ : ℍ, 1 ≤ τ.im → ‖f τ - 1 - c * qParamFun τ‖ ≤ A * ‖qParamFun τ‖ ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖f τ - 1‖ ≤ C * ‖qParamFun τ‖ := by
  refine ⟨‖c‖ + A + 1, by positivity, fun τ hτ => ?_⟩
  have h1 := h τ hτ
  have hq1 : ‖qParamFun τ‖ ≤ 1 := by
    rw [norm_qParamFun]; rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hτ]
  have hq : (0:ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
  have h2 : ‖qParamFun τ‖ ^ 2 ≤ ‖qParamFun τ‖ := by nlinarith
  have h3 : ‖f τ - 1 - c * qParamFun τ‖ ≤ (A + 1) * ‖qParamFun τ‖ := by
    calc ‖f τ - 1 - c * qParamFun τ‖ ≤ A * ‖qParamFun τ‖ ^ 2 := h1
      _ ≤ A * ‖qParamFun τ‖ := by nlinarith
      _ ≤ (A + 1) * ‖qParamFun τ‖ := by nlinarith
  have hsp : f τ - 1 = (f τ - 1 - c * qParamFun τ) + c * qParamFun τ := by ring
  rw [hsp]
  have h4 := norm_add_le (f τ - 1 - c * qParamFun τ) (c * qParamFun τ)
  rw [norm_mul] at h4
  nlinarith [h4, h3]

theorem E2_sub_one_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖E2Fun τ - 1‖ ≤ C * ‖qParamFun τ‖ := by
  obtain ⟨C, hC, h⟩ := E2Fun_two_term
  exact dev_bound E2Fun (-24) C hC (fun τ hτ => by simpa using h τ hτ)

theorem E4_sub_one_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖E4Fun τ - 1‖ ≤ C * ‖qParamFun τ‖ := by
  obtain ⟨C, hC, h⟩ := E4Fun_two_term
  exact dev_bound E4Fun 240 C hC (fun τ hτ => by simpa using h τ hτ)

theorem E6_sub_one_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖E6Fun τ - 1‖ ≤ C * ‖qParamFun τ‖ := by
  obtain ⟨C, hC, h⟩ := E6Fun_two_term
  exact dev_bound E6Fun (-504) C hC (fun τ hτ => by simpa using h τ hτ)

/-- `σ = S•z` on the imaginary axis: `Im σ = 1/Im z`. -/
lemma sg_im (z : UpperHalfPlane) (hz : z.re = 0) : (sg z).im = 1 / z.im := by
  have hz' : (z : ℂ) = (z.im : ℂ) * Complex.I := by
    rw [← Complex.re_add_im (z : ℂ), UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, hz]
    simp
  have hkey : -1 / ((z.im : ℂ) * Complex.I) = Complex.I / (z.im : ℂ) := by
    have ht : (z.im : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt z.im_pos)
    rw [div_eq_iff (mul_ne_zero ht Complex.I_ne_zero)]
    field_simp
    rw [pow_two, Complex.I_mul_I]
  rw [← UpperHalfPlane.coe_im, sg_coe, hz', hkey]
  rw [show (Complex.I / (z.im : ℂ)).im = 1 / z.im by
    rw [Complex.div_im]
    simp]

/-! ## `P`: `O(q)` at the cusp `i∞` -/

open Work.Asymptotics

lemma E4_add_one_bdd : IsBigOq (fun τ : ℍ => E4Fun τ + 1) 0 := by
  have h1 : IsBigOq (fun _ : ℍ => (1 : ℂ)) 0 :=
    IsBigOq.bounded 1 one_pos (fun _ _ => by simp)
  simpa using E4Fun_bdd.add h1

lemma E4sq_bdd : IsBigOq (fun τ : ℍ => E4Fun τ ^ 2) 0 := by
  have h := E4Fun_bdd.mul E4Fun_bdd
  refine h.congr (fun τ => ?_)
  ring

lemma E4sq_minus_one : IsBigOq (fun τ : ℍ => E4Fun τ ^ 2 - 1) 1 := by
  have h : IsBigOq (fun τ : ℍ => (E4Fun τ - 1) * (E4Fun τ + 1)) (1 + 0) :=
    E4_minus_one.mul E4_add_one_bdd
  refine (IsBigOq.mono h (by norm_num)).congr (fun τ => ?_)
  ring

lemma E2E6_minus_one : IsBigOq (fun τ : ℍ => E2Fun τ * E6Fun τ - 1) 1 := by
  have h : IsBigOq (fun τ : ℍ => (E2Fun τ - 1) * (E6Fun τ - 1) + (E2Fun τ - 1) + (E6Fun τ - 1))
      (min (min (1 + 1) 1) 1) :=
    ((E2_minus_one.mul E6_minus_one).add E2_minus_one).add E6_minus_one
  refine (IsBigOq.mono h (by norm_num)).congr (fun τ => ?_)
  ring

lemma E4E6_minus_one : IsBigOq (fun τ : ℍ => E4Fun τ * E6Fun τ - 1) 1 := by
  have h : IsBigOq (fun τ : ℍ => (E4Fun τ - 1) * (E6Fun τ - 1) + (E4Fun τ - 1) + (E6Fun τ - 1))
      (min (min (1 + 1) 1) 1) :=
    ((E4_minus_one.mul E6_minus_one).add E4_minus_one).add E6_minus_one
  refine (IsBigOq.mono h (by norm_num)).congr (fun τ => ?_)
  ring

lemma E2E4sq_minus_one : IsBigOq (fun τ : ℍ => E2Fun τ * E4Fun τ ^ 2 - 1) 1 := by
  have h : IsBigOq (fun τ : ℍ => (E2Fun τ - 1) * (E4Fun τ ^ 2) + (E4Fun τ ^ 2 - 1)) (min 1 1) :=
    (E2_minus_one.mul E4sq_bdd).add E4sq_minus_one
  refine (IsBigOq.mono h (le_refl 1)).congr (fun τ => ?_)
  ring

lemma E2sqE6_minus_one : IsBigOq (fun τ : ℍ => E2Fun τ ^ 2 * E6Fun τ - 1) 1 := by
  have h : IsBigOq (fun τ : ℍ => (E2Fun τ ^ 2 - 1) * (E6Fun τ) + (E6Fun τ - 1)) (min 1 1) :=
    (E2sq_minus_one.mul E6Fun_bdd).add E6_minus_one
  refine (IsBigOq.mono h (le_refl 1)).congr (fun τ => ?_)
  ring

lemma X_isBigOq :
    IsBigOq (fun τ : ℍ => E4Fun τ * E6Fun τ - 2 * E2Fun τ * E4Fun τ ^ 2 + E2Fun τ ^ 2 * E6Fun τ) 1 := by
  have h1 : IsBigOq (fun τ : ℍ => E4Fun τ * E6Fun τ - 1) 1 := E4E6_minus_one
  have h2 : IsBigOq (fun τ : ℍ => (-2) * (E2Fun τ * E4Fun τ ^ 2 - 1)) 1 :=
    E2E4sq_minus_one.const_mul (-2)
  have h3 : IsBigOq (fun τ : ℍ => E2Fun τ ^ 2 * E6Fun τ - 1) 1 := E2sqE6_minus_one
  have h : IsBigOq (fun τ : ℍ => (E4Fun τ * E6Fun τ - 1) + (-2) * (E2Fun τ * E4Fun τ ^ 2 - 1)
      + (E2Fun τ ^ 2 * E6Fun τ - 1)) (min (min 1 1) 1) := (h1.add h2).add h3
  refine (IsBigOq.mono h (by norm_num)).congr (fun τ => ?_)
  ring

lemma Y_isBigOq : IsBigOq (fun τ : ℍ => E4Fun τ ^ 2 - E2Fun τ * E6Fun τ) 1 := by
  have h : IsBigOq (fun τ : ℍ => (E4Fun τ ^ 2 - 1) + -(E2Fun τ * E6Fun τ - 1)) (min 1 1) :=
    E4sq_minus_one.add E2E6_minus_one.neg
  refine (IsBigOq.mono h (le_refl 1)).congr (fun τ => ?_)
  ring

theorem PFac_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖PFac τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := by
  obtain ⟨CX, hCX, hXb⟩ := X_isBigOq
  obtain ⟨CY, hCY, hYb⟩ := Y_isBigOq
  refine ⟨CX + 6 / Real.pi * CY + 1, by positivity, fun τ hτ => ?_⟩
  have hP : PFac τ = (τ : ℂ) * (E4Fun τ * E6Fun τ - 2 * E2Fun τ * E4Fun τ ^ 2 + E2Fun τ ^ 2 * E6Fun τ)
      + (6 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 2 - E2Fun τ * E6Fun τ) := by
    rw [PFac, phi0, phi2]; ring
  have hX := hXb τ hτ
  have hY := hYb τ hτ
  rw [pow_one] at hX hY
  have hq : (0:ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
  have hsix : ‖(6 * Complex.I / (Real.pi : ℂ))‖ ≤ 6 / Real.pi := by
    rw [norm_div, norm_mul]
    have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by rw [Complex.norm_real]; exact abs_of_nonneg Real.pi_pos.le
    rw [hpi, Complex.norm_ofNat, Complex.norm_I, mul_one]
  rw [hP]
  have h1 := norm_add_le ((τ : ℂ) * (E4Fun τ * E6Fun τ - 2 * E2Fun τ * E4Fun τ ^ 2
      + E2Fun τ ^ 2 * E6Fun τ)) ((6 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 2 - E2Fun τ * E6Fun τ))
  have h2 : ‖(τ : ℂ) * (E4Fun τ * E6Fun τ - 2 * E2Fun τ * E4Fun τ ^ 2 + E2Fun τ ^ 2 * E6Fun τ)‖
      ≤ ‖(τ : ℂ)‖ * (CX * ‖qParamFun τ‖) := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hX (norm_nonneg _)
  have h3 : ‖(6 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 2 - E2Fun τ * E6Fun τ)‖
      ≤ (6 / Real.pi) * (CY * ‖qParamFun τ‖) := by
    rw [norm_mul]; exact mul_le_mul hsix hY (norm_nonneg _) (by positivity)
  have hA : ‖(τ : ℂ)‖ * (CX * ‖qParamFun τ‖) ≤ (1 + ‖(τ : ℂ)‖) * (CX * ‖qParamFun τ‖) :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)) (mul_nonneg hCX.le hq)
  have hB : (6 / Real.pi) * (CY * ‖qParamFun τ‖)
      ≤ (1 + ‖(τ : ℂ)‖) * ((6 / Real.pi) * (CY * ‖qParamFun τ‖)) := by
    have h6 : (0:ℝ) ≤ 6 / Real.pi := by positivity
    have hb : (0:ℝ) ≤ CY * ‖qParamFun τ‖ := mul_nonneg hCY.le hq
    calc (6 / Real.pi) * (CY * ‖qParamFun τ‖)
        = 1 * ((6 / Real.pi) * (CY * ‖qParamFun τ‖)) := by ring
      _ ≤ (1 + ‖(τ : ℂ)‖) * ((6 / Real.pi) * (CY * ‖qParamFun τ‖)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg h6 hb)
          exact le_add_of_nonneg_right (norm_nonneg _)
  have h4 : ‖(τ : ℂ)‖ * (CX * ‖qParamFun τ‖) + (6 / Real.pi) * (CY * ‖qParamFun τ‖)
      ≤ (CX + 6 / Real.pi * CY + 1) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := by
    calc ‖(τ : ℂ)‖ * (CX * ‖qParamFun τ‖) + (6 / Real.pi) * (CY * ‖qParamFun τ‖)
        ≤ (1 + ‖(τ : ℂ)‖) * (CX * ‖qParamFun τ‖)
            + (1 + ‖(τ : ℂ)‖) * ((6 / Real.pi) * (CY * ‖qParamFun τ‖)) := add_le_add hA hB
      _ = (1 + ‖(τ : ℂ)‖) * ((CX + 6 / Real.pi * CY) * ‖qParamFun τ‖) := by ring
      _ ≤ (1 + ‖(τ : ℂ)‖) * ((CX + 6 / Real.pi * CY + 1) * ‖qParamFun τ‖) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right (by linarith) hq
      _ = (CX + 6 / Real.pi * CY + 1) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := by ring
  calc ‖(τ : ℂ) * (E4Fun τ * E6Fun τ - 2 * E2Fun τ * E4Fun τ ^ 2 + E2Fun τ ^ 2 * E6Fun τ)
        + (6 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 2 - E2Fun τ * E6Fun τ)‖
      ≤ ‖(τ : ℂ) * (E4Fun τ * E6Fun τ - 2 * E2Fun τ * E4Fun τ ^ 2 + E2Fun τ ^ 2 * E6Fun τ)‖
        + ‖(6 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 2 - E2Fun τ * E6Fun τ)‖ := h1
    _ ≤ ‖(τ : ℂ)‖ * (CX * ‖qParamFun τ‖) + (6 / Real.pi) * (CY * ‖qParamFun τ‖) := add_le_add h2 h3
    _ ≤ (CX + 6 / Real.pi * CY + 1) * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := h4


/-- **`Q`: `O(q(σ))` at the cusp `z → i0`.** -/
theorem QFac_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : UpperHalfPlane), 1 ≤ τ.im → 1 ≤ (sg z).im →
      ‖QFac τ z‖ ≤ C * (1 + ‖(τ : ℂ)‖) * ‖qParamFun (sg z)‖ := by
  obtain ⟨C2, hC2, h2⟩ := E2_sub_one_bound
  obtain ⟨C4, hC4, h4⟩ := E4_sub_one_bound
  obtain ⟨C6, hC6, h6⟩ := E6_sub_one_bound
  obtain ⟨B2, hB2, hb2⟩ := E2Fun_bound
  obtain ⟨B4, hB4, hb4⟩ := E4Fun_bound
  obtain ⟨B6, hB6, hb6⟩ := E6Fun_bound
  set K : ℝ := C2 + C4 + C6 + 1 with hK
  set B : ℝ := max B2 (max B4 B6) + 1 with hB
  have hKpos : 0 < K := by rw [hK]; linarith
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  have hB2max : B2 ≤ max B2 (max B4 B6) := le_max_left _ _
  have hBpos : 0 < B := by rw [hB]; linarith [le_trans hB2.le hB2max]
  have hB1 : 1 ≤ B := by rw [hB]; linarith [le_trans hB2.le hB2max]
  have hB2le : B2 ≤ B := by rw [hB]; linarith [hB2max]
  have hB4le : B4 ≤ B := by
    have h2 : max B2 (max B4 B6) ≤ B := by rw [hB]; linarith
    exact le_trans (le_trans (le_max_left B4 B6) (le_max_right B2 (max B4 B6))) h2
  have hB6le : B6 ≤ B := by
    have h2 : max B2 (max B4 B6) ≤ B := by rw [hB]; linarith
    exact le_trans (le_trans (le_max_right B4 B6) (le_max_right B2 (max B4 B6))) h2
  refine ⟨B ^ 3 * (K * (B + 1) + K) + 2 * (B + 3 / Real.pi) * B ^ 2 * (K * K + K * (B + 1) + 3 * K) + 1,
    by positivity, fun τ z hτ hσ => ?_⟩
  set q := ‖qParamFun (sg z)‖ with hqdef
  have hq1 : q ≤ 1 := by
    rw [hqdef, norm_qParamFun]; rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hσ]
  have hq0 : (0:ℝ) ≤ q := norm_nonneg _
  have hd2 : ‖E2Fun (sg z) - 1‖ ≤ K * q := by
    have hCK : C2 ≤ K := by rw [hK]; linarith
    calc ‖E2Fun (sg z) - 1‖ ≤ C2 * ‖qParamFun (sg z)‖ := h2 (sg z) hσ
      _ = C2 * q := by rw [hqdef]
      _ ≤ K * q := by nlinarith [hq0, hCK]
  have hd4 : ‖E4Fun (sg z) - 1‖ ≤ K * q := by
    have hCK : C4 ≤ K := by rw [hK]; linarith
    calc ‖E4Fun (sg z) - 1‖ ≤ C4 * ‖qParamFun (sg z)‖ := h4 (sg z) hσ
      _ = C4 * q := by rw [hqdef]
      _ ≤ K * q := by nlinarith [hq0, hCK]
  have hd6 : ‖E6Fun (sg z) - 1‖ ≤ K * q := by
    have hCK : C6 ≤ K := by rw [hK]; linarith
    calc ‖E6Fun (sg z) - 1‖ ≤ C6 * ‖qParamFun (sg z)‖ := h6 (sg z) hσ
      _ = C6 * q := by rw [hqdef]
      _ ≤ K * q := by nlinarith [hq0, hCK]
  have hb2s : ‖E2Fun (sg z)‖ ≤ B := (hb2 (sg z) hσ).trans hB2le
  have hb4s : ‖E4Fun (sg z)‖ ≤ B := (hb4 (sg z) hσ).trans hB4le
  have hb6s : ‖E6Fun (sg z)‖ ≤ B := (hb6 (sg z) hσ).trans hB6le
  have hb4t : ‖E4Fun τ‖ ≤ B := (hb4 τ hτ).trans hB4le
  have hb6t : ‖E6Fun τ‖ ≤ B := (hb6 τ hτ).trans hB6le
  have hb2t : ‖E2Fun τ‖ ≤ B := (hb2 τ hτ).trans hB2le
  have h2add : ‖E2Fun (sg z) + 1‖ ≤ B + 1 := by
    have := norm_add_le (E2Fun (sg z)) 1
    rw [norm_one] at this; linarith
  have h4add : ‖E4Fun (sg z) + 1‖ ≤ B + 1 := by
    have := norm_add_le (E4Fun (sg z)) 1
    rw [norm_one] at this; linarith
  -- the two small brackets at `σ`
  have hbr1 : ‖E2Fun (sg z) ^ 2 - E4Fun (sg z)‖ ≤ (K * (B + 1) + K) * q := by
    have hsp : E2Fun (sg z) ^ 2 - E4Fun (sg z)
        = (E2Fun (sg z) - 1) * (E2Fun (sg z) + 1) - (E4Fun (sg z) - 1) := by ring
    rw [hsp]
    have h1 := norm_sub_le ((E2Fun (sg z) - 1) * (E2Fun (sg z) + 1)) (E4Fun (sg z) - 1)
    have h2' : ‖(E2Fun (sg z) - 1) * (E2Fun (sg z) + 1)‖ ≤ (K * q) * (B + 1) := by
      rw [norm_mul]; exact mul_le_mul hd2 h2add (norm_nonneg _) (by positivity)
    have hfin : (K * q) * (B + 1) + K * q ≤ (K * (B + 1) + K) * q := by
      nlinarith [hq0, hBpos]
    linarith [h1, h2', hd4, hfin]
  have hbr2 : ‖E6Fun (sg z) * E2Fun (sg z) - E4Fun (sg z) ^ 2‖
      ≤ (K * K + K * (B + 1) + 3 * K) * q := by
    have hsp : E6Fun (sg z) * E2Fun (sg z) - E4Fun (sg z) ^ 2
        = (E6Fun (sg z) - 1) * (E2Fun (sg z) - 1) + (E6Fun (sg z) - 1) + (E2Fun (sg z) - 1)
          - (E4Fun (sg z) - 1) * (E4Fun (sg z) + 1) := by ring
    rw [hsp]
    have h1 := norm_sub_le ((E6Fun (sg z) - 1) * (E2Fun (sg z) - 1) + (E6Fun (sg z) - 1)
      + (E2Fun (sg z) - 1)) ((E4Fun (sg z) - 1) * (E4Fun (sg z) + 1))
    have h2a : ‖(E6Fun (sg z) - 1) * (E2Fun (sg z) - 1)‖ ≤ (K * q) * (K * q) := by
      rw [norm_mul]; exact mul_le_mul hd6 hd2 (norm_nonneg _) (by positivity)
    have h2ab : ‖(E6Fun (sg z) - 1) * (E2Fun (sg z) - 1) + (E6Fun (sg z) - 1) + (E2Fun (sg z) - 1)‖
        ≤ (K * q) * (K * q) + K * q + K * q := by
      have ha := norm_add_le ((E6Fun (sg z) - 1) * (E2Fun (sg z) - 1) + (E6Fun (sg z) - 1))
        (E2Fun (sg z) - 1)
      have hb := norm_add_le ((E6Fun (sg z) - 1) * (E2Fun (sg z) - 1)) (E6Fun (sg z) - 1)
      linarith [ha, hb, h2a, hd2, hd6]
    have h2b : ‖(E4Fun (sg z) - 1) * (E4Fun (sg z) + 1)‖ ≤ (K * q) * (B + 1) := by
      rw [norm_mul]; exact mul_le_mul hd4 h4add (norm_nonneg _) (by positivity)
    have hq2 : q * q ≤ q := by nlinarith [hq0, hq1]
    have hfin : (K * q) * (K * q) + K * q + K * q + (K * q) * (B + 1)
        ≤ (K * K + K * (B + 1) + 3 * K) * q := by
      nlinarith [hq0, hq1, hq2, hBpos, hKpos, hK1,
        mul_le_mul_of_nonneg_left hq2 (by positivity : (0:ℝ) ≤ K * K),
        mul_le_mul_of_nonneg_left hq2 (by positivity : (0:ℝ) ≤ K * (B + 1))]
    calc ‖(E6Fun (sg z) - 1) * (E2Fun (sg z) - 1) + (E6Fun (sg z) - 1) + (E2Fun (sg z) - 1)
          - (E4Fun (sg z) - 1) * (E4Fun (sg z) + 1)‖
        ≤ ‖(E6Fun (sg z) - 1) * (E2Fun (sg z) - 1) + (E6Fun (sg z) - 1)
            + (E2Fun (sg z) - 1)‖ + ‖(E4Fun (sg z) - 1) * (E4Fun (sg z) + 1)‖ := h1
      _ ≤ ((K * q) * (K * q) + K * q + K * q) + (K * q) * (B + 1) := add_le_add h2ab h2b
      _ ≤ (K * K + K * (B + 1) + 3 * K) * q := hfin
  -- the identity and the coefficient bounds
  have hQ : QFac τ z = (τ : ℂ) * E6Fun τ * (E4Fun (sg z)) ^ 2
        * ((E2Fun (sg z)) ^ 2 - E4Fun (sg z))
      - 2 * phi0 τ * E4Fun τ * E4Fun (sg z)
        * ((E6Fun (sg z)) * (E2Fun (sg z)) - (E4Fun (sg z)) ^ 2) := by
    rw [QFac, thetaOne]; ring
  have hphi : ‖phi0 τ‖ ≤ (B + 3 / Real.pi) * (1 + ‖(τ : ℂ)‖) := by
    have hE : phi0 τ = (τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ) := by simp only [phi0]
    rw [hE]
    have h1 := norm_sub_le ((τ : ℂ) * E2Fun τ) (3 * Complex.I / (Real.pi : ℂ))
    have h2' : ‖(τ : ℂ) * E2Fun τ‖ ≤ ‖(τ : ℂ)‖ * B := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left hb2t (norm_nonneg _)
    have h3 : ‖(3:ℂ) * Complex.I / (Real.pi : ℂ)‖ ≤ 3 / Real.pi := by
      rw [norm_div, norm_mul]
      have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
        rw [Complex.norm_real]; exact abs_of_nonneg Real.pi_pos.le
      rw [hpi, Complex.norm_ofNat, Complex.norm_I, mul_one]
    have hb1 : ‖(τ : ℂ)‖ * B ≤ (1 + ‖(τ : ℂ)‖) * B :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)) hBpos.le
    have hb2 : (3 / Real.pi : ℝ) ≤ (1 + ‖(τ : ℂ)‖) * (3 / Real.pi) := by
      calc (3 / Real.pi : ℝ) = 1 * (3 / Real.pi) := by ring
        _ ≤ (1 + ‖(τ : ℂ)‖) * (3 / Real.pi) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg _)) (by positivity)
    calc ‖(τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)‖
        ≤ ‖(τ : ℂ) * E2Fun τ‖ + ‖(3:ℂ) * Complex.I / (Real.pi : ℂ)‖ := h1
      _ ≤ ‖(τ : ℂ)‖ * B + 3 / Real.pi := add_le_add h2' h3
      _ ≤ (1 + ‖(τ : ℂ)‖) * B + (1 + ‖(τ : ℂ)‖) * (3 / Real.pi) := add_le_add hb1 hb2
      _ = (B + 3 / Real.pi) * (1 + ‖(τ : ℂ)‖) := by ring
  rw [hQ]
  have hmul1 : ‖(τ : ℂ) * E6Fun τ * (E4Fun (sg z)) ^ 2 * ((E2Fun (sg z)) ^ 2 - E4Fun (sg z))‖
      ≤ (1 + ‖(τ : ℂ)‖) * (B ^ 3 * (K * (B + 1) + K)) * q := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow]
    have h1 : ‖(τ : ℂ)‖ * ‖E6Fun τ‖ ≤ (1 + ‖(τ : ℂ)‖) * B :=
      mul_le_mul (le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)) hb6t (norm_nonneg _)
        (by positivity)
    have h2 : ‖E4Fun (sg z)‖ ^ 2 ≤ B * B := by
      rw [pow_two]; exact mul_le_mul hb4s hb4s (norm_nonneg _) hBpos.le
    calc ‖(τ : ℂ)‖ * ‖E6Fun τ‖ * ‖E4Fun (sg z)‖ ^ 2 * ‖(E2Fun (sg z)) ^ 2 - E4Fun (sg z)‖
        ≤ ((1 + ‖(τ : ℂ)‖) * B) * (B * B) * ((K * (B + 1) + K) * q) := by
          apply mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) hbr1 (norm_nonneg _)
            (by positivity)
      _ = (1 + ‖(τ : ℂ)‖) * (B ^ 3 * (K * (B + 1) + K)) * q := by ring
  have hmul2 : ‖2 * phi0 τ * E4Fun τ * E4Fun (sg z)
        * ((E6Fun (sg z)) * (E2Fun (sg z)) - (E4Fun (sg z)) ^ 2)‖
      ≤ (1 + ‖(τ : ℂ)‖) * (2 * (B + 3 / Real.pi) * B ^ 2 * (K * K + K * (B + 1) + 3 * K)) * q := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
    have hA : (2:ℝ) * ‖phi0 τ‖ * ‖E4Fun τ‖ ≤ (1 + ‖(τ : ℂ)‖) * (2 * (B + 3 / Real.pi) * B) := by
      calc (2:ℝ) * ‖phi0 τ‖ * ‖E4Fun τ‖
          ≤ (2 * ((B + 3 / Real.pi) * (1 + ‖(τ : ℂ)‖))) * B := by
            apply mul_le_mul
            · exact mul_le_mul (le_refl (2:ℝ)) hphi (norm_nonneg _) (by norm_num)
            · exact hb4t
            · positivity
            · positivity
        _ = (1 + ‖(τ : ℂ)‖) * (2 * (B + 3 / Real.pi) * B) := by ring
    have h1 : (2:ℝ) * ‖phi0 τ‖ * ‖E4Fun τ‖ * ‖E4Fun (sg z)‖
        ≤ (1 + ‖(τ : ℂ)‖) * (2 * (B + 3 / Real.pi) * B ^ 2) := by
      calc (2:ℝ) * ‖phi0 τ‖ * ‖E4Fun τ‖ * ‖E4Fun (sg z)‖
          ≤ ((1 + ‖(τ : ℂ)‖) * (2 * (B + 3 / Real.pi) * B)) * B :=
            mul_le_mul hA hb4s (norm_nonneg _) (by positivity)
        _ = (1 + ‖(τ : ℂ)‖) * (2 * (B + 3 / Real.pi) * B ^ 2) := by ring
    calc (2:ℝ) * ‖phi0 τ‖ * ‖E4Fun τ‖ * ‖E4Fun (sg z)‖
          * ‖E6Fun (sg z) * E2Fun (sg z) - (E4Fun (sg z)) ^ 2‖
        ≤ ((1 + ‖(τ : ℂ)‖) * (2 * (B + 3 / Real.pi) * B ^ 2))
            * ((K * K + K * (B + 1) + 3 * K) * q) := by
          apply mul_le_mul h1 hbr2 (norm_nonneg _) (by positivity)
      _ = (1 + ‖(τ : ℂ)‖) * (2 * (B + 3 / Real.pi) * B ^ 2 * (K * K + K * (B + 1) + 3 * K)) * q := by
          ring
  have hsum := norm_sub_le
    ((τ : ℂ) * E6Fun τ * (E4Fun (sg z)) ^ 2 * ((E2Fun (sg z)) ^ 2 - E4Fun (sg z)))
    (2 * phi0 τ * E4Fun τ * E4Fun (sg z)
      * ((E6Fun (sg z)) * (E2Fun (sg z)) - (E4Fun (sg z)) ^ 2))
  refine le_trans hsum (le_trans (add_le_add hmul1 hmul2) ?_)
  have hA0 : (0:ℝ) ≤ B ^ 3 * (K * (B + 1) + K) := by positivity
  have hA1 : (0:ℝ) ≤ 2 * (B + 3 / Real.pi) * B ^ 2 * (K * K + K * (B + 1) + 3 * K) := by positivity
  calc (1 + ‖(τ : ℂ)‖) * (B ^ 3 * (K * (B + 1) + K)) * q
        + (1 + ‖(τ : ℂ)‖) * (2 * (B + 3 / Real.pi) * B ^ 2 * (K * K + K * (B + 1) + 3 * K)) * q
      = (1 + ‖(τ : ℂ)‖) * (B ^ 3 * (K * (B + 1) + K)
          + 2 * (B + 3 / Real.pi) * B ^ 2 * (K * K + K * (B + 1) + 3 * K)) * q := by ring
    _ ≤ (B ^ 3 * (K * (B + 1) + K)
          + 2 * (B + 3 / Real.pi) * B ^ 2 * (K * K + K * (B + 1) + 3 * K) + 1)
          * (1 + ‖(τ : ℂ)‖) * q := by
        calc (1 + ‖(τ : ℂ)‖) * (B ^ 3 * (K * (B + 1) + K)
              + 2 * (B + 3 / Real.pi) * B ^ 2 * (K * K + K * (B + 1) + 3 * K)) * q
            ≤ (1 + ‖(τ : ℂ)‖) * (B ^ 3 * (K * (B + 1) + K)
                + 2 * (B + 3 / Real.pi) * B ^ 2 * (K * K + K * (B + 1) + 3 * K) + 1) * q := by
              apply mul_le_mul_of_nonneg_right _ hq0
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              linarith
          _ = (B ^ 3 * (K * (B + 1) + K)
                + 2 * (B + 3 / Real.pi) * B ^ 2 * (K * K + K * (B + 1) + 3 * K) + 1)
                * (1 + ‖(τ : ℂ)‖) * q := by ring

/-- **`N₁` is doubly exponentially small.** -/
theorem NOne_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : UpperHalfPlane), 1 ≤ τ.im → 1 ≤ (sg z).im →
      ‖NOne τ z‖ ≤ C * (1 + ‖(τ : ℂ)‖) * (‖qParamFun τ‖ * ‖qParamFun (sg z)‖) := by
  obtain ⟨CP, hCP, hP⟩ := PFac_bound
  obtain ⟨CQ, hCQ, hQ⟩ := QFac_bound
  obtain ⟨CD, hCD, hD⟩ := DeltaFun_isBigOq_one
  obtain ⟨B4, hB4, hb4⟩ := E4Fun_bound
  refine ⟨(CD * B4 ^ 2 * CP + CD * CQ) + 1, by positivity, fun τ z hτ hσ => ?_⟩
  rw [NOne_decomp]
  have hΔτ : ‖DeltaFun τ‖ ≤ CD * ‖qParamFun τ‖ := by simpa using hD τ hτ
  have hΔσ : ‖DeltaFun (sg z)‖ ≤ CD * ‖qParamFun (sg z)‖ := by simpa using hD (sg z) hσ
  have hE4 : ‖E4Fun τ‖ ≤ B4 := hb4 τ hτ
  have hPt : ‖PFac τ‖ ≤ CP * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := hP τ hτ
  have hQt : ‖QFac τ z‖ ≤ CQ * (1 + ‖(τ : ℂ)‖) * ‖qParamFun (sg z)‖ := hQ τ z hτ hσ
  have h1 : ‖DeltaFun (sg z) * E4Fun τ ^ 2 * PFac τ‖
      ≤ (CD * ‖qParamFun (sg z)‖) * (B4 ^ 2) * (CP * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := by
    rw [norm_mul, norm_mul, norm_pow]
    apply mul_le_mul
    · exact mul_le_mul hΔσ (pow_le_pow_left₀ (norm_nonneg _) hE4 2) (by positivity) (by positivity)
    · exact hPt
    · positivity
    · positivity
  have h2 : ‖DeltaFun τ * QFac τ z‖
      ≤ (CD * ‖qParamFun τ‖) * (CQ * (1 + ‖(τ : ℂ)‖) * ‖qParamFun (sg z)‖) := by
    rw [norm_mul]
    exact mul_le_mul hΔτ hQt (norm_nonneg _) (by positivity)
  have hsum := norm_add_le (DeltaFun (sg z) * E4Fun τ ^ 2 * PFac τ) (DeltaFun τ * QFac τ z)
  refine le_trans (le_trans hsum (add_le_add h1 h2)) ?_
  have hqτ : (0:ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
  have hqσ : (0:ℝ) ≤ ‖qParamFun (sg z)‖ := norm_nonneg _
  have hτb : (0:ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by positivity
  have hXY : (0:ℝ) ≤ ‖qParamFun τ‖ * ‖qParamFun (sg z)‖ := mul_nonneg hqτ hqσ
  have hA : (CD * B4 ^ 2 * CP + CD * CQ) ≤ ((CD * B4 ^ 2 * CP + CD * CQ) + 1) := by linarith
  calc (CD * ‖qParamFun (sg z)‖) * B4 ^ 2 * (CP * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖)
        + (CD * ‖qParamFun τ‖) * (CQ * (1 + ‖(τ : ℂ)‖) * ‖qParamFun (sg z)‖)
      = (CD * B4 ^ 2 * CP + CD * CQ) * (1 + ‖(τ : ℂ)‖)
          * (‖qParamFun τ‖ * ‖qParamFun (sg z)‖) := by ring_nf
    _ ≤ ((CD * B4 ^ 2 * CP + CD * CQ) + 1) * (1 + ‖(τ : ℂ)‖)
          * (‖qParamFun τ‖ * ‖qParamFun (sg z)‖) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hτb) hXY

/-- **`N₁` in the form used by the bound**: `‖N₁(τ,z)‖ ≲ (1+‖τ‖)e^{-2π(Im τ + 1/Im z)}`. -/
theorem NOneBound :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : UpperHalfPlane), 1 ≤ τ.im → z.re = 0 → 0 < z.im → z.im ≤ 1 →
      ‖NOne τ z‖ ≤ C * (1 + ‖(τ : ℂ)‖)
        * Real.exp (-(2 * Real.pi * (τ.im + 1 / z.im))) := by
  obtain ⟨C, hC, hN⟩ := NOne_bound
  refine ⟨C, hC, fun τ z hτ hzre hz hz1 => ?_⟩
  have hσ : 1 ≤ (sg z).im := by
    rw [sg_im z hzre]
    rw [le_div_iff₀ hz]
    simpa using hz1
  have h := hN τ z hτ hσ
  refine h.trans (le_of_eq ?_)
  rw [← sg_im z hzre, norm_qParamFun, norm_qParamFun, ← Real.exp_add]
  congr 1
  ring_nf

end Work.Asymptotics.CuspDecay
