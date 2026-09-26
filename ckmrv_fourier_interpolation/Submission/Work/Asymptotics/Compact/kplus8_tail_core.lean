/-
# The `i∞` tail estimate for `K_+^{(8)}` along the contour: core estimate

This file proves `Work.Asymptotics.Compact.kplus8_tail_core`: if the `τ`-atoms of the
dimension-`8` kernel are bounded by `M`, then along the contour `z = it` the difference
`K_+^{(8)}(τ,it) - 𝒢_+^{(8)}(τ,it)` is `O((1+t)² e^{-πt})`.

The proof is the algebra of `Submission/Work/Asymptotics/KPlus_eight_decomposition.lean`
combined with the `q`-expansions of the `z`-atoms at the cusp.  Writing
`C = 36π⁻²i` and `z = it`, `K_+^{(8)}` expands as

  `K_+^{(8)} = C⁻¹ [ z²(τE₆ - 2φ₀E₄) + φ₂(E₁₄/Δ(τ))/J + (τE₆·E₈(z)·φ̃₂ - 2φ₀E₄·E₁₀(z)·φ̃₁)/(Δ(z)J) ]`

with `J = j(τ) - j(z)`, while `𝒢_+^{(8)} = C⁻¹[(12i/π)(τE₆ - φ₀E₄)z + 36τE₆/π²]` is affine
in `z`.  Since `φ̃₁(z) = z G(z)`, `φ̃₂(z) = G(z)²` with `G(z) = zE₂(z) - 6i/π`, and
`Δ(z)(j(τ)-j(z)) = Δ(z)j(τ) - E₄(z)³`, the leading (polynomial in `t`) parts cancel and the
difference is a sum of three terms, each carrying a factor `E₂(z) - 1`, `Δ(z)/J` or
`E₄(z)^k - 1`; all of these are `O(e^{-2πt})` on `Im z ≥ 1`, which gives the stated bound.

The `τ`-dependence enters only through the hypotheses `‖τ‖, ‖φ₀(τ)‖, ‖φ₂(τ)‖, ‖E₄(τ)‖,
‖E₆(τ)‖, ‖E₁₄(τ)/Δ(τ)‖, ‖j(τ)‖ ≤ M`.
-/
import Mathlib
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.KPlus_eight_decomposition
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA
import Submission.Work.Asymptotics.MiddleRange.exists_bound_Kfun_of_coincidence
import Submission.Work.Asymptotics.cusp_invDelta
import Submission.Work.Asymptotics.cusp_inv_divisor_second

namespace Work.Asymptotics.Compact

open UpperHalfPlane
open Work.Kernels

noncomputable section

set_option maxHeartbeats 2000000

/-! ## The constant `C = 36 π⁻² i` and the affine form of `𝒢_+^{(8)}` -/

/-- The constant `C = 36 π⁻² i` multiplying `Υ_+^{(8)}`. -/
def tailC : ℂ := (36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I

lemma piC_ne_zero : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero

lemma tailC_ne_zero : tailC ≠ 0 := by
  rw [tailC]
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (zpow_ne_zero _ piC_ne_zero)) Complex.I_ne_zero

/-- `𝒢_+^{(8)}(τ,z)` is affine in `z`. -/
lemma Gplus8_eq_lin (τ z : ℍ) :
    Gplus8 τ z = tailC⁻¹ * ((12 * Complex.I / (Real.pi : ℂ)) *
        ((τ : ℂ) * E6Fun τ - phi0 τ * E4Fun τ) * (z : ℂ)
      + 36 * (τ : ℂ) * E6Fun τ / (Real.pi : ℂ) ^ 2) := by
  have hpi := piC_ne_zero
  rw [Gplus8, tailC]
  unfold phi1 Work.Kernels.phi0
  field_simp
  ring_nf
  simp only [show (Complex.I : ℂ) ^ 2 = -1 by rw [sq, Complex.I_mul_I],
    show (Complex.I : ℂ) ^ 3 = -Complex.I by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, sq, Complex.I_mul_I]; ring]
  ring

/-! ## The three pieces of the difference -/

/-- `Φ₁`: the part of the difference carrying the factor `E₂(z) - 1`. -/
def PhiMain (τ z : ℍ) : ℂ :=
  (E2Fun z - 1) * ((τ : ℂ) * E6Fun τ *
      (-((z : ℂ) ^ 2 * (1 + E2Fun z)) + 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ))
    + 2 * phi0 τ * E4Fun τ * (z : ℂ) ^ 2)

/-- `Φ₂`: the `φ₂(τ)E₁₄(τ)/Δ(τ)` term, which is `O(e^{-2πt})` because `1/J = O(e^{-2πt})`. -/
def PhiDiv (τ z : ℍ) : ℂ :=
  phi2 τ * E14Fun τ * (z : ℂ) ^ 2 / (DeltaFun τ * (jInvariantFun τ - jInvariantFun z))

/-- `Φ₃`: the correction coming from `E₈(z) ≠ E₄(z)³` and `E₁₀(z) ≠ E₄(z)³`. -/
def PhiCorr (τ z : ℍ) : ℂ :=
  ((τ : ℂ) * E6Fun τ * phitVec z 2 * (E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)
    - 2 * phi0 τ * E4Fun τ * phitVec z 1 *
        (E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ))
  / (DeltaFun z * (jInvariantFun τ - jInvariantFun z))

/-- **The algebraic decomposition of the difference.**  For `j(τ) ≠ j(z)`,
`K_+^{(8)}(τ,z) - 𝒢_+^{(8)}(τ,z) = C⁻¹(Φ₁ + Φ₂ + Φ₃)`. -/
lemma KPlus8_sub_Gplus8_decomp (τ z : ℍ) (hJ : jInvariantFun τ ≠ jInvariantFun z) :
    KPlus 8 τ z - Gplus8 τ z = tailC⁻¹ * (PhiMain τ z + PhiDiv τ z + PhiCorr τ z) := by
  have hDτ : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hJ' : jInvariantFun τ - jInvariantFun z ≠ 0 := sub_ne_zero.mpr hJ
  rw [Gplus8_eq_lin τ z, KPlus_eight_decomposition τ z hJ]
  unfold PhiMain PhiDiv PhiCorr
  simp only [E8Fun, E10Fun, E14Fun]
  rw [TildeFacts.phitVec_zero, TildeFacts.phitVec_one, TildeFacts.phitVec_two]
  unfold TildeFacts.Gt
  have hA : E4Fun τ ^ 3 * DeltaFun z - DeltaFun τ * E4Fun z ^ 3 ≠ 0 := by
    have e : E4Fun τ ^ 3 * DeltaFun z - DeltaFun τ * E4Fun z ^ 3
        = DeltaFun τ * DeltaFun z * (jInvariantFun τ - jInvariantFun z) := by
      rw [← ClassicalFacts.DeltaFun_mul_jInvariantFun τ,
        ← ClassicalFacts.DeltaFun_mul_jInvariantFun z]
      ring
    rw [e]
    exact mul_ne_zero (mul_ne_zero hDτ hDz) hJ'
  rw [show tailC = 36 * ((Real.pi : ℂ) ^ 2)⁻¹ * Complex.I by
    rw [tailC, show (-2 : ℤ) = -((2 : ℤ)) by norm_num, zpow_neg, zpow_ofNat]]
  field_simp
  ring_nf
  rw [show (Complex.I : ℂ) ^ 2 = -1 by rw [sq, Complex.I_mul_I]]
  ring

/-! ## Uniform bounds for the `z`-atoms on the contour -/

/-- **The cusp bounds for the `z`-atoms on `z = it`, `t ≥ 1`.**  All the `z`-atoms of the
kernel are exponentially close to their values at the cusp, and the `φ̃`-components grow at
most quadratically in `t`. -/
lemma imagAxis_cusp_bounds : ∃ B : ℝ, 1 ≤ B ∧
    (∀ (t : ℝ) (ht : 0 < t), 1 ≤ t →
      ‖E2Fun (imagAxis t ht) - 1‖ ≤ B * Real.exp (-(2 * Real.pi * t)) ∧
      ‖E4Fun (imagAxis t ht) - 1‖ ≤ B * Real.exp (-(2 * Real.pi * t)) ∧
      ‖E6Fun (imagAxis t ht) - 1‖ ≤ B * Real.exp (-(2 * Real.pi * t)) ∧
      ‖DeltaFun (imagAxis t ht)‖ ≤ B * Real.exp (-(2 * Real.pi * t)) ∧
      ‖E2Fun (imagAxis t ht)‖ ≤ B ∧
      ‖E4Fun (imagAxis t ht)‖ ≤ B ∧
      ‖E6Fun (imagAxis t ht)‖ ≤ B ∧
      ‖phitVec (imagAxis t ht) 1‖ ≤ B * (1 + t) ^ 2 ∧
      ‖phitVec (imagAxis t ht) 2‖ ≤ B * (1 + t) ^ 2) := by
  obtain ⟨C2, hC2, h2⟩ := Work.Asymptotics.E2Fun_two_term
  obtain ⟨C4, hC4, h4⟩ := Work.Asymptotics.E4Fun_two_term
  obtain ⟨C6, hC6, h6⟩ := Work.Asymptotics.E6Fun_two_term
  obtain ⟨CD, hCD, hD⟩ := Work.Asymptotics.DeltaFun_upper
  set B0 : ℝ := max (max (max (26 + C2) (242 + C4)) (max (506 + C6) CD)) 1 with hB0def
  have hB01 : 1 ≤ B0 := le_max_right _ _
  have hX1 : 26 + C2 ≤ B0 :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hX2 : 242 + C4 ≤ B0 :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hX3 : 506 + C6 ≤ B0 :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hX4 : CD ≤ B0 :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have h6pi : (0:ℝ) ≤ 6 / Real.pi := by positivity
  have h6pi1 : (1:ℝ) ≤ 1 + 6 / Real.pi := by linarith
  have hB0pos : 0 < B0 := lt_of_lt_of_le one_pos hB01
  set B : ℝ := (B0 + 2) ^ 2 * (1 + 6 / Real.pi) ^ 2 with hBdef
  have hBsq1 : (1:ℝ) ≤ (1 + 6 / Real.pi) ^ 2 := by nlinarith
  have hB0sq : B0 + 2 ≤ (B0 + 2) ^ 2 := by nlinarith
  have hBge : B0 ≤ B := by
    rw [hBdef]
    calc B0 ≤ B0 + 2 := by linarith
      _ ≤ (B0 + 2) ^ 2 := hB0sq
      _ = (B0 + 2) ^ 2 * 1 := by ring
      _ ≤ (B0 + 2) ^ 2 * (1 + 6 / Real.pi) ^ 2 :=
          mul_le_mul_of_nonneg_left hBsq1 (by positivity)
  have hB1 : 1 ≤ B := le_trans hB01 hBge
  have hQ2 : (1:ℝ) ≤ (B0 + 2) * (1 + 6 / Real.pi) := by nlinarith [hB01, h6pi]
  have hPhib : (B0 + 2) * (1 + 6 / Real.pi) ≤ B := by
    rw [hBdef]
    calc (B0 + 2) * (1 + 6 / Real.pi) = ((B0 + 2) * (1 + 6 / Real.pi)) * 1 := by ring
      _ ≤ ((B0 + 2) * (1 + 6 / Real.pi)) * ((B0 + 2) * (1 + 6 / Real.pi)) :=
          mul_le_mul_of_nonneg_left hQ2 (by positivity)
      _ = (B0 + 2) ^ 2 * (1 + 6 / Real.pi) ^ 2 := by ring
  have hBb : B0 + 1 ≤ B := by
    calc B0 + 1 ≤ B0 + 2 := by linarith
      _ ≤ (B0 + 2) ^ 2 := hB0sq
      _ = (B0 + 2) ^ 2 * 1 := by ring
      _ ≤ (B0 + 2) ^ 2 * (1 + 6 / Real.pi) ^ 2 :=
          mul_le_mul_of_nonneg_left hBsq1 (by positivity)
      _ = B := by rw [hBdef]
  refine ⟨B, hB1, ?_⟩
  intro t ht ht1
  set z : ℍ := imagAxis t ht with hzdef
  have hzim : z.im = t := by rw [hzdef]; simp [Work.Kernels.imagAxis]
  have hzn : ‖(z : ℂ)‖ = t := by
    rw [hzdef, show ((imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I from rfl, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hzt1 : 1 ≤ z.im := by rw [hzim]; exact ht1
  have hq : ‖qParamFun z‖ = Real.exp (-(2 * Real.pi * t)) := by
    rw [Work.Asymptotics.norm_qParamFun, hzim]
  have he1 : Real.exp (-(2 * Real.pi * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, le_of_lt ht]
  have hq1 : ‖qParamFun z‖ ≤ 1 := by rw [hq]; exact he1
  have h0q : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hsq : ‖qParamFun z‖ ^ 2 ≤ ‖qParamFun z‖ := by nlinarith [hq1, h0q]
  have h2z := h2 z hzt1
  have h4z := h4 z hzt1
  have h6z := h6 z hzt1
  have hDz := hD z hzt1
  have hE2s : ‖E2Fun z - 1‖ ≤ B0 * ‖qParamFun z‖ := by
    have h3 : ‖(24:ℂ) * qParamFun z‖ = 24 * ‖qParamFun z‖ := by
      rw [norm_mul, Complex.norm_ofNat]
    have hsplit : E2Fun z - 1 = (E2Fun z - 1 + 24 * qParamFun z) - 24 * qParamFun z := by ring
    have hstep : ‖E2Fun z - 1‖ ≤ C2 * ‖qParamFun z‖ ^ 2 + 24 * ‖qParamFun z‖ := by
      rw [hsplit]
      refine le_trans (norm_sub_le _ _) ?_
      rw [h3]
      exact add_le_add h2z le_rfl
    refine le_trans hstep ?_
    have h1 : C2 * ‖qParamFun z‖ ^ 2 ≤ C2 * ‖qParamFun z‖ :=
      mul_le_mul_of_nonneg_left hsq hC2.le
    have h2' : C2 * ‖qParamFun z‖ + 24 * ‖qParamFun z‖ ≤ B0 * ‖qParamFun z‖ := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (by linarith) h0q
    linarith
  have hE4s : ‖E4Fun z - 1‖ ≤ B0 * ‖qParamFun z‖ := by
    have h3 : ‖(240:ℂ) * qParamFun z‖ = 240 * ‖qParamFun z‖ := by
      rw [norm_mul, Complex.norm_ofNat]
    have hsplit : E4Fun z - 1 = (E4Fun z - 1 - 240 * qParamFun z) + 240 * qParamFun z := by ring
    have hstep : ‖E4Fun z - 1‖ ≤ C4 * ‖qParamFun z‖ ^ 2 + 240 * ‖qParamFun z‖ := by
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      rw [h3]
      exact add_le_add h4z le_rfl
    refine le_trans hstep ?_
    have h1 : C4 * ‖qParamFun z‖ ^ 2 ≤ C4 * ‖qParamFun z‖ :=
      mul_le_mul_of_nonneg_left hsq hC4.le
    have h2' : C4 * ‖qParamFun z‖ + 240 * ‖qParamFun z‖ ≤ B0 * ‖qParamFun z‖ := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (by linarith) h0q
    linarith
  have hE6s : ‖E6Fun z - 1‖ ≤ B0 * ‖qParamFun z‖ := by
    have h3 : ‖(504:ℂ) * qParamFun z‖ = 504 * ‖qParamFun z‖ := by
      rw [norm_mul, Complex.norm_ofNat]
    have hsplit : E6Fun z - 1 = (E6Fun z - 1 + 504 * qParamFun z) - 504 * qParamFun z := by ring
    have hstep : ‖E6Fun z - 1‖ ≤ C6 * ‖qParamFun z‖ ^ 2 + 504 * ‖qParamFun z‖ := by
      rw [hsplit]
      refine le_trans (norm_sub_le _ _) ?_
      rw [h3]
      exact add_le_add h6z le_rfl
    refine le_trans hstep ?_
    have h1 : C6 * ‖qParamFun z‖ ^ 2 ≤ C6 * ‖qParamFun z‖ :=
      mul_le_mul_of_nonneg_left hsq hC6.le
    have h2' : C6 * ‖qParamFun z‖ + 504 * ‖qParamFun z‖ ≤ B0 * ‖qParamFun z‖ := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (by linarith) h0q
    linarith
  have hDzb : ‖DeltaFun z‖ ≤ B0 * ‖qParamFun z‖ :=
    le_trans hDz (mul_le_mul_of_nonneg_right hX4 h0q)
  have hE2d : ‖E2Fun z - 1‖ ≤ B0 * Real.exp (-(2 * Real.pi * t)) := by
    rw [← hq]; exact hE2s
  have hE4d : ‖E4Fun z - 1‖ ≤ B0 * Real.exp (-(2 * Real.pi * t)) := by
    rw [← hq]; exact hE4s
  have hE6d : ‖E6Fun z - 1‖ ≤ B0 * Real.exp (-(2 * Real.pi * t)) := by
    rw [← hq]; exact hE6s
  have hDd : ‖DeltaFun z‖ ≤ B0 * Real.exp (-(2 * Real.pi * t)) := by
    rw [← hq]; exact hDzb
  have hE2bd : ‖E2Fun z‖ ≤ B0 + 1 := by
    have h1 : B0 * Real.exp (-(2 * Real.pi * t)) ≤ B0 * 1 :=
      mul_le_mul_of_nonneg_left he1 (le_of_lt hB0pos)
    have hsp : E2Fun z = (E2Fun z - 1) + 1 := by ring
    rw [hsp]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_one]
    linarith
  have hE4bd : ‖E4Fun z‖ ≤ B0 + 1 := by
    have h1 : B0 * Real.exp (-(2 * Real.pi * t)) ≤ B0 * 1 :=
      mul_le_mul_of_nonneg_left he1 (le_of_lt hB0pos)
    have hsp : E4Fun z = (E4Fun z - 1) + 1 := by ring
    rw [hsp]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_one]
    linarith
  have hE6bd : ‖E6Fun z‖ ≤ B0 + 1 := by
    have h1 : B0 * Real.exp (-(2 * Real.pi * t)) ≤ B0 * 1 :=
      mul_le_mul_of_nonneg_left he1 (le_of_lt hB0pos)
    have hsp : E6Fun z = (E6Fun z - 1) + 1 := by ring
    rw [hsp]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_one]
    linarith
  -- the `φ̃`-components
  have hGt : ‖TildeFacts.Gt z‖ ≤ (B0 + 1) * t + 6 / Real.pi := by
    have he : TildeFacts.Gt z = (z : ℂ) * E2Fun z - 6 * Complex.I / (Real.pi : ℂ) := rfl
    rw [he]
    have h6 : ‖(6:ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
      rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    calc ‖(z : ℂ) * E2Fun z - 6 * Complex.I / (Real.pi : ℂ)‖
        ≤ ‖(z : ℂ) * E2Fun z‖ + ‖6 * Complex.I / (Real.pi : ℂ)‖ := norm_sub_le _ _
      _ ≤ (B0 + 1) * t + 6 / Real.pi := by
          rw [h6]
          refine add_le_add ?_ le_rfl
          rw [norm_mul, hzn, mul_comm (B0 + 1) t]
          exact mul_le_mul_of_nonneg_left hE2bd (le_of_lt ht)
  have hBQ : B0 + 2 + 6 / Real.pi ≤ (B0 + 2) * (1 + 6 / Real.pi) := by
    have h2 : 6 / Real.pi ≤ (B0 + 2) * (6 / Real.pi) := le_mul_of_one_le_left h6pi (by linarith)
    have h3 : (B0 + 2) * (1 + 6 / Real.pi) = B0 + 2 + (B0 + 2) * (6 / Real.pi) := by ring
    rw [h3]; linarith
  have hXQ : (B0 + 1) * t + 6 / Real.pi ≤ (1 + t) * ((B0 + 2) * (1 + 6 / Real.pi)) := by
    have h2 : (B0 + 1) * t ≤ (B0 + 2) * t :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt ht)
    have h3 : 6 / Real.pi ≤ 6 / Real.pi * t := le_mul_of_one_le_right h6pi ht1
    have h4 : (B0 + 2 + 6 / Real.pi) * (1 + t)
        = (B0 + 2) + (B0 + 2) * t + (6 / Real.pi + 6 / Real.pi * t) := by ring
    have h5 : (B0 + 1) * t + 6 / Real.pi ≤ (B0 + 2 + 6 / Real.pi) * (1 + t) := by
      rw [h4]; linarith [h2, h3, hB01, h6pi]
    have h6 : (B0 + 2 + 6 / Real.pi) * (1 + t)
        ≤ ((B0 + 2) * (1 + 6 / Real.pi)) * (1 + t) :=
      mul_le_mul_of_nonneg_right hBQ (by linarith)
    have h7 : ((B0 + 2) * (1 + 6 / Real.pi)) * (1 + t)
        = (1 + t) * ((B0 + 2) * (1 + 6 / Real.pi)) := by ring
    linarith [h5, h6, h7]
  have hGt2 : ‖TildeFacts.Gt z‖ ≤ (1 + t) * ((B0 + 2) * (1 + 6 / Real.pi)) :=
    le_trans hGt hXQ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc ‖E2Fun z - 1‖ ≤ B0 * Real.exp (-(2 * Real.pi * t)) := hE2d
      _ ≤ B * Real.exp (-(2 * Real.pi * t)) :=
          mul_le_mul_of_nonneg_right hBge (Real.exp_nonneg _)
  · calc ‖E4Fun z - 1‖ ≤ B0 * Real.exp (-(2 * Real.pi * t)) := hE4d
      _ ≤ B * Real.exp (-(2 * Real.pi * t)) :=
          mul_le_mul_of_nonneg_right hBge (Real.exp_nonneg _)
  · calc ‖E6Fun z - 1‖ ≤ B0 * Real.exp (-(2 * Real.pi * t)) := hE6d
      _ ≤ B * Real.exp (-(2 * Real.pi * t)) :=
          mul_le_mul_of_nonneg_right hBge (Real.exp_nonneg _)
  · calc ‖DeltaFun z‖ ≤ B0 * Real.exp (-(2 * Real.pi * t)) := hDd
      _ ≤ B * Real.exp (-(2 * Real.pi * t)) :=
          mul_le_mul_of_nonneg_right hBge (Real.exp_nonneg _)
  · exact le_trans hE2bd hBb
  · exact le_trans hE4bd hBb
  · exact le_trans hE6bd hBb
  · have h1 : ‖phitVec z 1‖ ≤ t * ((B0 + 1) * t + 6 / Real.pi) := by
      rw [TildeFacts.phitVec_one, norm_mul, hzn]
      exact mul_le_mul_of_nonneg_left hGt (le_of_lt ht)
    calc ‖phitVec z 1‖ ≤ t * ((B0 + 1) * t + 6 / Real.pi) := h1
      _ ≤ t * ((1 + t) * ((B0 + 2) * (1 + 6 / Real.pi))) :=
          mul_le_mul_of_nonneg_left hXQ (le_of_lt ht)
      _ ≤ (1 + t) * ((1 + t) * ((B0 + 2) * (1 + 6 / Real.pi))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (1 + t) ^ 2 * ((B0 + 2) * (1 + 6 / Real.pi)) := by ring
      _ ≤ (1 + t) ^ 2 * B := mul_le_mul_of_nonneg_left hPhib (by positivity)
      _ = B * (1 + t) ^ 2 := by ring
  · have h1 : ‖phitVec z 2‖ ≤ ((B0 + 1) * t + 6 / Real.pi) ^ 2 := by
      rw [TildeFacts.phitVec_two, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hGt 2
    have h2 : (B0 + 1) * t + 6 / Real.pi ≤ (1 + t) * ((B0 + 2) * (1 + 6 / Real.pi)) := hXQ
    calc ‖phitVec z 2‖ ≤ ((B0 + 1) * t + 6 / Real.pi) ^ 2 := h1
      _ ≤ ((1 + t) * ((B0 + 2) * (1 + 6 / Real.pi))) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      _ = (1 + t) ^ 2 * ((B0 + 2) * (1 + 6 / Real.pi)) ^ 2 := by rw [mul_pow]
      _ = (1 + t) ^ 2 * B := by rw [hBdef]; ring
      _ = B * (1 + t) ^ 2 := by ring

/-! ## The estimate of the difference -/

/-- The auxiliary bracket `-(z²(1+E₂(z))) + 12iz/π` of `Φ₁`. -/
def PhiL (z : ℍ) : ℂ := -((z : ℂ) ^ 2 * (1 + E2Fun z)) + 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ)

lemma PhiMain_eq (τ z : ℍ) :
    PhiMain τ z = (E2Fun z - 1) * ((τ : ℂ) * E6Fun τ * PhiL z + 2 * phi0 τ * E4Fun τ * (z : ℂ) ^ 2) :=
  rfl

lemma PhiDiv_eq (τ z : ℍ) :
    PhiDiv τ z = (phi2 τ * (E14Fun τ / DeltaFun τ)) * (z : ℂ) ^ 2
      / (jInvariantFun τ - jInvariantFun z) := by
  have hD : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  rw [PhiDiv]
  field_simp

lemma one_le_mul_self {x y : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) : x ≤ x * y :=
  le_mul_of_one_le_right hx hy

lemma le_self_pow_four {x : ℝ} (hx : 1 ≤ x) : x ≤ x ^ 4 := by
  have h0 : (0:ℝ) ≤ x := by linarith
  have h3 : (1:ℝ) ≤ x ^ 3 := one_le_pow₀ hx
  calc x = x * 1 := (mul_one x).symm
    _ ≤ x * x ^ 3 := mul_le_mul_of_nonneg_left h3 h0
    _ = x ^ 4 := by ring

lemma pow_three_le_pow_four {x : ℝ} (hx : 1 ≤ x) : x ^ 3 ≤ x ^ 4 := by
  have h0 : (0:ℝ) ≤ x ^ 3 := by positivity
  calc x ^ 3 = x ^ 3 * 1 := (mul_one _).symm
    _ ≤ x ^ 3 * x := mul_le_mul_of_nonneg_left hx h0
    _ = x ^ 4 := by ring

lemma le_self_pow_three {x : ℝ} (hx : 1 ≤ x) : x ≤ x ^ 3 := by
  have h0 : (0:ℝ) ≤ x := by linarith
  have h2 : (1:ℝ) ≤ x ^ 2 := one_le_pow₀ hx
  calc x = x * 1 := (mul_one x).symm
    _ ≤ x * x ^ 2 := mul_le_mul_of_nonneg_left h2 h0
    _ = x ^ 3 := by ring

/-- Products of four bounded nonnegative factors. -/
lemma mul4_le_mul4 {a b c d a' b' c' d' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (hd : d ≤ d') (h0b : 0 ≤ b) (h0c : 0 ≤ c) (h0d : 0 ≤ d) (h0a' : 0 ≤ a') (h0b' : 0 ≤ b')
    (h0c' : 0 ≤ c') : a * b * c * d ≤ a' * b' * c' * d' := by
  have h1 : a * b ≤ a' * b' := mul_le_mul ha hb h0b h0a'
  have h2 : a * b * c ≤ a' * b' * c' := mul_le_mul h1 hc h0c (mul_nonneg h0a' h0b')
  exact mul_le_mul h2 hd h0d (mul_nonneg (mul_nonneg h0a' h0b') h0c')

/-- **The core estimate.**  For `τ` whose atoms are bounded by `M` and for `t` large,
`‖K_+^{(8)}(τ,it) - 𝒢_+^{(8)}(τ,it)‖ ≤ A (1+t)² e^{-2πt}`. -/
lemma kplus8_diff_bound {M : ℝ} (hM : 0 < M) :
    ∃ A T : ℝ, 0 < A ∧ 0 < T ∧ ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t), T ≤ t →
      ‖(τ : ℂ)‖ ≤ M → ‖phi0 τ‖ ≤ M → ‖phi2 τ‖ ≤ M → ‖E4Fun τ‖ ≤ M →
      ‖E6Fun τ‖ ≤ M → ‖E14Fun τ / DeltaFun τ‖ ≤ M → ‖jInvariantFun τ‖ ≤ M →
      ‖KPlus 8 τ (imagAxis t ht) - Gplus8 τ (imagAxis t ht)‖
        ≤ A * (1 + t) ^ 2 * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨B, hB1, hB⟩ := imagAxis_cusp_bounds
  set M' : ℝ := max M 1 with hM'def
  have hM'1 : 1 ≤ M' := le_max_right M 1
  have hM'M : M ≤ M' := le_max_left M 1
  have hM'pos : 0 < M' := lt_of_lt_of_le hM hM'M
  set c0 : ℝ := 2 * B * (B ^ 2 + B + 1 + M' + 1) with hc0def
  have hc0pos : 0 < c0 := by rw [hc0def]; nlinarith [hB1, hM'1]
  set T : ℝ := max 1 (Real.log c0 / (2 * Real.pi) + 1) with hTdef
  have hT1 : 1 ≤ T := le_max_left _ _
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le one_pos hT1
  refine ⟨‖tailC⁻¹‖ * (8 * B ^ 2 * M' ^ 2 + 2 * B ^ 2 * M' ^ 2 + 24 * B ^ 4 * M' ^ 4) + 1, T,
    by positivity, hTpos, ?_⟩
  intro τ t ht hTt hτ hφ0 hφ2 hE4 hE6 hE14 hj
  have ht1 : 1 ≤ t := le_trans hT1 hTt
  set z : ℍ := imagAxis t ht with hzdef
  set e : ℝ := Real.exp (-(2 * Real.pi * t)) with hedef
  have hepos : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := by rw [hedef, Real.exp_le_one_iff]; nlinarith [Real.pi_pos, le_of_lt ht]
  have hzim : z.im = t := by rw [hzdef]; simp [Work.Kernels.imagAxis]
  have hzt1 : 1 ≤ z.im := by rw [hzim]; exact ht1
  have hzn : ‖(z : ℂ)‖ = t := by
    rw [hzdef, show ((imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I from rfl, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have htq : t ≤ (1 + t) ^ 2 := by nlinarith
  have h0tsq : (0:ℝ) ≤ (1 + t) ^ 2 := by positivity
  obtain ⟨b2, b4, b6, bD, B2z, B4z, B6z, bt1, bt2⟩ := hB t ht ht1
  have hb2 : ‖E2Fun z - 1‖ ≤ B * e := by rw [hzdef, hedef]; exact b2
  have hb4 : ‖E4Fun z - 1‖ ≤ B * e := by rw [hzdef, hedef]; exact b4
  have hb6 : ‖E6Fun z - 1‖ ≤ B * e := by rw [hzdef, hedef]; exact b6
  have hbD : ‖DeltaFun z‖ ≤ B * e := by rw [hzdef, hedef]; exact bD
  have hB2 : ‖E2Fun z‖ ≤ B := by rw [hzdef]; exact B2z
  have hB4 : ‖E4Fun z‖ ≤ B := by rw [hzdef]; exact B4z
  have hB6 : ‖E6Fun z‖ ≤ B := by rw [hzdef]; exact B6z
  have hbt1 : ‖phitVec z 1‖ ≤ B * (1 + t) ^ 2 := by rw [hzdef]; exact bt1
  have hbt2 : ‖phitVec z 2‖ ≤ B * (1 + t) ^ 2 := by rw [hzdef]; exact bt2
  -- the threshold: `e ≤ 1/c0`
  have hec : e ≤ 1 / c0 := by
    have hlog : Real.log c0 ≤ 2 * Real.pi * t := by
      have h2 : Real.log c0 / (2 * Real.pi) + 1 ≤ t := le_trans (le_max_right _ _) hTt
      have h3 : Real.log c0 / (2 * Real.pi) ≤ t := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 2 * Real.pi)
      rwa [mul_div_cancel₀ _ (by positivity : (2 * Real.pi) ≠ 0)] at h4
    have h5 : Real.exp (-(2 * Real.pi * t)) ≤ Real.exp (-(Real.log c0)) := by
      rw [Real.exp_le_exp]; linarith
    have h6 : Real.exp (-(Real.log c0)) = 1 / c0 := by
      rw [Real.exp_neg, Real.exp_log hc0pos, inv_eq_one_div]
    rw [hedef, ← h6]; exact h5
  -- the divisor `Δ(z)(j τ - j z)`
  have hη : ‖1 - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ‖ ≤ (1:ℝ) / 2 := by
    have hfac : E4Fun z ^ 3 - 1 = (E4Fun z - 1) * (E4Fun z ^ 2 + E4Fun z + 1) := by ring
    have h2' : ‖E4Fun z ^ 2 + E4Fun z + 1‖ ≤ B ^ 2 + B + 1 := by
      have hA : ‖E4Fun z ^ 2 + E4Fun z + 1‖ ≤ ‖E4Fun z ^ 2 + E4Fun z‖ + 1 := by
        simpa using norm_add_le (E4Fun z ^ 2 + E4Fun z) (1:ℂ)
      have hB' : ‖E4Fun z ^ 2 + E4Fun z‖ ≤ B ^ 2 + B := by
        have h := norm_add_le (E4Fun z ^ 2) (E4Fun z)
        rw [norm_pow] at h
        exact le_trans h (add_le_add (pow_le_pow_left₀ (norm_nonneg _) hB4 2) hB4)
      linarith
    have hcub : ‖E4Fun z ^ 3 - 1‖ ≤ (B * e) * (B ^ 2 + B + 1) := by
      rw [hfac, norm_mul]
      exact mul_le_mul hb4 h2' (by positivity) (by positivity)
    have hDm : ‖DeltaFun z * jInvariantFun τ‖ ≤ (B * e) * M := by
      rw [norm_mul]
      exact mul_le_mul hbD hj (norm_nonneg _) (by positivity)
    have h1 : ‖1 - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ‖
        ≤ (B * e) * (B ^ 2 + B + 1) + (B * e) * M := by
      have heq : 1 - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ
          = -(E4Fun z ^ 3 - 1) + DeltaFun z * jInvariantFun τ := by ring
      rw [heq]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_neg]
      exact add_le_add hcub hDm
    have h6 : (B ^ 2 + B + 1) * (B * e) + (B * e) * M ≤ B * e * (B ^ 2 + B + 1 + M') := by
      have h7 : (B * e) * M ≤ (B * e) * M' := mul_le_mul_of_nonneg_left hM'M (by positivity)
      have h8 : B * e * (B ^ 2 + B + 1 + M')
          = (B ^ 2 + B + 1) * (B * e) + (B * e) * M' := by ring
      rw [h8]
      linarith [h7]
    have h9 : B * e * (B ^ 2 + B + 1 + M') ≤ (1:ℝ) / 2 := by
      calc B * e * (B ^ 2 + B + 1 + M') = B * (B ^ 2 + B + 1 + M') * e := by ring
        _ ≤ B * (B ^ 2 + B + 1 + M') * (1 / c0) :=
            mul_le_mul_of_nonneg_left hec (by positivity)
        _ = B * (B ^ 2 + B + 1 + M') / c0 := by ring
        _ ≤ (1:ℝ) / 2 := by
            rw [div_le_iff₀ hc0pos]
            have h13 : c0 = 2 * B * (B ^ 2 + B + 1 + M' + 1) := hc0def
            have h14 : B * (B ^ 2 + B + 1 + M') ≤ B * (B ^ 2 + B + 1 + M' + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            have h15 : (1:ℝ) / 2 * c0 = B * (B ^ 2 + B + 1 + M' + 1) := by
              rw [h13]; ring
            rw [h15]
            exact h14
    linarith
  have hDJ : DeltaFun z * (jInvariantFun τ - jInvariantFun z)
      = -(1 - (1 - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)) := by
    rw [mul_sub, ClassicalFacts.DeltaFun_mul_jInvariantFun z]; ring
  have hDJne : DeltaFun z * (jInvariantFun τ - jInvariantFun z) ≠ 0 := by
    intro h0
    have hJ0 : jInvariantFun τ - jInvariantFun z = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (ClassicalFacts.DeltaFun_ne_zero z)
      · exact h
    have h1 : (1 - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ) = 1 := by
      have h2 : jInvariantFun τ = jInvariantFun z := sub_eq_zero.mp hJ0
      rw [h2, ClassicalFacts.DeltaFun_mul_jInvariantFun z]
      ring
    have h3 := hη
    rw [h1, norm_one] at h3
    linarith
  have hDJge : (1:ℝ) / 2 ≤ ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ := by
    rw [hDJ, norm_neg]
    have h := norm_sub_norm_le (1:ℂ) (1 - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)
    rw [norm_one] at h
    linarith
  have hJne : jInvariantFun τ - jInvariantFun z ≠ 0 := by
    intro h0
    exact hDJne (by rw [h0, mul_zero])
  have hJpos : 0 < ‖jInvariantFun τ - jInvariantFun z‖ := norm_pos_iff.mpr hJne
  have hinvJ : ‖(jInvariantFun τ - jInvariantFun z)⁻¹‖ ≤ 2 * B * e := by
    rw [norm_inv]
    rw [inv_le_iff_one_le_mul₀ hJpos]
    have h2' : ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖
        ≤ (B * e) * ‖jInvariantFun τ - jInvariantFun z‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hbD (norm_nonneg _)
    linarith
  -- the bracket `Φ₁`
  have hPhiL : ‖PhiL z‖ ≤ (5 + B) * (1 + t) ^ 2 := by
    rw [PhiL]
    have hA : ‖-((z:ℂ)^2 * (1 + E2Fun z)) + 12*Complex.I*(z:ℂ)/(Real.pi:ℂ)‖
        ≤ ‖(z:ℂ)^2 * (1 + E2Fun z)‖ + ‖12*Complex.I*(z:ℂ)/(Real.pi:ℂ)‖ := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_neg]
    have hP : ‖(z:ℂ)^2 * (1 + E2Fun z)‖ ≤ t^2 * (1 + B) := by
      rw [norm_mul, norm_pow, hzn]
      have h2' : ‖(1:ℂ) + E2Fun z‖ ≤ 1 + B := by
        calc ‖(1:ℂ) + E2Fun z‖ ≤ ‖(1:ℂ)‖ + ‖E2Fun z‖ := norm_add_le _ _
          _ ≤ 1 + B := by rw [norm_one]; linarith
      exact mul_le_mul_of_nonneg_left h2' (by positivity)
    have hQ : ‖12*Complex.I*(z:ℂ)/(Real.pi:ℂ)‖ ≤ 4 * (1 + t)^2 := by
      have h1 : ‖(12:ℂ)*Complex.I*(z:ℂ)/(Real.pi:ℂ)‖ = 12 * t / Real.pi := by
        rw [norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, hzn,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [h1, div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_three, ht, sq_nonneg (1 + t)]
    have h5 : t^2 * (1+B) ≤ (1+B) * (1+t)^2 := by
      have h6 : t^2 ≤ (1+t)^2 := by nlinarith
      calc t^2 * (1+B) = (1+B) * t^2 := by ring
        _ ≤ (1+B) * (1+t)^2 := mul_le_mul_of_nonneg_left h6 (by positivity)
    have h7 : (1+B)*(1+t)^2 + 4*(1+t)^2 = (5+B)*(1+t)^2 := by ring
    linarith [hA, hP, hQ, h5]
  have hE2c : ‖E2Fun z - 1‖ ≤ B * e := hb2
  have hMain : ‖PhiMain τ z‖ ≤ 8 * B ^ 2 * M' ^ 2 * (1 + t) ^ 2 * e := by
    rw [PhiMain_eq, norm_mul]
    have hX : ‖(τ : ℂ) * E6Fun τ * PhiL z + 2 * phi0 τ * E4Fun τ * (z : ℂ) ^ 2‖
        ≤ 8 * B * M' ^ 2 * (1 + t) ^ 2 := by
      have hτ6 : ‖(τ : ℂ) * E6Fun τ‖ ≤ M' ^ 2 := by
        rw [norm_mul]
        calc ‖(τ : ℂ)‖ * ‖E6Fun τ‖ ≤ M' * M' :=
              mul_le_mul (le_trans hτ hM'M) (le_trans hE6 hM'M) (norm_nonneg _) (by positivity)
          _ = M' ^ 2 := by ring
      have h1 : ‖(τ : ℂ) * E6Fun τ * PhiL z‖ ≤ M' ^ 2 * ((5 + B) * (1 + t) ^ 2) := by
        rw [norm_mul]
        exact mul_le_mul hτ6 hPhiL (norm_nonneg _) (by positivity)
      have h2 : ‖2 * phi0 τ * E4Fun τ * (z : ℂ) ^ 2‖ ≤ 2 * M' ^ 2 * (1 + t) ^ 2 := by
        simp only [norm_mul, norm_pow]
        rw [show ‖(2:ℂ)‖ = 2 by norm_num, hzn]
        calc 2 * ‖phi0 τ‖ * ‖E4Fun τ‖ * t ^ 2
            ≤ 2 * M' * M' * (1 + t) ^ 2 := by
              refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (le_trans hφ0 hM'M)
                (by norm_num)) (le_trans hE4 hM'M) (norm_nonneg _) (by positivity))
                (by nlinarith) (by positivity) (by positivity)
          _ = 2 * M' ^ 2 * (1 + t) ^ 2 := by ring
      refine le_trans (norm_add_le _ _) ?_
      have h8 : M' ^ 2 * ((5 + B) * (1 + t) ^ 2) + 2 * M' ^ 2 * (1 + t) ^ 2
          = M' ^ 2 * (B + 7) * (1 + t) ^ 2 := by ring
      have h9 : M' ^ 2 * (B + 7) * (1 + t) ^ 2 ≤ 8 * B * M' ^ 2 * (1 + t) ^ 2 := by
        have h10 : M' ^ 2 * (B + 7) ≤ 8 * B * M' ^ 2 := by nlinarith [hB1, hM'1]
        exact mul_le_mul_of_nonneg_right h10 h0tsq
      linarith [h1, h2, h8, h9]
    calc ‖E2Fun z - 1‖ * ‖(τ : ℂ) * E6Fun τ * PhiL z + 2 * phi0 τ * E4Fun τ * (z : ℂ) ^ 2‖
        ≤ (B * e) * (8 * B * M' ^ 2 * (1 + t) ^ 2) :=
          mul_le_mul hE2c hX (norm_nonneg _) (by positivity)
      _ = 8 * B ^ 2 * M' ^ 2 * (1 + t) ^ 2 * e := by ring
  -- the `Δ(z)`-term `Φ₂`
  have hDiv : ‖PhiDiv τ z‖ ≤ 2 * B ^ 2 * M' ^ 2 * (1 + t) ^ 2 * e := by
    rw [PhiDiv_eq]
    rw [show (phi2 τ * (E14Fun τ / DeltaFun τ)) * (z : ℂ) ^ 2
          / (jInvariantFun τ - jInvariantFun z)
        = (phi2 τ * (E14Fun τ / DeltaFun τ)) * (z : ℂ) ^ 2
          * (jInvariantFun τ - jInvariantFun z)⁻¹ from by rw [div_eq_mul_inv]]
    rw [norm_mul, norm_mul, norm_mul]
    have h1 : ‖phi2 τ‖ ≤ M' := le_trans hφ2 hM'M
    have h2 : ‖E14Fun τ / DeltaFun τ‖ ≤ M' := le_trans hE14 hM'M
    have h3 : ‖(z : ℂ) ^ 2‖ ≤ (1 + t) ^ 2 := by rw [norm_pow, hzn]; nlinarith
    calc ‖phi2 τ‖ * ‖E14Fun τ / DeltaFun τ‖ * ‖(z : ℂ) ^ 2‖
          * ‖(jInvariantFun τ - jInvariantFun z)⁻¹‖
        ≤ M' * M' * (1 + t) ^ 2 * (2 * B * e) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3
            (norm_nonneg _) (by positivity)) hinvJ (norm_nonneg _) (by positivity)
      _ = 2 * B * M' ^ 2 * (1 + t) ^ 2 * e := by ring
      _ ≤ 2 * B ^ 2 * M' ^ 2 * (1 + t) ^ 2 * e := by
          have h4 : B ≤ B ^ 2 := by nlinarith [hB1]
          have h5 : 2 * B * M' ^ 2 ≤ 2 * B ^ 2 * M' ^ 2 := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by norm_num)) (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h5 h0tsq) (le_of_lt hepos)
  -- the correction `Φ₃`
  have hE8all : ‖E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ‖ ≤ 3 * B ^ 3 * M' * e := by
    have heq : E8Fun z - E4Fun z ^ 3 = E4Fun z ^ 2 * (1 - E4Fun z) := by rw [E8Fun]; ring
    have h1 : ‖E4Fun z ^ 2 * (1 - E4Fun z)‖ ≤ B ^ 2 * (B * e) := by
      rw [norm_mul]
      refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
      · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hB4 2
      · rw [norm_sub_rev]; exact hb4
    have h2 : ‖DeltaFun z * jInvariantFun τ‖ ≤ B * M' * e := by
      rw [norm_mul]
      calc ‖DeltaFun z‖ * ‖jInvariantFun τ‖ ≤ (B * e) * M' :=
            mul_le_mul hbD (le_trans hj hM'M) (norm_nonneg _) (by positivity)
        _ = B * M' * e := by ring
    have h3 : B ^ 2 * (B * e) + B * M' * e ≤ 3 * B ^ 3 * M' * e := by
      have hBe : B ^ 2 * (B * e) = B ^ 3 * e := by ring
      have h4 : B ^ 3 * e ≤ B ^ 3 * M' * e := by
        have h5 : e ≤ M' * e := le_mul_of_one_le_left (le_of_lt hepos) hM'1
        calc B ^ 3 * e ≤ B ^ 3 * (M' * e) := mul_le_mul_of_nonneg_left h5 (by positivity)
          _ = B ^ 3 * M' * e := by ring
      have h6 : B * M' * e ≤ B ^ 3 * M' * e := by
        have h7 : B ≤ B ^ 3 := le_self_pow_three hB1
        have h8 : B * M' ≤ B ^ 3 * M' := mul_le_mul_of_nonneg_right h7 hM'pos.le
        calc B * M' * e = (B * M') * e := by ring
          _ ≤ (B ^ 3 * M') * e := mul_le_mul_of_nonneg_right h8 (le_of_lt hepos)
          _ = B ^ 3 * M' * e := by ring
      have h0 : (0:ℝ) ≤ B ^ 3 * M' * e := by positivity
      linarith [hBe, h4, h6, h0]
    have heq2 : E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ
        = E4Fun z ^ 2 * (1 - E4Fun z) + DeltaFun z * jInvariantFun τ := by rw [heq]
    rw [heq2]
    refine le_trans (norm_add_le _ _) ?_
    linarith [h1, h2, h3]
  have hE10all : ‖E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ‖ ≤ 4 * B ^ 3 * M' * e := by
    have heq : E10Fun z - E4Fun z ^ 3 = E4Fun z * (E6Fun z - E4Fun z ^ 2) := by
      simp only [E10Fun]; ring
    have h3 : ‖E4Fun z ^ 2 - 1‖ ≤ B * e * (B + 1) := by
      have h4 : E4Fun z ^ 2 - 1 = (E4Fun z - 1) * (E4Fun z + 1) := by ring
      rw [h4, norm_mul]
      refine mul_le_mul hb4 ?_ (norm_nonneg _) (by positivity)
      calc ‖E4Fun z + 1‖ ≤ ‖E4Fun z‖ + ‖(1:ℂ)‖ := norm_add_le _ _
        _ ≤ B + 1 := by rw [norm_one]; linarith
    have h5 : ‖E6Fun z - E4Fun z ^ 2‖ ≤ 3 * B ^ 2 * e := by
      have h6 : E6Fun z - E4Fun z ^ 2 = (E6Fun z - 1) - (E4Fun z ^ 2 - 1) := by ring
      rw [h6]
      refine le_trans (norm_sub_le _ _) ?_
      have h7 : B * e * (B + 1) ≤ 2 * B ^ 2 * e := by
        have h7' : B + 1 ≤ 2 * B := by linarith
        have h7'' : B * (B + 1) ≤ B * (2 * B) :=
          mul_le_mul_of_nonneg_left h7' (by linarith)
        calc B * e * (B + 1) = B * (B + 1) * e := by ring
          _ ≤ B * (2 * B) * e := mul_le_mul_of_nonneg_right h7'' (le_of_lt hepos)
          _ = 2 * B ^ 2 * e := by ring
      linarith [hb6, h3, h7]
    have h1 : ‖E4Fun z * (E6Fun z - E4Fun z ^ 2)‖ ≤ B * (3 * B ^ 2 * e) := by
      rw [norm_mul]
      exact mul_le_mul hB4 h5 (norm_nonneg _) (by positivity)
    have h2 : ‖DeltaFun z * jInvariantFun τ‖ ≤ B * M' * e := by
      rw [norm_mul]
      calc ‖DeltaFun z‖ * ‖jInvariantFun τ‖ ≤ (B * e) * M' :=
            mul_le_mul hbD (le_trans hj hM'M) (norm_nonneg _) (by positivity)
        _ = B * M' * e := by ring
    have heq2 : E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ
        = E4Fun z * (E6Fun z - E4Fun z ^ 2) + DeltaFun z * jInvariantFun τ := by rw [heq]
    rw [heq2]
    refine le_trans (norm_add_le _ _) ?_
    have h8 : B * (3 * B ^ 2 * e) = 3 * B ^ 3 * e := by ring
    have h9 : B * M' * e ≤ B ^ 3 * M' * e := by
      have h7 : B ≤ B ^ 3 := le_self_pow_three hB1
      have h7'' : B * M' ≤ B ^ 3 * M' := mul_le_mul_of_nonneg_right h7 hM'pos.le
      calc B * M' * e = (B * M') * e := by ring
        _ ≤ (B ^ 3 * M') * e := mul_le_mul_of_nonneg_right h7'' (le_of_lt hepos)
        _ = B ^ 3 * M' * e := by ring
    have h11 : 3 * B ^ 3 * e ≤ 3 * B ^ 3 * M' * e := by
      have h12 : e ≤ M' * e := le_mul_of_one_le_left (le_of_lt hepos) hM'1
      calc 3 * B ^ 3 * e = (3 * B ^ 3) * e := by ring
        _ ≤ (3 * B ^ 3) * (M' * e) := mul_le_mul_of_nonneg_left h12 (by positivity)
        _ = 3 * B ^ 3 * M' * e := by ring
    have h0 : (0:ℝ) ≤ B ^ 3 * M' * e := by positivity
    linarith [h1, h2, h8, h9, h11, h0]
  have hCorr : ‖PhiCorr τ z‖ ≤ 24 * B ^ 4 * M' ^ 4 * (1 + t) ^ 2 * e := by
    rw [PhiCorr]
    have hnum : ‖(τ : ℂ) * E6Fun τ * phitVec z 2
          * (E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)
        - 2 * phi0 τ * E4Fun τ * phitVec z 1
          * (E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)‖
        ≤ 12 * B ^ 4 * M' ^ 4 * (1 + t) ^ 2 * e := by
      refine le_trans (norm_sub_le _ _) ?_
      have hτ6 : ‖(τ : ℂ) * E6Fun τ‖ ≤ M' ^ 2 := by
        rw [norm_mul]
        calc ‖(τ : ℂ)‖ * ‖E6Fun τ‖ ≤ M' * M' :=
              mul_le_mul (le_trans hτ hM'M) (le_trans hE6 hM'M) (norm_nonneg _) (by positivity)
          _ = M' ^ 2 := by ring
      have hn1 : ‖(τ : ℂ) * E6Fun τ * phitVec z 2
            * (E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)‖
          ≤ 3 * B ^ 4 * M' ^ 4 * (1 + t) ^ 2 * e := by
        rw [norm_mul, norm_mul]
        have hstep : ‖(τ : ℂ) * E6Fun τ‖ * ‖phitVec z 2‖
              * ‖E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ‖
            ≤ M' ^ 2 * (B * (1 + t) ^ 2) * (3 * B ^ 3 * M' * e) :=
          mul_le_mul (mul_le_mul hτ6 hbt2 (norm_nonneg _) (by positivity)) hE8all
            (norm_nonneg _) (by positivity)
        refine le_trans hstep ?_
        have hM4 : M' ^ 3 ≤ M' ^ 4 := pow_three_le_pow_four hM'1
        calc M' ^ 2 * (B * (1 + t) ^ 2) * (3 * B ^ 3 * M' * e)
            = 3 * B ^ 4 * M' ^ 3 * (1 + t) ^ 2 * e := by ring
          _ ≤ 3 * B ^ 4 * M' ^ 4 * (1 + t) ^ 2 * e := by
              calc 3 * B ^ 4 * M' ^ 3 * (1 + t) ^ 2 * e
                  = (3 * B ^ 4 * (1 + t) ^ 2 * e) * M' ^ 3 := by ring
                _ ≤ (3 * B ^ 4 * (1 + t) ^ 2 * e) * M' ^ 4 :=
                    mul_le_mul_of_nonneg_left hM4 (by positivity)
                _ = 3 * B ^ 4 * M' ^ 4 * (1 + t) ^ 2 * e := by ring
      have hn2 : ‖2 * phi0 τ * E4Fun τ * phitVec z 1
            * (E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)‖
          ≤ 8 * B ^ 4 * M' ^ 4 * (1 + t) ^ 2 * e := by
        simp only [norm_mul]
        rw [show ‖(2:ℂ)‖ = 2 by norm_num]
        have hstep : 2 * ‖phi0 τ‖ * ‖E4Fun τ‖ * ‖phitVec z 1‖
              * ‖E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ‖
            ≤ 2 * M' * M' * (B * (1 + t) ^ 2) * (4 * B ^ 3 * M' * e) := by
          exact mul4_le_mul4 (mul_le_mul_of_nonneg_left (le_trans hφ0 hM'M) (by norm_num))
            (le_trans hE4 hM'M) hbt1 hE10all (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
            (by positivity) (by positivity) (by positivity)
        refine le_trans hstep ?_
        have hM4 : M' ^ 3 ≤ M' ^ 4 := pow_three_le_pow_four hM'1
        calc 2 * M' * M' * (B * (1 + t) ^ 2) * (4 * B ^ 3 * M' * e)
            = 8 * B ^ 4 * M' ^ 3 * (1 + t) ^ 2 * e := by ring
          _ ≤ 8 * B ^ 4 * M' ^ 4 * (1 + t) ^ 2 * e := by
              calc 8 * B ^ 4 * M' ^ 3 * (1 + t) ^ 2 * e
                  = (8 * B ^ 4 * (1 + t) ^ 2 * e) * M' ^ 3 := by ring
                _ ≤ (8 * B ^ 4 * (1 + t) ^ 2 * e) * M' ^ 4 :=
                    mul_le_mul_of_nonneg_left hM4 (by positivity)
                _ = 8 * B ^ 4 * M' ^ 4 * (1 + t) ^ 2 * e := by ring
      have h0 : (0:ℝ) ≤ B ^ 4 * M' ^ 4 * (1 + t) ^ 2 * e := by positivity
      linarith [hn1, hn2, h0]
    calc ‖((τ : ℂ) * E6Fun τ * phitVec z 2
            * (E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)
          - 2 * phi0 τ * E4Fun τ * phitVec z 1
            * (E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ))
          / (DeltaFun z * (jInvariantFun τ - jInvariantFun z))‖
        = ‖(τ : ℂ) * E6Fun τ * phitVec z 2
            * (E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)
          - 2 * phi0 τ * E4Fun τ * phitVec z 1
            * (E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)‖
            / ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ := norm_div _ _
      _ ≤ ‖(τ : ℂ) * E6Fun τ * phitVec z 2
            * (E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)
          - 2 * phi0 τ * E4Fun τ * phitVec z 1
            * (E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)‖ / (1/2) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hDJge
      _ = 2 * ‖(τ : ℂ) * E6Fun τ * phitVec z 2
            * (E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)
          - 2 * phi0 τ * E4Fun τ * phitVec z 1
            * (E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)‖ := by ring
      _ ≤ 24 * B ^ 4 * M' ^ 4 * (1 + t) ^ 2 * e := by linarith [hnum]
  -- assembly
  have hsum : ‖PhiMain τ z + PhiDiv τ z + PhiCorr τ z‖
      ≤ (8 * B ^ 2 * M' ^ 2 + 2 * B ^ 2 * M' ^ 2 + 24 * B ^ 4 * M' ^ 4) * (1 + t) ^ 2 * e := by
    have h1 := norm_add_le (PhiMain τ z + PhiDiv τ z) (PhiCorr τ z)
    have h2 := norm_add_le (PhiMain τ z) (PhiDiv τ z)
    have h3 : 8 * B ^ 2 * M' ^ 2 * (1 + t) ^ 2 * e + 2 * B ^ 2 * M' ^ 2 * (1 + t) ^ 2 * e
        = (8 * B ^ 2 * M' ^ 2 + 2 * B ^ 2 * M' ^ 2) * (1 + t) ^ 2 * e := by ring
    have h4 : (8 * B ^ 2 * M' ^ 2 + 2 * B ^ 2 * M' ^ 2) * (1 + t) ^ 2 * e
          + 24 * B ^ 4 * M' ^ 4 * (1 + t) ^ 2 * e
        = (8 * B ^ 2 * M' ^ 2 + 2 * B ^ 2 * M' ^ 2 + 24 * B ^ 4 * M' ^ 4) * (1 + t) ^ 2 * e := by
      ring
    linarith [h1, h2, hMain, hDiv, hCorr, h3, h4]
  have hdecomp := KPlus8_sub_Gplus8_decomp τ z (sub_ne_zero.mp hJne)
  rw [hdecomp, norm_mul]
  have hTC : (0:ℝ) ≤ ‖tailC⁻¹‖ := norm_nonneg _
  have hA1 : (0:ℝ) ≤ 8 * B ^ 2 * M' ^ 2 + 2 * B ^ 2 * M' ^ 2 + 24 * B ^ 4 * M' ^ 4 := by positivity
  calc ‖tailC⁻¹‖ * ‖PhiMain τ z + PhiDiv τ z + PhiCorr τ z‖
      ≤ ‖tailC⁻¹‖ * ((8 * B ^ 2 * M' ^ 2 + 2 * B ^ 2 * M' ^ 2 + 24 * B ^ 4 * M' ^ 4)
          * (1 + t) ^ 2 * e) := mul_le_mul_of_nonneg_left hsum hTC
    _ ≤ (‖tailC⁻¹‖ * (8 * B ^ 2 * M' ^ 2 + 2 * B ^ 2 * M' ^ 2 + 24 * B ^ 4 * M' ^ 4) + 1)
          * (1 + t) ^ 2 * e := by
        have hx : (0:ℝ) ≤ (1 + t) ^ 2 * e := by positivity
        nlinarith [hTC, hA1, hx]

/-- **The requested lemma.** -/
theorem kplus8_tail_core {M : ℝ} (hM : 0 < M) : ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ (τ : UpperHalfPlane), ‖(τ : ℂ)‖ ≤ M → ‖Work.Kernels.phi0 τ‖ ≤ M → ‖Work.Kernels.phi2 τ‖ ≤ M → ‖Work.Kernels.E4Fun τ‖ ≤ M → ‖Work.Kernels.E6Fun τ‖ ≤ M → ‖Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ‖ ≤ M → ‖Work.Kernels.jInvariantFun τ‖ ≤ M → ∀ (t : ℝ) (ht : 0 < t), T ≤ t → ‖Work.Kernels.KPlus 8 τ (Work.Kernels.imagAxis t ht) - Work.Asymptotics.Compact.Gplus8 τ (Work.Kernels.imagAxis t ht)‖ ≤ C * (1 + t) ^ 2 * Real.exp (-(Real.pi * t)) := by
  obtain ⟨A, T, hA, hT, hbound⟩ := kplus8_diff_bound hM
  refine ⟨A, T, hA, hT, ?_⟩
  intro τ hτ hφ0 hφ2 hE4 hE6 hE14 hj t ht hTt
  have h1 := hbound τ t ht hTt hτ hφ0 hφ2 hE4 hE6 hE14 hj
  refine le_trans h1 ?_
  have he : Real.exp (-(2 * Real.pi * t)) ≤ Real.exp (-(Real.pi * t)) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, le_of_lt ht]
  have h0 : (0:ℝ) ≤ A * (1 + t) ^ 2 := by positivity
  calc A * (1 + t) ^ 2 * Real.exp (-(2 * Real.pi * t))
      ≤ A * (1 + t) ^ 2 * Real.exp (-(Real.pi * t)) := mul_le_mul_of_nonneg_left he h0
    _ = A * (1 + t) ^ 2 * Real.exp (-(Real.pi * t)) := rfl

end

end Work.Asymptotics.Compact

