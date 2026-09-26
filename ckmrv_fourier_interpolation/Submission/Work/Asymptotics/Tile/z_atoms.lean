import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Residues.E6FunSecondOrder
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Residues.ThetaDecay
import Submission.Work.Residues.LogLambdaBound
import Submission.Work.Asymptotics.Tile.DeltaFun_lower_region

namespace Work.Asymptotics.Tile

open UpperHalfPlane

noncomputable section

/-! ## Elementary estimates for the exponential

These two helpers convert the decay statements of `Work.Residues.ThetaDecay` into plain
boundedness statements, and provide the inverse-exponential identity used to compare a
quotient `f/Δ` with `f · Δ⁻¹`. -/

/-- `e^{-x} ≤ 1` for `x ≥ 0`. -/
private lemma exp_neg_le_one {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) ≤ 1 := by
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by linarith)

/-- `(e^{-x})⁻¹ = e^{x}`. -/
private lemma inv_exp_neg (x : ℝ) : (Real.exp (-x))⁻¹ = Real.exp x := by
  rw [Real.exp_neg]
  simp

/-- `(c e^{-x})⁻¹ = c⁻¹ e^{x}`. -/
private lemma inv_mul_exp_neg (c x : ℝ) : (c * Real.exp (-x))⁻¹ = c⁻¹ * Real.exp x := by
  rw [mul_inv, inv_exp_neg]

/-- If `‖f - 1‖` decays like `e^{-a π Im}` with `a ≥ 0`, then `f` is bounded by `C + 1`. -/
private lemma norm_le_one_add_of_norm_sub_one_le {f : ℍ → ℂ} {C a : ℝ} (hC : 0 < C)
    (ha : 0 ≤ a)
    (h : ∀ z : ℍ, 1 ≤ z.im → ‖f z - 1‖ ≤ C * Real.exp (-(a * Real.pi * z.im))) :
    ∀ z : ℍ, 1 ≤ z.im → ‖f z‖ ≤ C + 1 := by
  intro z hz
  have hnn : 0 ≤ a * Real.pi * z.im :=
    mul_nonneg (mul_nonneg ha Real.pi_pos.le) z.im_pos.le
  have hE : Real.exp (-(a * Real.pi * z.im)) ≤ 1 := exp_neg_le_one hnn
  have h1 : ‖f z - 1‖ ≤ C := by
    calc ‖f z - 1‖ ≤ C * Real.exp (-(a * Real.pi * z.im)) := h z hz
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hE hC.le
      _ = C := mul_one C
  calc ‖f z‖ = ‖(f z - 1) + 1‖ := by congr 1; ring
    _ ≤ ‖f z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ = ‖f z - 1‖ + 1 := by simp
    _ ≤ C + 1 := by linarith

/-! ## Boundedness on `Im ≥ 1` -/

private theorem atoms_bounded : ∃ C : ℝ, 0 < C ∧
    (∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.E4Fun z‖ ≤ C) ∧
    (∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.E6Fun z‖ ≤ C) ∧
    (∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.E8Fun z‖ ≤ C) ∧
    (∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.E10Fun z‖ ≤ C) ∧
    (∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.E14Fun z‖ ≤ C) ∧
    (∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.UFun z‖ ≤ C) ∧
    (∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.WFun z‖ ≤ C) := by
  obtain ⟨C4, hC4, h4⟩ := Work.Residues.E4Fun_decay
  obtain ⟨C6, hC6, h6⟩ := Work.Residues.E6Fun_decay
  obtain ⟨CU, hCU, hU⟩ := Work.Residues.UFun_decay
  obtain ⟨CW, hCW, hW⟩ := Work.Residues.WFun_decay
  have h4p : 0 < C4 + 1 := by linarith
  have h6p : 0 < C6 + 1 := by linarith
  have hUp : 0 < CU + 1 := by linarith
  have hWp : 0 < CW + 1 := by linarith
  have k3 : 0 < (C4 + 1) ^ 2 := pow_pos h4p 2
  have k4 : 0 < (C4 + 1) * (C6 + 1) := mul_pos h4p h6p
  have k5 : 0 < (C4 + 1) ^ 2 * (C6 + 1) := mul_pos k3 h6p
  have hE4 := norm_le_one_add_of_norm_sub_one_le (f := Work.Kernels.E4Fun)
    hC4 (by norm_num : (0 : ℝ) ≤ 2) h4
  have hE6 := norm_le_one_add_of_norm_sub_one_le (f := Work.Kernels.E6Fun)
    hC6 (by norm_num : (0 : ℝ) ≤ 2) h6
  have hU' : ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Kernels.UFun z - 1‖ ≤ CU * Real.exp (-(1 * Real.pi * z.im)) := by
    intro z hz; simpa using hU z hz
  have hW' : ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Kernels.WFun z - 1‖ ≤ CW * Real.exp (-(1 * Real.pi * z.im)) := by
    intro z hz; simpa using hW z hz
  have hU1 := norm_le_one_add_of_norm_sub_one_le (f := Work.Kernels.UFun)
    hCU (by norm_num : (0 : ℝ) ≤ 1) hU'
  have hW1 := norm_le_one_add_of_norm_sub_one_le (f := Work.Kernels.WFun)
    hCW (by norm_num : (0 : ℝ) ≤ 1) hW'
  refine ⟨1 + (C4 + 1) + (C6 + 1) + (C4 + 1) ^ 2 + (C4 + 1) * (C6 + 1)
    + (C4 + 1) ^ 2 * (C6 + 1) + (CU + 1) + (CW + 1), by linarith,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have h := hE4 z hz
    linarith [h, h6p, k3, k4, k5, hUp, hWp]
  · intro z hz
    have h := hE6 z hz
    linarith [h, h4p, k3, k4, k5, hUp, hWp]
  · intro z hz
    have h := hE4 z hz
    have h8 : Work.Kernels.E8Fun z = Work.Kernels.E4Fun z ^ 2 := rfl
    rw [h8, norm_pow]
    have h2 : ‖Work.Kernels.E4Fun z‖ ^ 2 ≤ (C4 + 1) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    linarith [h2, k3, k4, k5, h6p, hUp, hWp]
  · intro z hz
    have hA := hE4 z hz
    have hB := hE6 z hz
    have h10 : Work.Kernels.E10Fun z = Work.Kernels.E4Fun z * Work.Kernels.E6Fun z := rfl
    rw [h10, norm_mul]
    have := mul_le_mul hA hB (norm_nonneg _) h4p.le
    linarith [this, h4p, h6p, k5, hUp, hWp]
  · intro z hz
    have hA := hE4 z hz
    have hB := hE6 z hz
    have h14 : Work.Kernels.E14Fun z = Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z := rfl
    rw [h14, norm_mul, norm_pow]
    have hA2 : ‖Work.Kernels.E4Fun z‖ ^ 2 ≤ (C4 + 1) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hA 2
    have := mul_le_mul hA2 hB (norm_nonneg _) k3.le
    linarith [this, h4p, h6p, hUp, hWp]
  · intro z hz
    have h := hU1 z hz
    linarith [h, h4p, h6p, k3, k4, k5, hWp]
  · intro z hz
    have h := hW1 z hz
    linarith [h, h4p, h6p, k3, k4, k5, hUp]

/-! ## Exponential decay of `V`, of `U² - W²` and of `𝓛_S` -/

private theorem atoms_decay (ℓ : Work.Kernels.LogLambdaData) : ∃ C : ℝ, 0 < C ∧
    (∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.VFun z‖ ≤ C * Real.exp (-(Real.pi * z.im))) ∧
    (∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2‖ ≤ C * Real.exp (-(Real.pi * z.im))) ∧
    (∀ z : ℍ, 1 ≤ z.im → ‖ℓ.L_S z‖ ≤ C * Real.exp (-(Real.pi * z.im))) := by
  obtain ⟨CV, hCV, hV⟩ := Work.Residues.VFun_decay
  obtain ⟨CL, hCL, hLS⟩ := (Work.Residues.LogLambdaBound ℓ).2
  obtain ⟨CU, hCU, hU⟩ := Work.Residues.UFun_decay
  obtain ⟨CW, hCW, hW⟩ := Work.Residues.WFun_decay
  have hUp : 0 < CU + 1 := by linarith
  have hWp : 0 < CW + 1 := by linarith
  have hU' : ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Kernels.UFun z - 1‖ ≤ CU * Real.exp (-(1 * Real.pi * z.im)) := by
    intro z hz; simpa using hU z hz
  have hW' : ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Kernels.WFun z - 1‖ ≤ CW * Real.exp (-(1 * Real.pi * z.im)) := by
    intro z hz; simpa using hW z hz
  have hU1 : ∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.UFun z‖ ≤ CU + 1 :=
    norm_le_one_add_of_norm_sub_one_le hCU (by norm_num : (0 : ℝ) ≤ 1) hU'
  have hW1 : ∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.WFun z‖ ≤ CW + 1 :=
    norm_le_one_add_of_norm_sub_one_le hCW (by norm_num : (0 : ℝ) ≤ 1) hW'
  -- the two "square" bounds
  have hU2 : ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Kernels.UFun z ^ 2 - 1‖ ≤ CU * (CU + 2) * Real.exp (-(Real.pi * z.im)) := by
    intro z hz
    have h1 : ‖Work.Kernels.UFun z - 1‖ ≤ CU * Real.exp (-(Real.pi * z.im)) := hU z hz
    have h2 : ‖Work.Kernels.UFun z + 1‖ ≤ CU + 2 := by
      have := norm_add_le (Work.Kernels.UFun z) (1 : ℂ)
      have hb := hU1 z hz
      simp only [norm_one] at this
      linarith
    have hE : 0 ≤ Real.exp (-(Real.pi * z.im)) := Real.exp_nonneg _
    have hfac : Work.Kernels.UFun z ^ 2 - 1 =
        (Work.Kernels.UFun z - 1) * (Work.Kernels.UFun z + 1) := by ring
    calc ‖Work.Kernels.UFun z ^ 2 - 1‖
        = ‖(Work.Kernels.UFun z - 1) * (Work.Kernels.UFun z + 1)‖ := by rw [hfac]
      _ = ‖Work.Kernels.UFun z - 1‖ * ‖Work.Kernels.UFun z + 1‖ := norm_mul _ _
      _ ≤ (CU * Real.exp (-(Real.pi * z.im))) * (CU + 2) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = CU * (CU + 2) * Real.exp (-(Real.pi * z.im)) := by ring
  have hW2 : ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Kernels.WFun z ^ 2 - 1‖ ≤ CW * (CW + 2) * Real.exp (-(Real.pi * z.im)) := by
    intro z hz
    have h1 : ‖Work.Kernels.WFun z - 1‖ ≤ CW * Real.exp (-(Real.pi * z.im)) := hW z hz
    have h2 : ‖Work.Kernels.WFun z + 1‖ ≤ CW + 2 := by
      have := norm_add_le (Work.Kernels.WFun z) (1 : ℂ)
      have hb := hW1 z hz
      simp only [norm_one] at this
      linarith
    have hfac : Work.Kernels.WFun z ^ 2 - 1 =
        (Work.Kernels.WFun z - 1) * (Work.Kernels.WFun z + 1) := by ring
    calc ‖Work.Kernels.WFun z ^ 2 - 1‖
        = ‖(Work.Kernels.WFun z - 1) * (Work.Kernels.WFun z + 1)‖ := by rw [hfac]
      _ = ‖Work.Kernels.WFun z - 1‖ * ‖Work.Kernels.WFun z + 1‖ := norm_mul _ _
      _ ≤ (CW * Real.exp (-(Real.pi * z.im))) * (CW + 2) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = CW * (CW + 2) * Real.exp (-(Real.pi * z.im)) := by ring
  have k2 : 0 < CU * (CU + 2) + CW * (CW + 2) := by
    have h1 : 0 < CU * (CU + 2) := mul_pos hCU (by linarith)
    have h2 : 0 < CW * (CW + 2) := mul_pos hCW (by linarith)
    linarith
  refine ⟨CV + (CU * (CU + 2) + CW * (CW + 2)) + CL + 1, by linarith, ?_, ?_, ?_⟩
  · intro z hz
    have h := hV z hz
    have hle : CV ≤ CV + (CU * (CU + 2) + CW * (CW + 2)) + CL + 1 := by linarith
    exact h.trans (mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _))
  · intro z hz
    have h1 := hU2 z hz
    have h2 := hW2 z hz
    have hsub : Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2
        = (Work.Kernels.UFun z ^ 2 - 1) - (Work.Kernels.WFun z ^ 2 - 1) := by ring
    have hle : CU * (CU + 2) + CW * (CW + 2)
        ≤ CV + (CU * (CU + 2) + CW * (CW + 2)) + CL + 1 := by linarith [hCV, hCL]
    calc ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2‖
        = ‖(Work.Kernels.UFun z ^ 2 - 1) - (Work.Kernels.WFun z ^ 2 - 1)‖ := by rw [hsub]
      _ ≤ ‖Work.Kernels.UFun z ^ 2 - 1‖ + ‖Work.Kernels.WFun z ^ 2 - 1‖ := norm_sub_le _ _
      _ ≤ CU * (CU + 2) * Real.exp (-(Real.pi * z.im))
            + CW * (CW + 2) * Real.exp (-(Real.pi * z.im)) := add_le_add h1 h2
      _ = (CU * (CU + 2) + CW * (CW + 2)) * Real.exp (-(Real.pi * z.im)) := by ring
      _ ≤ (CV + (CU * (CU + 2) + CW * (CW + 2)) + CL + 1)
            * Real.exp (-(Real.pi * z.im)) :=
          mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)
  · intro z hz
    have h := hLS z hz
    have hle : CL ≤ CV + (CU * (CU + 2) + CW * (CW + 2)) + CL + 1 := by linarith
    exact h.trans (mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _))

/-! ## Exponential growth of `Δ⁻¹`, `j`, `E₁₄/Δ`, `E₁₀/Δ` -/

private theorem atoms_growth : ∃ C : ℝ, 0 < C ∧
    (∀ z : ℍ, 1 ≤ z.im → ‖(Work.Kernels.DeltaFun z)⁻¹‖ ≤ C * Real.exp (2 * Real.pi * z.im)) ∧
    (∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Kernels.jInvariantFun z‖ ≤ C * Real.exp (2 * Real.pi * z.im)) ∧
    (∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z‖
      ≤ C * Real.exp (2 * Real.pi * z.im)) ∧
    (∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z‖
      ≤ C * Real.exp (2 * Real.pi * z.im)) := by
  obtain ⟨C4, hC4, h4⟩ := Work.Residues.E4Fun_decay
  obtain ⟨C6, hC6, h6⟩ := Work.Residues.E6Fun_decay
  obtain ⟨Cd, hCd, hDlo⟩ := DeltaFun_lower_region
  have h4p : 0 < C4 + 1 := by linarith
  have h6p : 0 < C6 + 1 := by linarith
  have hE4 : ∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.E4Fun z‖ ≤ C4 + 1 :=
    norm_le_one_add_of_norm_sub_one_le hC4 (by norm_num : (0 : ℝ) ≤ 2) h4
  have hE6 : ∀ z : ℍ, 1 ≤ z.im → ‖Work.Kernels.E6Fun z‖ ≤ C6 + 1 :=
    norm_le_one_add_of_norm_sub_one_le hC6 (by norm_num : (0 : ℝ) ≤ 2) h6
  have hE14 : ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Kernels.E14Fun z‖ ≤ (C4 + 1) ^ 2 * (C6 + 1) := by
    intro z hz
    have hA := hE4 z hz
    have hB := hE6 z hz
    have h14 : Work.Kernels.E14Fun z = Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z := rfl
    rw [h14, norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hA 2) hB (norm_nonneg _) (pow_nonneg h4p.le 2)
  have hE10 : ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Kernels.E10Fun z‖ ≤ (C4 + 1) * (C6 + 1) := by
    intro z hz
    have hA := hE4 z hz
    have hB := hE6 z hz
    have h10 : Work.Kernels.E10Fun z = Work.Kernels.E4Fun z * Work.Kernels.E6Fun z := rfl
    rw [h10, norm_mul]
    exact mul_le_mul hA hB (norm_nonneg _) h4p.le
  have hdi : 0 < Cd⁻¹ := inv_pos.mpr hCd
  have k2 : 0 < (C4 + 1) ^ 3 * Cd⁻¹ := mul_pos (pow_pos h4p 3) hdi
  have k3 : 0 < (C4 + 1) ^ 2 * (C6 + 1) * Cd⁻¹ :=
    mul_pos (mul_pos (pow_pos h4p 2) h6p) hdi
  have k4 : 0 < (C4 + 1) * (C6 + 1) * Cd⁻¹ := mul_pos (mul_pos h4p h6p) hdi
  refine ⟨Cd⁻¹ + (C4 + 1) ^ 3 * Cd⁻¹ + (C4 + 1) ^ 2 * (C6 + 1) * Cd⁻¹
    + (C4 + 1) * (C6 + 1) * Cd⁻¹ + 1, by linarith, ?_, ?_, ?_, ?_⟩
  · -- `Δ⁻¹`
    intro z hz
    have hm : 0 < Cd * Real.exp (-(2 * Real.pi * z.im)) := mul_pos hCd (Real.exp_pos _)
    have h1 : (‖Work.Kernels.DeltaFun z‖)⁻¹
        ≤ (Cd * Real.exp (-(2 * Real.pi * z.im)))⁻¹ := inv_anti₀ hm (hDlo z hz)
    rw [← norm_inv, inv_mul_exp_neg] at h1
    have hle : Cd⁻¹ ≤ Cd⁻¹ + (C4 + 1) ^ 3 * Cd⁻¹ + (C4 + 1) ^ 2 * (C6 + 1) * Cd⁻¹
        + (C4 + 1) * (C6 + 1) * Cd⁻¹ + 1 := by linarith [k2, k3, k4]
    exact h1.trans (mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _))
  · -- `j`
    intro z hz
    have hm : 0 < Cd * Real.exp (-(2 * Real.pi * z.im)) := mul_pos hCd (Real.exp_pos _)
    have hinv : (‖Work.Kernels.DeltaFun z‖)⁻¹
        ≤ (Cd * Real.exp (-(2 * Real.pi * z.im)))⁻¹ := inv_anti₀ hm (hDlo z hz)
    have hnum : ‖Work.Kernels.E4Fun z ^ 3‖ ≤ (C4 + 1) ^ 3 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hE4 z hz) 3
    have hmono : ‖Work.Kernels.E4Fun z ^ 3‖ * (‖Work.Kernels.DeltaFun z‖)⁻¹
        ≤ (C4 + 1) ^ 3 * (Cd * Real.exp (-(2 * Real.pi * z.im)))⁻¹ :=
      mul_le_mul hnum hinv (by positivity) (by positivity)
    rw [show Work.Kernels.jInvariantFun z
          = Work.Kernels.E4Fun z ^ 3 / Work.Kernels.DeltaFun z from rfl,
      norm_div, div_eq_mul_inv]
    have hval : (C4 + 1) ^ 3 * (Cd * Real.exp (-(2 * Real.pi * z.im)))⁻¹
        = ((C4 + 1) ^ 3 * Cd⁻¹) * Real.exp (2 * Real.pi * z.im) := by
      rw [inv_mul_exp_neg]; ring
    have hle : (C4 + 1) ^ 3 * Cd⁻¹ ≤ Cd⁻¹ + (C4 + 1) ^ 3 * Cd⁻¹
        + (C4 + 1) ^ 2 * (C6 + 1) * Cd⁻¹ + (C4 + 1) * (C6 + 1) * Cd⁻¹ + 1 := by
      linarith [hdi, k3, k4]
    exact (hmono.trans_eq hval).trans
      (mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _))
  · -- `E₁₄/Δ`
    intro z hz
    have hm : 0 < Cd * Real.exp (-(2 * Real.pi * z.im)) := mul_pos hCd (Real.exp_pos _)
    have hinv : (‖Work.Kernels.DeltaFun z‖)⁻¹
        ≤ (Cd * Real.exp (-(2 * Real.pi * z.im)))⁻¹ := inv_anti₀ hm (hDlo z hz)
    have hnum := hE14 z hz
    have hmono : ‖Work.Kernels.E14Fun z‖ * (‖Work.Kernels.DeltaFun z‖)⁻¹
        ≤ ((C4 + 1) ^ 2 * (C6 + 1)) * (Cd * Real.exp (-(2 * Real.pi * z.im)))⁻¹ :=
      mul_le_mul hnum hinv (by positivity) (by positivity)
    rw [norm_div, div_eq_mul_inv]
    have hval : ((C4 + 1) ^ 2 * (C6 + 1)) * (Cd * Real.exp (-(2 * Real.pi * z.im)))⁻¹
        = (((C4 + 1) ^ 2 * (C6 + 1)) * Cd⁻¹) * Real.exp (2 * Real.pi * z.im) := by
      rw [inv_mul_exp_neg]; ring
    have hle : (C4 + 1) ^ 2 * (C6 + 1) * Cd⁻¹ ≤ Cd⁻¹ + (C4 + 1) ^ 3 * Cd⁻¹
        + (C4 + 1) ^ 2 * (C6 + 1) * Cd⁻¹ + (C4 + 1) * (C6 + 1) * Cd⁻¹ + 1 := by
      linarith [hdi, k2, k4]
    exact (hmono.trans_eq hval).trans
      (mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _))
  · -- `E₁₀/Δ`
    intro z hz
    have hm : 0 < Cd * Real.exp (-(2 * Real.pi * z.im)) := mul_pos hCd (Real.exp_pos _)
    have hinv : (‖Work.Kernels.DeltaFun z‖)⁻¹
        ≤ (Cd * Real.exp (-(2 * Real.pi * z.im)))⁻¹ := inv_anti₀ hm (hDlo z hz)
    have hnum := hE10 z hz
    have hmono : ‖Work.Kernels.E10Fun z‖ * (‖Work.Kernels.DeltaFun z‖)⁻¹
        ≤ ((C4 + 1) * (C6 + 1)) * (Cd * Real.exp (-(2 * Real.pi * z.im)))⁻¹ :=
      mul_le_mul hnum hinv (by positivity) (by positivity)
    rw [norm_div, div_eq_mul_inv]
    have hval : ((C4 + 1) * (C6 + 1)) * (Cd * Real.exp (-(2 * Real.pi * z.im)))⁻¹
        = (((C4 + 1) * (C6 + 1)) * Cd⁻¹) * Real.exp (2 * Real.pi * z.im) := by
      rw [inv_mul_exp_neg]; ring
    have hle : (C4 + 1) * (C6 + 1) * Cd⁻¹ ≤ Cd⁻¹ + (C4 + 1) ^ 3 * Cd⁻¹
        + (C4 + 1) ^ 2 * (C6 + 1) * Cd⁻¹ + (C4 + 1) * (C6 + 1) * Cd⁻¹ + 1 := by
      linarith [hdi, k2, k3]
    exact (hmono.trans_eq hval).trans
      (mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _))

/-! ## The assembled statement -/

theorem z_atoms (ℓ : Work.Kernels.LogLambdaData) : ∃ C : ℝ, 0 < C ∧
      (∀ z : UpperHalfPlane, 1 ≤ z.im → ‖Work.Kernels.E4Fun z‖ ≤ C) ∧
      (∀ z : UpperHalfPlane, 1 ≤ z.im → ‖Work.Kernels.E6Fun z‖ ≤ C) ∧
      (∀ z : UpperHalfPlane, 1 ≤ z.im → ‖Work.Kernels.E8Fun z‖ ≤ C) ∧
      (∀ z : UpperHalfPlane, 1 ≤ z.im → ‖Work.Kernels.E10Fun z‖ ≤ C) ∧
      (∀ z : UpperHalfPlane, 1 ≤ z.im → ‖Work.Kernels.E14Fun z‖ ≤ C) ∧
      (∀ z : UpperHalfPlane, 1 ≤ z.im → ‖Work.Kernels.UFun z‖ ≤ C) ∧
      (∀ z : UpperHalfPlane, 1 ≤ z.im → ‖Work.Kernels.WFun z‖ ≤ C) ∧
      (∀ z : UpperHalfPlane, 1 ≤ z.im → ‖Work.Kernels.VFun z‖ ≤ C * Real.exp (-(Real.pi * z.im))) ∧
      (∀ z : UpperHalfPlane, 1 ≤ z.im → ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2‖
        ≤ C * Real.exp (-(Real.pi * z.im))) ∧
      (∀ z : UpperHalfPlane, 1 ≤ z.im → ‖ℓ.L_S z‖ ≤ C * Real.exp (-(Real.pi * z.im))) ∧
      (∀ z : UpperHalfPlane, 1 ≤ z.im → ‖(Work.Kernels.DeltaFun z)⁻¹‖ ≤ C * Real.exp (2 * Real.pi * z.im)) ∧
      (∀ z : UpperHalfPlane, 1 ≤ z.im → ‖Work.Kernels.jInvariantFun z‖ ≤ C * Real.exp (2 * Real.pi * z.im)) ∧
      (∀ z : UpperHalfPlane, 1 ≤ z.im → ‖Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z‖
        ≤ C * Real.exp (2 * Real.pi * z.im)) ∧
      (∀ z : UpperHalfPlane, 1 ≤ z.im → ‖Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z‖
        ≤ C * Real.exp (2 * Real.pi * z.im)) := by
  obtain ⟨C1, hC1, hE4b, hE6b, hE8b, hE10b, hE14b, hUb, hWb⟩ := atoms_bounded
  obtain ⟨C2, hC2, hVd, hUWd, hLSd⟩ := atoms_decay ℓ
  obtain ⟨C3, hC3, hDinv, hJ, hE14D, hE10D⟩ := atoms_growth
  refine ⟨C1 + C2 + C3 + 1, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz; have h := hE4b z hz; linarith [h, hC2, hC3]
  · intro z hz; have h := hE6b z hz; linarith [h, hC2, hC3]
  · intro z hz; have h := hE8b z hz; linarith [h, hC2, hC3]
  · intro z hz; have h := hE10b z hz; linarith [h, hC2, hC3]
  · intro z hz; have h := hE14b z hz; linarith [h, hC2, hC3]
  · intro z hz; have h := hUb z hz; linarith [h, hC2, hC3]
  · intro z hz; have h := hWb z hz; linarith [h, hC2, hC3]
  · intro z hz
    have h := hVd z hz
    have hle : C2 ≤ C1 + C2 + C3 + 1 := by linarith
    exact h.trans (mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _))
  · intro z hz
    have h := hUWd z hz
    have hle : C2 ≤ C1 + C2 + C3 + 1 := by linarith
    exact h.trans (mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _))
  · intro z hz
    have h := hLSd z hz
    have hle : C2 ≤ C1 + C2 + C3 + 1 := by linarith
    exact h.trans (mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _))
  · intro z hz
    have h := hDinv z hz
    have hle : C3 ≤ C1 + C2 + C3 + 1 := by linarith
    exact h.trans (mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _))
  · intro z hz
    have h := hJ z hz
    have hle : C3 ≤ C1 + C2 + C3 + 1 := by linarith
    exact h.trans (mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _))
  · intro z hz
    have h := hE14D z hz
    have hle : C3 ≤ C1 + C2 + C3 + 1 := by linarith
    exact h.trans (mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _))
  · intro z hz
    have h := hE10D z hz
    have hle : C3 ≤ C1 + C2 + C3 + 1 := by linarith
    exact h.trans (mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _))

end

end Work.Asymptotics.Tile
