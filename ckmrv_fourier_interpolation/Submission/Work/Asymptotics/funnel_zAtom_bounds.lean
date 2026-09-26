import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.E4Fun_sub_one_explicit
import Submission.Work.Asymptotics.Compact.zsmall
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.Asymptotics.E6_div_E4_sub_one_atom
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Residues.E6FunSecondOrder
import Submission.Work.Asymptotics.cusp_invDelta
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA

/-!
# The `z`-atoms of the funnel, on the imaginary axis `z = i t`, `t ≥ 3`

This file assembles the eleven first-order cusp bounds on the `z`-variable atoms
`E₄, E₆, E₁₄, E₄³, Δ, 1/Δ, q/Δ, E₂ˢ, E₆/E₄, 1/E₄` and `1/(1 - 6i/(πz))` which are needed
to control the funnel expansion.  All but the last two are first-order at the cusp: with
`q = qParamFun z = e^{2πiz}` they read `(atom) = (leading term) + O(q)`.

The cusp estimates themselves are taken from the `IsSmallT` toolkit of
`Submission/Work/Asymptotics/Compact/zsmall.lean`; the two numerical bounds
`‖1/E₄‖ ≤ 2` and `‖1/(1 - 6i/(πz))‖ ≤ 3` on the axis `z = i t`, `t ≥ 3`, are proved here
directly.
-/

namespace Work.Asymptotics

open UpperHalfPlane

noncomputable section

/-! ## Auxiliary facts -/

/-- On the imaginary axis the imaginary part is the parameter `t`. -/
lemma im_of_coe_eq_mul_I {z : UpperHalfPlane} {t : ℝ}
    (h : (z : ℂ) = (t : ℂ) * Complex.I) : z.im = t := by
  have h' := congrArg Complex.im h
  simpa [UpperHalfPlane.coe_im] using h'

/-- `E₁₄ - 1 = O(q)` at the cusp: `E₁₄ = E₄²E₆ = 1 - 24q + O(q²)`. -/
theorem E14_sub_one_small :
    Small.IsSmallT 1 (fun z => Work.Kernels.E14Fun z - 1) 1 := by
  have hE4p1 : Small.IsSmallT 1 (fun z => Work.Kernels.E4Fun z + 1) 0 := by
    have h := Small.E4_sub_one.add (le_refl 1)
      (Small.IsSmallT.bounded (f := fun _ : ℍ => (2 : ℂ)) 2 (by norm_num) (fun _ _ => by simp))
    exact h.congr (fun z => by ring)
  have hE6 : Small.IsSmallT 1 (fun z => Work.Kernels.E6Fun z) 0 := by
    have h := Small.E6_sub_one.add (le_refl 1)
      (Small.IsSmallT.bounded (f := fun _ : ℍ => (1 : ℂ)) 1 (by norm_num) (fun _ _ => by simp))
    exact h.congr (fun z => by ring)
  have h : Small.IsSmallT 1 (fun z => (Work.Kernels.E4Fun z - 1)
      * ((Work.Kernels.E4Fun z + 1) * Work.Kernels.E6Fun z) + (Work.Kernels.E6Fun z - 1)) 1 :=
    (Small.E4_sub_one.mul (le_refl 1) (hE4p1.mul (le_refl 1) hE6)).add (le_refl 1) Small.E6_sub_one
  refine h.congr (fun z => ?_)
  simp only [Work.Kernels.E14Fun]
  ring

/-- `q/Δ - 1 = O(q)`: equivalently `Δ/q = 1 + O(q)`. -/
theorem q_div_Delta_sub_one_small :
    Small.IsSmallT 1 (fun z => Work.Kernels.qParamFun z / Work.Kernels.DeltaFun z - 1) 1 := by
  obtain ⟨C, hC, h⟩ := Small.delta_inv_small
  refine ⟨24 + C + 1, by positivity, fun z hz => ?_⟩
  have h1 := h z hz
  rw [pow_one] at h1
  rw [pow_one]
  change ‖Work.Kernels.qParamFun z / Work.Kernels.DeltaFun z - 1‖
      ≤ (24 + C + 1) * ‖Work.Kernels.qParamFun z‖
  have hq0 : Work.Kernels.qParamFun z ≠ 0 := qParamFun_ne_zero' z
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := norm_qParamFun_le_one z hz
  have hqnn : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have key : Work.Kernels.qParamFun z / Work.Kernels.DeltaFun z - 1
      = 24 * Work.Kernels.qParamFun z
        + Work.Kernels.qParamFun z * ((Work.Kernels.DeltaFun z)⁻¹
            - (Work.Kernels.qParamFun z)⁻¹ - 24) := by
    rw [div_eq_mul_inv]
    field_simp
    ring
  rw [key]
  have h2 : ‖Work.Kernels.qParamFun z * ((Work.Kernels.DeltaFun z)⁻¹
      - (Work.Kernels.qParamFun z)⁻¹ - 24)‖
      ≤ ‖Work.Kernels.qParamFun z‖ * (C * ‖Work.Kernels.qParamFun z‖) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left h1 hqnn
  calc ‖24 * Work.Kernels.qParamFun z
        + Work.Kernels.qParamFun z * ((Work.Kernels.DeltaFun z)⁻¹
            - (Work.Kernels.qParamFun z)⁻¹ - 24)‖
      ≤ ‖24 * Work.Kernels.qParamFun z‖
        + ‖Work.Kernels.qParamFun z * ((Work.Kernels.DeltaFun z)⁻¹
            - (Work.Kernels.qParamFun z)⁻¹ - 24)‖ := norm_add_le _ _
    _ ≤ 24 * ‖Work.Kernels.qParamFun z‖
          + ‖Work.Kernels.qParamFun z‖ * (C * ‖Work.Kernels.qParamFun z‖) := by
        have h24 : ‖(24 : ℂ) * Work.Kernels.qParamFun z‖ = 24 * ‖Work.Kernels.qParamFun z‖ := by
          rw [norm_mul, Complex.norm_ofNat]
        rw [h24]
        linarith
    _ = (24 + C * ‖Work.Kernels.qParamFun z‖) * ‖Work.Kernels.qParamFun z‖ := by ring
    _ ≤ (24 + C + 1) * ‖Work.Kernels.qParamFun z‖ := by
        have hCq : C * ‖Work.Kernels.qParamFun z‖ ≤ C := by
          simpa using mul_le_mul_of_nonneg_left hq1 hC.le
        have h1' : (0 : ℝ) ≤ 1 + C - C * ‖Work.Kernels.qParamFun z‖ := by linarith
        nlinarith [mul_nonneg h1' hqnn]

/-- `‖1/(1 - 6i/(πz))‖ ≤ 3` on the imaginary axis `z = i t`, `t ≥ 3`. -/
lemma imagAxis_one_sub_inv_le {z : UpperHalfPlane} {t : ℝ} (ht : 3 ≤ t)
    (h : (z : ℂ) = (t : ℂ) * Complex.I) :
    ‖(1 - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ)))⁻¹‖ ≤ 3 := by
  have ht0 : (0 : ℝ) < t := by linarith
  set w : ℂ := 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ)) with hw
  have hwnorm : ‖w‖ ≤ 2 / 3 := by
    have h6 : ‖(6 : ℂ) * Complex.I‖ = 6 := by simp
    have hden : ‖(Real.pi : ℂ) * (z : ℂ)‖ = Real.pi * t := by
      rw [norm_mul, h, norm_mul]
      simp [abs_of_nonneg Real.pi_pos.le, abs_of_nonneg ht0.le]
    rw [hw, norm_div, h6, hden]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three, ht]
  have hge : (1 : ℝ) / 3 ≤ ‖1 - w‖ := by
    have hb := norm_sub_norm_le (1 : ℂ) w
    rw [norm_one] at hb
    linarith
  have hpos : 0 < ‖1 - w‖ := by linarith
  rw [norm_inv]
  calc ‖1 - w‖⁻¹ ≤ (1 / 3)⁻¹ := (inv_le_inv₀ hpos (by norm_num)).mpr hge
    _ = 3 := by norm_num

/-- `‖1/E₄‖ ≤ 2` for `Im z ≥ 3`. -/
lemma E4Fun_inv_norm_le (z : UpperHalfPlane) (hz : 3 ≤ z.im) :
    ‖(Work.Kernels.E4Fun z)⁻¹‖ ≤ 2 := by
  have hE4 : (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun z‖ :=
    Work.FunnelNumerics.E4_funnel_bounds.2 z hz
  have hpos : 0 < ‖Work.Kernels.E4Fun z‖ := by linarith
  rw [norm_inv, show (2 : ℝ) = (1 / 2)⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr hE4

/-! ## The atom bounds -/

/-- The eleven `z`-atom bounds on the imaginary axis `z = i t`, `t ≥ 3`. -/
theorem funnel_zAtom_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : UpperHalfPlane) (t : ℝ), 3 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Work.Kernels.E4Fun z - 1‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ∧
      ‖Work.Kernels.E6Fun z - 1‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ∧
      ‖Work.Kernels.E14Fun z - 1‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ∧
      ‖Work.Kernels.E4Fun z ^ 3 - 1‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ∧
      ‖Work.Kernels.DeltaFun z - Work.Kernels.qParamFun z‖
        ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 2 ∧
      ‖(Work.Kernels.DeltaFun z)⁻¹ - ((Work.Kernels.qParamFun z)⁻¹ + 24)‖
        ≤ C * ‖Work.Kernels.qParamFun z‖ ∧
      ‖Work.Kernels.qParamFun z / Work.Kernels.DeltaFun z - 1‖
        ≤ C * ‖Work.Kernels.qParamFun z‖ ∧
      ‖Work.Kernels.E2S z - (1 - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ)))‖
        ≤ C * ‖Work.Kernels.qParamFun z‖ ∧
      ‖Work.Kernels.E6Fun z / Work.Kernels.E4Fun z - 1‖
        ≤ C * ‖Work.Kernels.qParamFun z‖ ∧
      ‖(Work.Kernels.E4Fun z)⁻¹‖ ≤ 2 ∧
      ‖(1 - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ)))⁻¹‖ ≤ 3 := by
  obtain ⟨C1, hC1, h1⟩ := Small.E4_sub_one
  obtain ⟨C2, hC2, h2⟩ := Small.E6_sub_one
  obtain ⟨C3, hC3, h3⟩ := E14_sub_one_small
  obtain ⟨C4, hC4, h4⟩ := Small.E4_cube_sub_one
  obtain ⟨C5, hC5, h5⟩ := Small.delta_sub_q_second
  obtain ⟨C6, hC6, h6⟩ := Small.delta_inv_small
  obtain ⟨C7, hC7, h7⟩ := q_div_Delta_sub_one_small
  obtain ⟨C8, hC8, h8⟩ := Small.E2S_sub_S0c
  obtain ⟨C9, hC9, h9⟩ := E6_div_E4_sub_one_atom
  set Ctot : ℝ := 1 + C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + C9 with hCtot
  have hpos : 0 < Ctot := by rw [hCtot]; positivity
  have hC1le : C1 ≤ Ctot := by rw [hCtot]; linarith
  have hC2le : C2 ≤ Ctot := by rw [hCtot]; linarith
  have hC3le : C3 ≤ Ctot := by rw [hCtot]; linarith
  have hC4le : C4 ≤ Ctot := by rw [hCtot]; linarith
  have hC5le : C5 ≤ Ctot := by rw [hCtot]; linarith
  have hC6le : C6 ≤ Ctot := by rw [hCtot]; linarith
  have hC7le : C7 ≤ Ctot := by rw [hCtot]; linarith
  have hC8le : C8 ≤ Ctot := by rw [hCtot]; linarith
  have hC9le : C9 ≤ Ctot := by rw [hCtot]; linarith
  refine ⟨Ctot, hpos, fun z t ht hz => ?_⟩
  have hzim : z.im = t := im_of_coe_eq_mul_I hz
  have hz1 : 1 ≤ z.im := by rw [hzim]; linarith
  have hz3 : 3 ≤ z.im := by rw [hzim]; exact ht
  have hqnn : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc ‖Work.Kernels.E4Fun z - 1‖ ≤ C1 * ‖Work.Kernels.qParamFun z‖ := by
          simpa only [pow_one] using h1 z hz1
      _ ≤ Ctot * ‖Work.Kernels.qParamFun z‖ :=
          mul_le_mul_of_nonneg_right hC1le hqnn
  · calc ‖Work.Kernels.E6Fun z - 1‖ ≤ C2 * ‖Work.Kernels.qParamFun z‖ := by
          simpa only [pow_one] using h2 z hz1
      _ ≤ Ctot * ‖Work.Kernels.qParamFun z‖ :=
          mul_le_mul_of_nonneg_right hC2le hqnn
  · calc ‖Work.Kernels.E14Fun z - 1‖ ≤ C3 * ‖Work.Kernels.qParamFun z‖ := by
          simpa only [pow_one] using h3 z hz1
      _ ≤ Ctot * ‖Work.Kernels.qParamFun z‖ :=
          mul_le_mul_of_nonneg_right hC3le hqnn
  · calc ‖Work.Kernels.E4Fun z ^ 3 - 1‖ ≤ C4 * ‖Work.Kernels.qParamFun z‖ := by
          simpa only [pow_one] using h4 z hz1
      _ ≤ Ctot * ‖Work.Kernels.qParamFun z‖ :=
          mul_le_mul_of_nonneg_right hC4le hqnn
  · calc ‖Work.Kernels.DeltaFun z - Work.Kernels.qParamFun z‖
          ≤ C5 * ‖Work.Kernels.qParamFun z‖ ^ 2 := h5 z hz1
      _ ≤ Ctot * ‖Work.Kernels.qParamFun z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hC5le (by positivity)
  · have hp : ‖(Work.Kernels.DeltaFun z)⁻¹ - (Work.Kernels.qParamFun z)⁻¹ - 24‖
        ≤ C6 * ‖Work.Kernels.qParamFun z‖ := by
      simpa only [pow_one] using h6 z hz1
    have he : (Work.Kernels.DeltaFun z)⁻¹ - ((Work.Kernels.qParamFun z)⁻¹ + 24)
        = (Work.Kernels.DeltaFun z)⁻¹ - (Work.Kernels.qParamFun z)⁻¹ - 24 := by ring
    rw [he]
    calc ‖(Work.Kernels.DeltaFun z)⁻¹ - (Work.Kernels.qParamFun z)⁻¹ - 24‖
          ≤ C6 * ‖Work.Kernels.qParamFun z‖ := hp
      _ ≤ Ctot * ‖Work.Kernels.qParamFun z‖ :=
          mul_le_mul_of_nonneg_right hC6le hqnn
  · calc ‖Work.Kernels.qParamFun z / Work.Kernels.DeltaFun z - 1‖
          ≤ C7 * ‖Work.Kernels.qParamFun z‖ := by
          simpa only [pow_one] using h7 z hz1
      _ ≤ Ctot * ‖Work.Kernels.qParamFun z‖ :=
          mul_le_mul_of_nonneg_right hC7le hqnn
  · calc ‖Work.Kernels.E2S z - (1 - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ)))‖
          ≤ C8 * ‖Work.Kernels.qParamFun z‖ := by
          simpa only [pow_one, Small.S0c] using h8 z hz1
      _ ≤ Ctot * ‖Work.Kernels.qParamFun z‖ :=
          mul_le_mul_of_nonneg_right hC8le hqnn
  · calc ‖Work.Kernels.E6Fun z / Work.Kernels.E4Fun z - 1‖
          ≤ C9 * ‖Work.Kernels.qParamFun z‖ := h9 z hz3
      _ ≤ Ctot * ‖Work.Kernels.qParamFun z‖ :=
          mul_le_mul_of_nonneg_right hC9le hqnn
  · exact E4Fun_inv_norm_le z hz3
  · exact imagAxis_one_sub_inv_le ht hz

end

end Work.Asymptotics
