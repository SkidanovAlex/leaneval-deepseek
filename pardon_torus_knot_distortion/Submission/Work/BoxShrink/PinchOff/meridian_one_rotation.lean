import Mathlib
import Submission.Work.BoxShrink.PinchOff.Rotation

/-!
# The meridian `{θ = 1}` of the rotated torus lies in the upper half-region

For `ψ = rotDiffeo (1/4)` (the rotation of `ℝ³` about the `x`-axis by `1/4`), the meridian curve
`meridianCurve (ψ F_standard) 1`, i.e. the curve `t ↦ ψ (torusMap 1 t)`, lies in the upper
half-region `upperRegion (ψ F_standard) (9/5) 0 sigmaY 0 = F ∩ PBox (9/5) 0 sigmaY ∩ {y > 0}`.

Writing `α = 1/4` and `Y t = rotFun α (torusMap 1 t)`, the coordinates are

* `Y t 0 = (2 + cos t) cos 1`,
* `Y t 1 = cos α (2 + cos t) sin 1 − sin α sin t`,
* `Y t 2 = sin α (2 + cos t) sin 1 + cos α sin t`,

and `σ = sigmaY` is the cyclic permutation with `σ 0 = 2`, `σ 1 = 0`, `σ 2 = 1`, so the box
`PBox (9/5) 0 sigmaY` requires `|Y t 2| < 9/5`, `|Y t 0| < 2^{1/3} · 9/5`,
`|Y t 1| < 2^{2/3} · 9/5`, while the half-space requires `Y t 1 > 0`.  All four are elementary
consequences of the Taylor bounds `Real.sin_bound`, `Real.cos_bound` and the elementary bounds
`Real.one_sub_sq_div_two_le_cos`, `Real.sin_lt`; the numerical margins are

* `|Y t 2| ≤ 7/4 < 9/5`,
* `|Y t 0| ≤ 3 · 53/96 < 9/5 ≤ 2^{1/3} · 9/5`,
* `|Y t 1| ≤ (23813/24576) · 3 · (253/300) + 1/4 < (151/100) · 9/5 < 2^{2/3} · 9/5`,
* `Y t 1 ≥ (31/32) · (247/300) − 1/4 > 0`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-! ## Elementary numerical bounds -/

/-- `cos (1/4) ≥ 31/32`, from `1 − x²/2 ≤ cos x` at `x = 1/4`. -/
lemma cos_quarter_ge : (31 : ℝ) / 32 ≤ Real.cos (1 / 4) := by
  have h := Real.one_sub_sq_div_two_le_cos (x := (1 / 4 : ℝ))
  norm_num at h ⊢
  linarith

/-- `cos (1/4) ≤ 23813/24576`, from the quartic Taylor bound `Real.cos_bound` at `x = 1/4`. -/
lemma cos_quarter_le : Real.cos (1 / 4) ≤ 23813 / 24576 := by
  have h := Real.cos_bound (x := (1 / 4 : ℝ)) (by norm_num)
  rw [abs_le] at h
  norm_num at h
  linarith [h.2]

lemma cos_quarter_nonneg : 0 ≤ Real.cos (1 / 4) :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩

lemma sin_quarter_nonneg : 0 ≤ Real.sin (1 / 4) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num) (by linarith [Real.pi_gt_three])

lemma sin_quarter_lt : Real.sin (1 / 4) < 1 / 4 := Real.sin_lt (by norm_num)

/-- `sin 1 ≥ 247/300`, from the quintic Taylor bound `Real.sin_bound` at `x = 1`. -/
lemma sin_one_ge : (247 : ℝ) / 300 ≤ Real.sin 1 := by
  have h := Real.sin_bound (x := (1 : ℝ)) (by norm_num)
  rw [abs_le] at h
  norm_num at h
  linarith [h.1]

/-- `sin 1 ≤ 253/300`, from the quintic Taylor bound `Real.sin_bound` at `x = 1`. -/
lemma sin_one_le : Real.sin 1 ≤ 253 / 300 := by
  have h := Real.sin_bound (x := (1 : ℝ)) (by norm_num)
  rw [abs_le] at h
  norm_num at h
  linarith [h.2]

lemma sin_one_nonneg : 0 ≤ Real.sin 1 :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num) (by linarith [Real.pi_gt_three])

/-- `cos 1 ≤ 53/96`, from the quartic Taylor bound `Real.cos_bound` at `x = 1`. -/
lemma cos_one_le : Real.cos 1 ≤ 53 / 96 := by
  have h := Real.cos_bound (x := (1 : ℝ)) (by norm_num)
  rw [abs_le] at h
  norm_num at h
  linarith [h.2]

lemma cos_one_nonneg : 0 ≤ Real.cos 1 :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩

/-- `2^{1/3} > 5/4`. -/
lemma rpow_third_gt : (5 : ℝ) / 4 < (2 : ℝ) ^ (1 / 3 : ℝ) := by
  have hcube : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 2 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (1 / 3 : ℝ)) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h2 : ((5 : ℝ) / 4) ^ 3 < ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := by
    rw [hcube]; norm_num
  exact lt_of_pow_lt_pow_left₀ 3 (by positivity) h2

/-- `2^{2/3} > 151/100`. -/
lemma rpow_two_thirds_gt : (151 : ℝ) / 100 < (2 : ℝ) ^ (2 / 3 : ℝ) := by
  have hcube : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = 4 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (2 / 3 : ℝ)) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h2 : ((151 : ℝ) / 100) ^ 3 < ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 := by
    rw [hcube]; norm_num
  exact lt_of_pow_lt_pow_left₀ 3 (by positivity) h2

/-! ## The coordinates of the rotated meridian -/

lemma rotMeridian_coord_zero (t : ℝ) :
    (rotFun (1 / 4) (Work.Core.torusMap 1 t)) 0 = (2 + Real.cos t) * Real.cos 1 := by
  rw [rotFun_coord_zero, Work.BoxShrink.Pinch.torusMap_apply_zero]

lemma rotMeridian_coord_one (t : ℝ) :
    (rotFun (1 / 4) (Work.Core.torusMap 1 t)) 1
      = Real.cos (1 / 4) * (2 + Real.cos t) * Real.sin 1
        - Real.sin (1 / 4) * Real.sin t := by
  rw [rotFun_coord_one, Work.BoxShrink.Pinch.torusMap_apply_one,
    Work.BoxShrink.Pinch.torusMap_apply_two]
  ring

lemma rotMeridian_coord_two (t : ℝ) :
    (rotFun (1 / 4) (Work.Core.torusMap 1 t)) 2
      = Real.sin (1 / 4) * (2 + Real.cos t) * Real.sin 1
        + Real.cos (1 / 4) * Real.sin t := by
  rw [rotFun_coord_two, Work.BoxShrink.Pinch.torusMap_apply_one,
    Work.BoxShrink.Pinch.torusMap_apply_two]
  ring

/-! ## The three coordinate bounds -/

/-- The `x`-coordinate (`σ 0 = 2`) is bounded by `3 cos 1 < (9/5) 2^{1/3}`. -/
lemma rotMeridian_abs_coord_zero_lt (t : ℝ) :
    |(rotFun (1 / 4) (Work.Core.torusMap 1 t)) 0| < (2 : ℝ) ^ (1 / 3 : ℝ) * (9 / 5) := by
  rw [rotMeridian_coord_zero t]
  have hw : 2 + Real.cos t ≤ 3 := by linarith [Real.cos_le_one t]
  have hwn : 0 ≤ 2 + Real.cos t := by linarith [Real.neg_one_le_cos t]
  have hprod : (2 + Real.cos t) * Real.cos 1 ≤ 3 * (53 / 96) :=
    mul_le_mul hw cos_one_le cos_one_nonneg (by norm_num)
  rw [abs_of_nonneg (mul_nonneg hwn cos_one_nonneg)]
  have h9 : (9 : ℝ) / 5 ≤ (2 : ℝ) ^ (1 / 3 : ℝ) * (9 / 5) := by
    have := mul_le_mul_of_nonneg_right Submission.one_le_rpow_third
      (show (0 : ℝ) ≤ 9 / 5 by norm_num)
    simpa using this
  nlinarith [hprod, h9]

/-- The `y`-coordinate (`σ 2 = 1`) is bounded by `cos(1/4)·3·sin 1 + sin(1/4)
< (151/100)·(9/5) < 2^{2/3}·(9/5)`. -/
lemma rotMeridian_abs_coord_one_lt (t : ℝ) :
    |(rotFun (1 / 4) (Work.Core.torusMap 1 t)) 1| < (2 : ℝ) ^ (2 / 3 : ℝ) * (9 / 5) := by
  rw [rotMeridian_coord_one t]
  have hw : 2 + Real.cos t ≤ 3 := by linarith [Real.cos_le_one t]
  have hwn : 0 ≤ 2 + Real.cos t := by linarith [Real.neg_one_le_cos t]
  have h1 : Real.cos (1 / 4) * (2 + Real.cos t) ≤ (23813 / 24576) * 3 :=
    mul_le_mul cos_quarter_le hw hwn (by norm_num)
  have h1n : 0 ≤ Real.cos (1 / 4) * (2 + Real.cos t) :=
    mul_nonneg cos_quarter_nonneg hwn
  have h2 : Real.cos (1 / 4) * (2 + Real.cos t) * Real.sin 1
      ≤ (23813 / 24576) * 3 * (253 / 300) :=
    mul_le_mul h1 sin_one_le sin_one_nonneg (by norm_num)
  have h2n : 0 ≤ Real.cos (1 / 4) * (2 + Real.cos t) * Real.sin 1 :=
    mul_nonneg h1n sin_one_nonneg
  have h3up : Real.sin (1 / 4) * Real.sin t ≤ 1 / 4 := by
    have h := mul_le_mul_of_nonneg_left (Real.sin_le_one t) sin_quarter_nonneg
    linarith [h, sin_quarter_lt.le]
  have h3lo : -(1 / 4) ≤ Real.sin (1 / 4) * Real.sin t := by
    have h := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin t) sin_quarter_nonneg
    linarith [h, sin_quarter_lt.le]
  have hr : (151 : ℝ) / 100 * (9 / 5) < (2 : ℝ) ^ (2 / 3 : ℝ) * (9 / 5) :=
    mul_lt_mul_of_pos_right rpow_two_thirds_gt (by norm_num)
  rw [abs_lt]
  refine ⟨?_, ?_⟩
  · have hlow : -(1 / 4) ≤ Real.cos (1 / 4) * (2 + Real.cos t) * Real.sin 1
        - Real.sin (1 / 4) * Real.sin t := by linarith [h2n, h3up]
    nlinarith [hlow, hr]
  · have hup : Real.cos (1 / 4) * (2 + Real.cos t) * Real.sin 1
        - Real.sin (1 / 4) * Real.sin t
        ≤ (23813 / 24576) * 3 * (253 / 300) + 1 / 4 := by linarith [h2, h3lo]
    nlinarith [hup, hr]

/-- The `z`-coordinate (`σ 1 = 0`) is bounded by `7/4 < 9/5`. -/
lemma rotMeridian_abs_coord_two_lt (t : ℝ) :
    |(rotFun (1 / 4) (Work.Core.torusMap 1 t)) 2| < 9 / 5 := by
  rw [rotMeridian_coord_two t]
  have hw : 2 + Real.cos t ≤ 3 := by linarith [Real.cos_le_one t]
  have hwn : 0 ≤ 2 + Real.cos t := by linarith [Real.neg_one_le_cos t]
  have h1 : Real.sin (1 / 4) * (2 + Real.cos t) ≤ (1 / 4) * 3 :=
    mul_le_mul sin_quarter_lt.le hw hwn (by norm_num)
  have h1n : 0 ≤ Real.sin (1 / 4) * (2 + Real.cos t) :=
    mul_nonneg sin_quarter_nonneg hwn
  have h2 : Real.sin (1 / 4) * (2 + Real.cos t) * Real.sin 1 ≤ (1 / 4) * 3 * 1 :=
    mul_le_mul h1 (Real.sin_le_one 1) sin_one_nonneg (by norm_num)
  have h2n : 0 ≤ Real.sin (1 / 4) * (2 + Real.cos t) * Real.sin 1 :=
    mul_nonneg h1n sin_one_nonneg
  have h3 : Real.cos (1 / 4) * Real.sin t ≤ 1 * 1 := by
    have ha := mul_le_mul_of_nonneg_left (Real.sin_le_one t) cos_quarter_nonneg
    nlinarith [ha, cos_quarter_le]
  have h4 : -(1 : ℝ) ≤ Real.cos (1 / 4) * Real.sin t := by
    have ha := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin t) cos_quarter_nonneg
    nlinarith [ha, cos_quarter_le]
  rw [abs_lt]
  refine ⟨?_, ?_⟩
  · nlinarith [h4, h2n]
  · have hup : Real.sin (1 / 4) * (2 + Real.cos t) * Real.sin 1
        + Real.cos (1 / 4) * Real.sin t ≤ (1 / 4) * 3 * 1 + 1 * 1 := by linarith [h2, h3]
    nlinarith [hup]

/-! ## Positivity of the `y`-coordinate -/

/-- `Y t 1 ≥ (31/32)·(247/300) − 1/4 > 0`. -/
lemma rotMeridian_coord_one_pos (t : ℝ) :
    0 < (rotFun (1 / 4) (Work.Core.torusMap 1 t)) 1 := by
  rw [rotMeridian_coord_one t]
  have hw : (1 : ℝ) ≤ 2 + Real.cos t := by linarith [Real.neg_one_le_cos t]
  have hwn : 0 ≤ 2 + Real.cos t := by linarith [Real.neg_one_le_cos t]
  have ha : (31 / 32) * 1 ≤ Real.cos (1 / 4) * (2 + Real.cos t) :=
    mul_le_mul cos_quarter_ge hw (by norm_num) cos_quarter_nonneg
  have ha2 : ((31 / 32) * 1) * (247 / 300)
      ≤ Real.cos (1 / 4) * (2 + Real.cos t) * Real.sin 1 :=
    mul_le_mul ha sin_one_ge (by norm_num) (mul_nonneg cos_quarter_nonneg hwn)
  have hs : Real.sin (1 / 4) * Real.sin t ≤ 1 / 4 := by
    have h := mul_le_mul_of_nonneg_left (Real.sin_le_one t) sin_quarter_nonneg
    linarith [h, sin_quarter_lt.le]
  nlinarith [ha2, hs]

/-! ## The membership -/

/-- The rotated meridian point at parameter `t` lies in the upper half-region. -/
lemma rotMeridian_mem_upperRegion (t : ℝ) :
    rotFun (1 / 4) (Work.Core.torusMap 1 t) ∈
      Work.BoxShrink.Core.upperRegion (surface (rotDiffeo (1 / 4))) (9 / 5) 0 sigmaY 0 := by
  rw [Work.BoxShrink.Core.mem_upperRegion]
  refine ⟨⟨(1, t), rfl⟩, ?_, ?_⟩
  · rw [Submission.mem_PBox]
    intro i
    fin_cases i
    · simpa [sigmaY_zero, Submission.boxSide_zero] using rotMeridian_abs_coord_two_lt t
    · simpa [sigmaY_one, Submission.boxSide_one] using rotMeridian_abs_coord_zero_lt t
    · simpa [sigmaY_two, Submission.boxSide_two] using rotMeridian_abs_coord_one_lt t
  · rw [sigmaY_two, PiLp.zero_apply, zero_add]
    exact rotMeridian_coord_one_pos t

/-! ## The target -/

theorem meridian_one_rotation :
    ∀ t : ℝ, (Work.CoreTopology.meridianCurve (surface (rotDiffeo (1 / 4))) 1) t ∈
      Work.BoxShrink.Core.upperRegion (surface (rotDiffeo (1 / 4))) (9 / 5) 0 sigmaY 0 := by
  intro t
  have hval : (Work.CoreTopology.meridianCurve (surface (rotDiffeo (1 / 4))) 1) t
      = rotFun (1 / 4) (Work.Core.torusMap 1 t) := by
    rw [Work.CoreTopology.meridianCurve_apply, Work.Smooth.Morse.torus_psi]
    rfl
  rw [hval]
  exact rotMeridian_mem_upperRegion t

end

end Work.BoxShrink.PinchOff
