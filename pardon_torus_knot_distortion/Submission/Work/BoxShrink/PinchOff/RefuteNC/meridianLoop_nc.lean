import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteNC.Config

/-!
# The meridian of the `nc` configuration lies in its box region with winding `(0,1)`

The refuting configuration of `RefuteNC/Config.lean` is the standard torus (`ψ = idDiffeo`), the box
`PBox ncRad ncCtr ncCyc3` and the cutting plane `{x = 1/2}`.  This module exhibits an *essential*
loop of the box region `Ω = F ∩ PBox`, namely the meridian

  `γ = meridianCurve (surface idDiffeo) ncTheta`,   `ncTheta = arccos (1/3)`,

i.e. the curve `t ↦ torusMap ncTheta t = ((2 + cos t)·(1/3), (2 + cos t)·(2√2/3), sin t)`.

At `θ = arccos (1/3)` the first coordinate runs over `[1/3, 1] ⊂ (1 - 2^{2/3}, 1 + 2^{2/3})`, the
second over `[2√2/3, 2√2] ⊂ (9/10, 29/10)` and the third over `[-1, 1]`, so `γ` does lie in the box;
its winding vector is `(0, 1)`, so `(0, 1)` is realised in `W(Ω)`.

This is the first of the three facts that make the configuration a counterexample to the transport
form of the residual; the comment of `RefuteNC/Config.lean` calls it `ncMer_mem_Omega`.
-/

namespace Work.BoxShrink.PinchOff.RefuteNC

open Work.BoxShrink.PinchOff

noncomputable section

/-! ## Elementary bounds at `ncTheta = arccos (1/3)` -/

private theorem ncTheta_cos : Real.cos ncTheta = 1 / 3 :=
  Real.cos_arccos (by norm_num) (by norm_num)

private theorem ncTheta_sin : Real.sin ncTheta = Real.sqrt (8 / 9) := by
  rw [ncTheta, Real.sin_arccos]; norm_num

/-- `9/10 < sin (arccos (1/3))`: the meridian's second coordinate stays above `9/10`. -/
private theorem ncTheta_sin_gt : (9 : ℝ) / 10 < Real.sin ncTheta := by
  rw [ncTheta_sin, Real.lt_sqrt (by norm_num)]; norm_num

/-- `sin (arccos (1/3)) < 29/30`: the meridian's second coordinate stays below `29/10`. -/
private theorem ncTheta_sin_lt : Real.sin ncTheta < 29 / 30 := by
  rw [ncTheta_sin, Real.sqrt_lt (by norm_num) (by norm_num)]; norm_num

/-- `1 < 2^{1/3}`. -/
private theorem one_lt_rpow_third : (1 : ℝ) < (2 : ℝ) ^ (1 / 3 : ℝ) := by
  have h := (Real.rpow_lt_rpow_left_iff (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
    (y := (0 : ℝ)) (z := (1 / 3 : ℝ))).mpr (by norm_num)
  simpa using h

/-- `2/3 < 2^{2/3}`. -/
private theorem two_thirds_lt_rpow_two_thirds : (2 : ℝ) / 3 < (2 : ℝ) ^ (2 / 3 : ℝ) := by
  have h : (1 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) := by
    have h' := (Real.rpow_lt_rpow_left_iff (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
      (y := (0 : ℝ)) (z := (2 / 3 : ℝ))).mpr (by norm_num)
    simpa using h'
  linarith

/-- **The meridian `{θ = arccos (1/3)}` of the standard torus lies in the box.**  Its first
coordinate `(2 + cos t)/3` runs over `[1/3, 1]`, its second `(2 + cos t)·sin ncTheta` over
`[2√2/3, 2√2] ⊂ (9/10, 29/10)` and its third `sin t` over `[-1, 1]`. -/
private theorem torusMap_ncTheta_mem_PBox (t : ℝ) :
    Work.Core.torusMap ncTheta t ∈ Submission.PBox ncRad ncCtr ncCyc3 := by
  rw [mem_PBox_nc]
  refine ⟨?_, ?_, ?_⟩
  · -- `|(2 + cos t)·sin ncTheta - 19/10| < 1`
    show |(2 + Real.cos t) * Real.sin ncTheta - 19 / 10| < 1
    rw [abs_lt]
    have hu1 : (1 : ℝ) ≤ 2 + Real.cos t := by linarith [Real.neg_one_le_cos t]
    have hu3 : 2 + Real.cos t ≤ 3 := by linarith [Real.cos_le_one t]
    have hs_pos : 0 < Real.sin ncTheta := by linarith [ncTheta_sin_gt]
    have hlow : (9 : ℝ) / 10 < (2 + Real.cos t) * Real.sin ncTheta :=
      lt_of_lt_of_le ncTheta_sin_gt (by
        have := mul_le_mul_of_nonneg_right hu1 (le_of_lt hs_pos)
        simpa using this)
    have hhigh : (2 + Real.cos t) * Real.sin ncTheta < 29 / 10 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hu3 (le_of_lt hs_pos)) (by
        have := mul_lt_mul_of_pos_left ncTheta_sin_lt (by norm_num : (0 : ℝ) < 3)
        norm_num at this ⊢
        linarith)
    exact ⟨by linarith, by linarith⟩
  · -- `|sin t| < 2^{1/3}`
    show |Real.sin t| < (2 : ℝ) ^ (1 / 3 : ℝ)
    exact lt_of_le_of_lt (Real.abs_sin_le_one t) one_lt_rpow_third
  · -- `|(2 + cos t)·cos ncTheta - 1| < 2^{2/3}`
    show |(2 + Real.cos t) * Real.cos ncTheta - 1| < (2 : ℝ) ^ (2 / 3 : ℝ)
    rw [ncTheta_cos]
    have hb : |(2 + Real.cos t) * (1 / 3) - 1| ≤ 2 / 3 := by
      rw [abs_le]
      exact ⟨by nlinarith [Real.neg_one_le_cos t], by nlinarith [Real.cos_le_one t]⟩
    exact lt_of_le_of_lt hb two_thirds_lt_rpow_two_thirds

/-- **The meridian `{θ = arccos (1/3)}` lies in the box region `Ω`.** -/
theorem ncMer_mem_Omega :
    ∀ t : ℝ, (Work.CoreTopology.meridianCurve (surface idDiffeo) ncTheta) t ∈
      Omega idDiffeo ncRad ncCtr ncCyc3 := by
  intro t
  rw [Omega, Work.BoxShrink.Core.mem_boxRegion]
  exact ⟨(Work.CoreTopology.meridianCurve (surface idDiffeo) ncTheta).mem t,
    torusMap_ncTheta_mem_PBox t⟩

/-- **The winding vector of `γ = meridianCurve (surface idDiffeo) ncTheta` is `(0, 1)`.** -/
theorem windingOf_ncMer :
    Work.SurgeryInvariance.windingOf (surface idDiffeo)
      (Work.CoreTopology.meridianCurve (surface idDiffeo) ncTheta) = (0, 1) := by
  rw [Work.SurgeryInvariance.windingOf_eq (surface idDiffeo) _
      (Work.CoreTopology.meridianLift (surface idDiffeo) ncTheta),
    Work.CoreTopology.meridianLift_winding]

/-- **The meridian of the `nc` configuration is an essential loop of the box region with winding
vector `(0, 1)`.** -/
theorem meridianLoop_nc :
    ∃ γ : Work.CoreTopology.ClosedCurve (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo),
      (∀ t : ℝ, γ t ∈ Work.BoxShrink.PinchOff.Omega Work.BoxShrink.PinchOff.idDiffeo
        Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
        Work.BoxShrink.PinchOff.ncCyc3) ∧
      Work.SurgeryInvariance.windingOf (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo) γ =
        (0, 1) :=
  ⟨Work.CoreTopology.meridianCurve (surface idDiffeo) ncTheta, ncMer_mem_Omega, windingOf_ncMer⟩

end

end Work.BoxShrink.PinchOff.RefuteNC
