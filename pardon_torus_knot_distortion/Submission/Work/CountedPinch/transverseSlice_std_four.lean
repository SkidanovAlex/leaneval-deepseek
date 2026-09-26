import Mathlib
import Submission.Work.BoxShrink.PinchOff.TangentConfig
import Submission.Work.CountedPinch.not_finiteCrossing_std
import Submission.Work.BoxShrink.Pinch.Basic

/-!
# Transversality of the standard cutting plane `{z = 1/2}` at the box `PBox 4 0 refl`

This module proves the general-position hypothesis `TransverseSlice` at the configuration used by
`Submission.Work.CountedPinch.not_finiteCrossing_std`: the identity diffeomorphism (the standard
torus of revolution), the box `PBox 4 0 (refl (Fin 3))` and the cutting plane `{z = 1/2}`
(`σ = refl`, `u = 1/2`).

In the parameter plane of the standard torus the plane coordinate is the second torus coordinate
minus `1/2`,

  `planeG idDiffeo 0 (refl (Fin 3)) (1/2) (θ, φ) = sin φ - 1/2`  (`planeG_std`),

so on the slice one has `sin φ = 1/2`, whence `cos φ = ±√3/2 ≠ 0`, and the directional derivative
in the `φ`-direction is `cos φ ≠ 0`.  Hence `∇G ≠ 0` on the whole slice `{G = 0}` — in fact without
any use of the box condition `boxB < 4`.
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.CountedPinch

noncomputable section

/-- **The plane coordinate of the standard configuration**: with `ψ = idDiffeo`, `c = 0`,
`σ = refl (Fin 3)` and `u = 1/2`, the pull-back of the plane coordinate is the second torus
coordinate shifted by `1/2`, i.e. `(θ, φ) ↦ sin φ - 1/2`. -/
theorem planeG_std :
    Work.BoxShrink.Pinch.planeG Work.BoxShrink.PinchOff.idDiffeo (0 : R3)
      (Equiv.refl (Fin 3)) (1 / 2)
      = fun p : ℝ × ℝ => Real.sin p.2 - 1 / 2 := by
  funext p
  rw [Work.BoxShrink.Pinch.planeG_apply, Work.BoxShrink.Bubble.planeCoord_apply,
    Work.BoxShrink.Pinch.par_apply]
  simp only [Work.BoxShrink.PinchOff.idDiffeo, id_eq, Equiv.refl_apply, PiLp.zero_apply,
    zero_add]
  rw [Work.CoreTopology.torusMap_apply_two]

/-- **The derivative of the explicit plane coordinate** `(θ, φ) ↦ sin φ - 1/2`. -/
theorem fderiv_planeG_std (p : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => Real.sin p.2 - 1 / 2) p
      = Real.cos p.2 • (ContinuousLinearMap.snd ℝ ℝ ℝ) := by
  have h : HasFDerivAt (fun p : ℝ × ℝ => Real.sin p.2)
      (Real.cos p.2 • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.snd ℝ ℝ ℝ)).sin
  exact (h.sub_const (1 / 2)).fderiv

/-- **The derivative of the explicit plane coordinate is nonzero on its zero level.**  At a point
`p` with `sin p.2 = 1/2` the `φ`-derivative `cos p.2` is nonzero, because
`cos p.2 ^ 2 = 1 - sin p.2 ^ 2 = 3/4`. -/
theorem fderiv_planeG_std_ne (p : ℝ × ℝ) (hG : Real.sin p.2 - 1 / 2 = 0) :
    fderiv ℝ (fun p : ℝ × ℝ => Real.sin p.2 - 1 / 2) p ≠ 0 := by
  have hsin : Real.sin p.2 = 1 / 2 := by linarith
  have hcos : Real.cos p.2 ≠ 0 := by
    intro hc
    have h := Real.sin_sq_add_cos_sq p.2
    rw [hsin, hc] at h
    norm_num at h
  intro hzero
  have hval : (fderiv ℝ (fun p : ℝ × ℝ => Real.sin p.2 - 1 / 2) p) (0, 1) = Real.cos p.2 := by
    rw [fderiv_planeG_std]; simp
  rw [hzero] at hval
  simp at hval
  exact hcos hval.symm

/-- **The cutting plane `{z = 1/2}` is transverse along the slice at the standard configuration.**
The derivative of the plane coordinate never vanishes on `{G = 0}` (a fortiori on
`{G = 0} ∩ {boxB < 4}`), because its `φ`-derivative is `cos φ ≠ 0` there. -/
theorem transverseSlice_std_four :
    Work.BoxShrink.Pinch.TransverseSlice Work.BoxShrink.PinchOff.idDiffeo 4
      (0 : LeanEval.KnotTheory.PardonDistortion.R3) (Equiv.refl (Fin 3)) (1 / 2) := by
  intro p _ hG
  rw [planeG_std] at hG ⊢
  exact fderiv_planeG_std_ne p hG

end

end Work.CountedPinch
