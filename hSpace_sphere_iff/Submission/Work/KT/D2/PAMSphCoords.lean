import Mathlib
import Submission.Work.KT.D2.PAMDefs

namespace Work.KT.D2

/-!
# Coordinates of the disc-model quotient map `qc 2`

The disc-model quotient map `qc 2 : D² → S²` sends `y` to
`(sfun ‖y‖ • y, -cos (π ‖y‖))`, where `sfun r = π sinc (π r)` is the continuous extension of
`sin (π r)/r`.  This file records the resulting formulae for the coordinates `sphCoord k` and
`sphCoordR` of `qc 2 y`, both for a general point of the disc, for a radial point `r • x`
(`r ∈ [0,1]`, `x ∈ S¹`) and for a boundary point `inBallA x`.
-/

open Work.KT

/-- The first two coordinates of `qc 2 y`. -/
lemma sphCoord_eq_sfun_mul (k : Fin 2) (y : Dc) :
    sphCoord k y = sfun ‖(y : E2)‖ * (y : E2) k := by
  show (((qc 2 y : ModelSphere 2).fst) k) = sfun ‖(y : E2)‖ * (y : E2) k
  rw [qc_apply, qMapDisk]
  simp only [WithLp.fst, PiLp.smul_apply, smul_eq_mul]

/-- The last coordinate of `qc 2 y`. -/
lemma sphCoordR_eq_neg_cos (y : Dc) :
    sphCoordR y = -Real.cos (Real.pi * ‖(y : E2)‖) := by
  show ((qc 2 y : ModelSphere 2).snd) = -Real.cos (Real.pi * ‖(y : E2)‖)
  rw [qc_apply, qMapDisk]
  simp only [WithLp.snd]

/-- The norm of a radial point of the disc. -/
lemma norm_coe_radCM (r : unitInterval) (x : Sc) :
    ‖((radCM r x : Dc) : E2)‖ = (r : ℝ) := by
  rw [radCM_coe, norm_smul, Real.norm_eq_abs, abs_of_nonneg r.2.1, norm_coe_sphere, mul_one]

theorem PAMSphCoords :
    (∀ y : Work.KT.D2.Dc,
      Work.KT.D2.sphCoord 0 y = Work.KT.sfun ‖(y : Work.KT.D2.E2)‖ * (y : Work.KT.D2.E2) 0 ∧
      Work.KT.D2.sphCoord 1 y = Work.KT.sfun ‖(y : Work.KT.D2.E2)‖ * (y : Work.KT.D2.E2) 1 ∧
      Work.KT.D2.sphCoordR y = -Real.cos (Real.pi * ‖(y : Work.KT.D2.E2)‖)) ∧
    (∀ (r : unitInterval) (x : Work.KT.D2.Sc),
      Work.KT.D2.sphCoord 0 (Work.KT.D2.radCM r x) = Real.sin (Real.pi * (r : ℝ)) * (x : Work.KT.D2.E2) 0 ∧
      Work.KT.D2.sphCoord 1 (Work.KT.D2.radCM r x) = Real.sin (Real.pi * (r : ℝ)) * (x : Work.KT.D2.E2) 1 ∧
      Work.KT.D2.sphCoordR (Work.KT.D2.radCM r x) = -Real.cos (Real.pi * (r : ℝ))) ∧
    (∀ x : Work.KT.D2.Sc, Work.KT.D2.sphCoordR (Work.KT.D2.inBallA x) = 1 ∧
      Work.KT.D2.sphCoord 0 (Work.KT.D2.inBallA x) = 0 ∧
      Work.KT.D2.sphCoord 1 (Work.KT.D2.inBallA x) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact ⟨sphCoord_eq_sfun_mul 0 y, sphCoord_eq_sfun_mul 1 y, sphCoordR_eq_neg_cos y⟩
  · intro r x
    refine ⟨?_, ?_, ?_⟩
    · rw [sphCoord_eq_sfun_mul, norm_coe_radCM, radCM_coe, PiLp.smul_apply, smul_eq_mul,
        ← mul_assoc, sfun_mul]
    · rw [sphCoord_eq_sfun_mul, norm_coe_radCM, radCM_coe, PiLp.smul_apply, smul_eq_mul,
        ← mul_assoc, sfun_mul]
    · rw [sphCoordR_eq_neg_cos, norm_coe_radCM]
  · intro x
    refine ⟨?_, ?_, ?_⟩
    · rw [sphCoordR_eq_neg_cos, inBallA_coe, norm_coe_sphere, mul_one, Real.cos_pi, neg_neg]
    · rw [sphCoord_eq_sfun_mul, inBallA_coe, norm_coe_sphere, sfun_one, zero_mul]
    · rw [sphCoord_eq_sfun_mul, inBallA_coe, norm_coe_sphere, sfun_one, zero_mul]

end Work.KT.D2
