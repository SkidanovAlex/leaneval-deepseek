import Mathlib
import Submission.Work.CharacteristicClasses.Degree
import Submission.Work.CharacteristicClasses.chern2_functor
import Submission.Work.CharacteristicClasses.chern2_mul

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.CharacteristicClasses

noncomputable section

/-- `chern2` of the constant self-map `q ↦ 1` of `S³` vanishes.  (Apply the Hopf additivity
`chern2_mul` to `1 · 1 = 1`: `chern2 (const 1) = chern2 (const 1) + chern2 (const 1)`.) -/
lemma chern2_s3OneCm : chern2 s3OneCm = 0 := by
  have hh : s3MulCm s3OneCm s3OneCm = s3OneCm := by
    apply ContinuousMap.ext
    intro q
    simp
  have hh2 := chern2_mul s3OneCm s3OneCm
  rw [hh] at hh2
  linarith

/-- **The degree of the inverse map `q ↦ q⁻¹` on `S³` is `-1`.**  (Conjugation `q ↦ star q` is a
reflection of `S³`, of degree `-1`.)  Equivalently, the second Chern class of the conjugate
quaternionic line bundle is the negative of `c₂`; this is what makes the Pontryagin class of
`TS⁴` vanish.

Recommended route: `s3MulCm id s3InvCm` is the constant map `q ↦ 1` (use
`Work.CharacteristicClasses.s3Mul_inv`), so `Work.CharacteristicClasses.chern2_mul` (the
pointwise-product additivity, delegated in parallel) and `Work.CharacteristicClasses.chern2_const`
give `chern2 id + chern2 s3InvCm = 0`, and `chern2 id = 1` by
`Work.CharacteristicClasses.chern2_functor`. -/
theorem chern2_inv : Work.CharacteristicClasses.chern2 Work.CharacteristicClasses.s3InvCm = -1 := by
  have h1 : s3MulCm (ContinuousMap.id S3) s3InvCm = s3OneCm := by
    apply ContinuousMap.ext
    intro q
    exact s3Mul_inv q
  have hm := chern2_mul (ContinuousMap.id S3) s3InvCm
  rw [h1, chern2_s3OneCm, chern2_functor.1] at hm
  linarith

end

end Work.CharacteristicClasses
