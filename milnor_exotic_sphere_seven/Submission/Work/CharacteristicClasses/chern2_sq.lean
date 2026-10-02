import Mathlib
import Submission.Work.CharacteristicClasses.Degree
import Submission.Work.CharacteristicClasses.chern2_mul
import Submission.Work.CharacteristicClasses.chern2_functor

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The degree of the squaring map on `S³ = Sp(1)`

`s3Sq : q ↦ q * q` is the pointwise product of the identity with itself, so the Hopf formula
`Work.CharacteristicClasses.chern2_mul` (`deg (q ↦ f q * g q) = deg f + deg g`) gives its degree
immediately: `deg (q ↦ q²) = deg id + deg id = 1 + 1 = 2`.

This is the value `c₂(L²) = 2` for the second tensor power of the tautological quaternionic line
bundle `L` over `S⁴`, and hence — through the spin decomposition `(L², L)` of Milnor's bundle
`ξ = L²R^{-1}` — the input of the computation `p₁(ξ) = 2(2+1) = 6`
(`Submission/Work/CharacteristicClasses/Milnor.lean`).
-/

namespace Work.CharacteristicClasses

noncomputable section

/-- **The degree of the squaring map `q ↦ q²` on `S³ = Sp(1)` is `2`.** -/
theorem chern2_sq : chern2 s3Sq = 2 := by
  have h : s3Sq = s3MulCm (ContinuousMap.id S3) (ContinuousMap.id S3) := rfl
  rw [h, chern2_mul, chern2_functor.1]
  norm_num

end

end Work.CharacteristicClasses
