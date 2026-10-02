import Mathlib
import Submission.Work.Agree.crux
import Submission.Work.Agree.detMulLeftPos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Positivity of the determinant of the off-diagonal clutching twist `qTwist 1 0`

`Work.Agree.det_qTwist_one_zero_pos`: for a unit quaternion `q ∈ ℍ` (`‖q‖ = 1`) the real-linear
map of `ℝ⁴ ≅ ℍ`

    `v ↦ q · v`      (`qTwist 1 0 q`, i.e. `q^1 · v · q^0`)

has positive determinant.

The map is `ofQ ∘ (mulLeft q) ∘ toQ`, where `toQ : ℝ⁴ →ₗ ℍ` and `ofQ : ℍ →ₗ ℝ⁴` are inverse
linear isometries.  Conjugating the endomorphism `mulLeft q` of `ℍ` by the linear equivalence
`Quaternion.linearIsometryEquivTuple : ℍ ≃ₗ ℝ⁴` (Mathlib's `LinearMap.det_conj`) leaves the
determinant unchanged, so `det (qTwist 1 0 q) = det (mulLeft q)`, which is positive by
`Work.Agree.detMulLeftPos`.
-/

namespace Work.Agree

/-- The `q ^ 0`-part of `qTwist` is the identity: right multiplication by `1`. -/
private lemma flip_mul_one_toLinearMap :
    ((ContinuousLinearMap.mul ℝ (Quaternion ℝ)).flip (1 : Quaternion ℝ)).toLinearMap
      = LinearMap.id := by
  have hclm : (ContinuousLinearMap.mul ℝ (Quaternion ℝ)).flip (1 : Quaternion ℝ) = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', mul_one]
    simp
  rw [hclm, ContinuousLinearMap.toLinearMap_one]
  rfl

theorem det_qTwist_one_zero_pos (q : Quaternion ℝ) (hq : ‖q‖ = 1) :
    0 < LinearMap.det ((Work.Agree.qTwist 1 0 q).toLinearMap) := by
  -- Right multiplication by `q ^ 0 = 1` is the identity ...
  have hR : ((ContinuousLinearMap.mul ℝ (Quaternion ℝ)).flip (q ^ (0:ℤ))).toLinearMap
      = LinearMap.id := by
    rw [zpow_zero]
    exact flip_mul_one_toLinearMap
  -- ... and left multiplication by `q ^ 1 = q` is `mulLeft q`.
  have hL : ((ContinuousLinearMap.mul ℝ (Quaternion ℝ)) (q ^ (1:ℤ))).toLinearMap
      = LinearMap.mulLeft ℝ q := by
    rw [zpow_one]
    rfl
  -- Unfold the definition of `qTwist` into a composite of linear maps.
  have hT : (Work.Agree.qTwist 1 0 q).toLinearMap
      = ofQ.toLinearMap ∘ₗ LinearMap.mulLeft ℝ q ∘ₗ toQ.toLinearMap := by
    unfold qTwist
    rw [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
        ContinuousLinearMap.toLinearMap_comp, hR, hL, LinearMap.id_comp, LinearMap.comp_assoc]
  -- Conjugate `mulLeft q` by the linear isometry equivalence `ℍ ≃ₗ ℝ⁴`.
  have key : LinearMap.det (ofQ.toLinearMap ∘ₗ LinearMap.mulLeft ℝ q ∘ₗ toQ.toLinearMap)
      = LinearMap.det (LinearMap.mulLeft ℝ q) :=
    LinearMap.det_conj (f := LinearMap.mulLeft ℝ q)
      (e := (Quaternion.linearIsometryEquivTuple :
        Quaternion ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)).toLinearEquiv)
  rw [hT, key]
  exact detMulLeftPos q hq

end Work.Agree
