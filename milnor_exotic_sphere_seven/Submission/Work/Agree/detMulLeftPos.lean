import Mathlib
import Submission.Work.Agree.crux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Positivity of the determinant of left quaternionic multiplication

`Work.Agree.detMulLeftPos`: for a unit quaternion `q ∈ ℍ` (`‖q‖ = 1`), left multiplication
`x ↦ q * x` is an isometry of `ℍ = ℝ⁴` onto itself (it preserves the norm because
`‖q * x‖ = ‖q‖ * ‖x‖ = ‖x‖`), hence its determinant on `ℝ⁴` is `±1`; the sign is `+1` because
`q ↦ det (x ↦ q * x)` is continuous on the preconnected unit sphere `S³ ⊂ ℍ`, never vanishes
(left multiplication by a nonzero quaternion is invertible, with inverse left multiplication by
`q⁻¹`), and equals `1` at `q = 1`.  A continuous function on a preconnected set whose image misses
`0` cannot change sign, so the determinant is positive everywhere on `S³`.
-/

namespace Work.Agree

/-- Left multiplication by a quaternion, as a *continuous* linear map, has the same underlying
linear map as `LinearMap.mulLeft`. -/
private lemma toLinearMap_mul_eq_mulLeft (x : Quaternion ℝ) :
    (ContinuousLinearMap.mul ℝ (Quaternion ℝ) x).toLinearMap = LinearMap.mulLeft ℝ x := rfl

/-- Left multiplication by `1` is the identity. -/
private lemma mulLeft_one : LinearMap.mulLeft ℝ (1 : Quaternion ℝ) = LinearMap.id := by
  apply LinearMap.ext
  intro y
  show (1 : Quaternion ℝ) * y = y
  simp

/-- Left multiplication by a nonzero quaternion has nonzero determinant: `mulLeft q` is invertible
with inverse `mulLeft q⁻¹`, so `det (mulLeft q) * det (mulLeft q⁻¹) = det id = 1`. -/
private lemma det_mulLeft_ne_zero {x : Quaternion ℝ} (hx0 : x ≠ 0) :
    LinearMap.det (LinearMap.mulLeft ℝ x) ≠ 0 := by
  have hmul : LinearMap.mulLeft ℝ (x * x⁻¹)
      = LinearMap.mulLeft ℝ x ∘ₗ LinearMap.mulLeft ℝ x⁻¹ :=
    LinearMap.mulLeft_mul ℝ (Quaternion ℝ) x x⁻¹
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ x) * LinearMap.det (LinearMap.mulLeft ℝ x⁻¹)
      = 1 := by
    have h := LinearMap.det_comp (LinearMap.mulLeft ℝ x) (LinearMap.mulLeft ℝ x⁻¹)
    rw [← hmul, mul_inv_cancel₀ hx0, mulLeft_one, LinearMap.det_id] at h
    exact h.symm
  intro h0
  rw [h0, zero_mul] at hdet
  exact zero_ne_one hdet

theorem detMulLeftPos (q : Quaternion ℝ) (hq : ‖q‖ = 1) :
    0 < LinearMap.det ((ContinuousLinearMap.mul ℝ (Quaternion ℝ) q).toLinearMap) := by
  -- the unit sphere of `ℍ = ℝ⁴` is preconnected
  have hrank : 1 < Module.rank ℝ (Quaternion ℝ) := by
    rw [Quaternion.rank_eq_four]
    norm_num
  have hsphere : Metric.sphere (0 : Quaternion ℝ) 1 = {x : Quaternion ℝ | ‖x‖ = 1} := by
    ext x
    simp
  have hpre : IsPreconnected {x : Quaternion ℝ | ‖x‖ = 1} := by
    rw [← hsphere]
    exact isPreconnected_sphere hrank 0 1
  -- the determinant is continuous in `q`
  have hcont : Continuous fun x : Quaternion ℝ =>
      LinearMap.det ((ContinuousLinearMap.mul ℝ (Quaternion ℝ) x).toLinearMap) :=
    ContinuousLinearMap.continuous_det.comp (ContinuousLinearMap.mul ℝ (Quaternion ℝ)).continuous
  -- and nonvanishing at unit quaternions
  have hne : ∀ x : Quaternion ℝ, ‖x‖ = 1 →
      LinearMap.det ((ContinuousLinearMap.mul ℝ (Quaternion ℝ) x).toLinearMap) ≠ 0 := by
    intro x hx
    rw [toLinearMap_mul_eq_mulLeft x]
    refine det_mulLeft_ne_zero ?_
    rintro rfl
    simp at hx
  set F : Quaternion ℝ → ℝ := fun x =>
      LinearMap.det ((ContinuousLinearMap.mul ℝ (Quaternion ℝ) x).toLinearMap) with hFdef
  have hFcont : Continuous F := by rw [hFdef]; exact hcont
  have hFone : F 1 = 1 := by
    rw [hFdef]
    simp only [toLinearMap_mul_eq_mulLeft, mulLeft_one, LinearMap.det_id]
  have hneF : ∀ x : Quaternion ℝ, ‖x‖ = 1 → F x ≠ 0 := by
    intro x hx
    rw [hFdef]
    exact hne x hx
  -- the image of the sphere under `F` is preconnected, hence an interval
  have hpreF : IsPreconnected (F '' {x : Quaternion ℝ | ‖x‖ = 1}) :=
    hpre.image F hFcont.continuousOn
  have hord : (F '' {x : Quaternion ℝ | ‖x‖ = 1}).OrdConnected := hpreF.ordConnected
  have h1mem : (1 : ℝ) ∈ F '' {x : Quaternion ℝ | ‖x‖ = 1} :=
    ⟨1, by simp, hFone⟩
  have hqmem : F q ∈ F '' {x : Quaternion ℝ | ‖x‖ = 1} := ⟨q, hq, rfl⟩
  have h0not : (0 : ℝ) ∉ F '' {x : Quaternion ℝ | ‖x‖ = 1} := by
    rintro ⟨x, hx, hx0⟩
    exact hneF x hx hx0
  -- `1` and `F q` lie in the same interval which avoids `0`, so `F q > 0`
  change 0 < F q
  by_contra hcon
  have hle : F q ≤ 0 := le_of_not_gt hcon
  exact h0not (hord.out hqmem h1mem ⟨hle, zero_le_one⟩)

end Work.Agree
