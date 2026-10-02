import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.PTGeometric

/-- If `L : ℝ^N → ℝ^k` is a surjective linear map and `vv : ℝ^N` is a nonzero vector in its
kernel whose `0`-th coordinate is nonzero, then `L` admits a *continuous linear* right inverse `σ`
whose image lies in the hyperplane `{x | x 0 = 0}`.

Indeed, if `τ` is any right inverse of `L`, then
`σ y = τ y - ((τ y) 0 / (vv 0)) • vv` is linear, still satisfies `L (σ y) = y`
(because `L vv = 0`), and has vanishing `0`-th coordinate. -/
theorem exists_rightInverse_coord_eq_zero {N k : ℕ} [NeZero N]
    {L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin k)}
    {vv : EuclideanSpace ℝ (Fin N)} (hLv : L vv = 0) (hv0 : vv 0 ≠ 0)
    (hsurj : Function.Surjective L) :
    ∃ σ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin N),
      (∀ y, L (σ y) = y) ∧ (∀ y, (σ y) 0 = 0) := by
  obtain ⟨g, hg⟩ := L.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top_of_surjective _ hsurj)
  have hg' : ∀ y, L (g y) = y := by
    intro y
    have h := congrFun (congrArg DFunLike.coe hg) y
    simpa using h
  -- the `0`-th coordinate functional, as a linear map
  let c : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] ℝ :=
    (LinearMap.proj (R := ℝ) (0 : Fin N)).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ) :
        EuclideanSpace ℝ (Fin N) →ₗ[ℝ] (Fin N → ℝ))
  have hc : ∀ x, c x = x 0 := by
    intro x
    show (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)) x 0 = x 0
    rw [PiLp.continuousLinearEquiv_apply]
  -- the corrected section, linear by construction
  let σ₀ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin N) :=
    (g : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) -
      LinearMap.smulRight
        (((vv 0)⁻¹) • (c.comp (g : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)))) vv
  have hσ₀ : ∀ y, σ₀ y = g y - (((vv 0)⁻¹ * (g y) 0) • vv) := by
    intro y
    simp only [σ₀, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, hc, smul_eq_mul]
    rfl
  refine ⟨LinearMap.toContinuousLinearMap σ₀, ?_, ?_⟩
  · intro y
    change L (σ₀ y) = y
    rw [hσ₀ y, map_sub, map_smul, hLv, smul_zero, sub_zero]
    exact hg' y
  · intro y
    change (σ₀ y) 0 = 0
    rw [← hc (σ₀ y), hσ₀ y, map_sub, map_smul, hc, hc, smul_eq_mul]
    have key : (vv 0)⁻¹ * (g y) 0 * (vv 0) = (g y) 0 := by
      rw [mul_assoc, mul_comm ((g y) 0), ← mul_assoc, inv_mul_cancel₀ hv0, one_mul]
    rw [key, sub_self]

end Work.PTGeometric
