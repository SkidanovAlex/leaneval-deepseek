import Mathlib

namespace Work.KT

/-- Radial rescaling by a linear isomorphism: `x ↦ ‖x‖ • ((‖ψ x‖)⁻¹ • ψ x)`. -/
noncomputable def radRescale {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (ψ : V ≃ₗ[ℝ] W) (x : V) : W :=
  ‖x‖ • ((‖ψ x‖)⁻¹ • ψ x)

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- `smul_smul` normal form of the definition: the two scalars can be collected. -/
lemma radRescale_eq_smul (ψ : V ≃ₗ[ℝ] W) (x : V) :
    radRescale ψ x = (‖x‖ * ‖ψ x‖⁻¹) • ψ x := by
  rw [radRescale, smul_smul]

/-- `radRescale ψ` preserves the norm. -/
lemma radRescale_norm (ψ : V ≃ₗ[ℝ] W) (x : V) : ‖radRescale ψ x‖ = ‖x‖ := by
  rw [radRescale_eq_smul, norm_smul, norm_mul, norm_inv, Real.norm_of_nonneg (norm_nonneg x),
    Real.norm_of_nonneg (norm_nonneg (ψ x))]
  by_cases hx : x = 0
  · simp [hx]
  · have hψ : ψ x ≠ 0 := fun h => hx (ψ.map_eq_zero_iff.mp h)
    rw [mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hψ), mul_one]

/-- `ψ.symm` of a rescaled vector, in normal form. -/
lemma radRescale_symm_apply (ψ : V ≃ₗ[ℝ] W) (x : V) :
    ψ.symm (radRescale ψ x) = (‖x‖ * ‖ψ x‖⁻¹) • x := by
  rw [radRescale_eq_smul, map_smul, ψ.symm_apply_apply]

/-- Rescaling by `ψ` and then by `ψ.symm` is the identity. -/
lemma radRescale_inv_left (ψ : V ≃ₗ[ℝ] W) (x : V) :
    radRescale ψ.symm (radRescale ψ x) = x := by
  by_cases hx : x = 0
  · subst hx; simp [radRescale]
  · have hψ : ψ x ≠ 0 := fun h => hx (ψ.map_eq_zero_iff.mp h)
    have hn : ‖ψ x‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
    have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hnorm : ‖radRescale ψ x‖ = ‖x‖ := radRescale_norm ψ x
    have key : ψ.symm (radRescale ψ x) = (‖x‖ * ‖ψ x‖⁻¹) • x := radRescale_symm_apply ψ x
    have hnorm2 : ‖ψ.symm (radRescale ψ x)‖ = ‖x‖ * ‖ψ x‖⁻¹ * ‖x‖ := by
      rw [key, norm_smul, norm_mul, Real.norm_of_nonneg (norm_nonneg x),
        Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg (ψ x)))]
    rw [radRescale, hnorm, hnorm2, key, smul_smul, smul_smul]
    rw [show (‖x‖ * (‖x‖ * ‖ψ x‖⁻¹ * ‖x‖)⁻¹) * (‖x‖ * ‖ψ x‖⁻¹) = 1 from by
      field_simp, one_smul]

/-- `radRescale ψ` is continuous when `V` is finite-dimensional (so that `ψ` is continuous). -/
lemma radRescale_continuous [FiniteDimensional ℝ V] (ψ : V ≃ₗ[ℝ] W) :
    Continuous (radRescale ψ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, fun y hy => ?_⟩
    have h0 : radRescale ψ 0 = 0 := by simp [radRescale]
    have hd : dist (radRescale ψ y) (radRescale ψ 0) = dist y 0 := by
      rw [h0, dist_zero_right, dist_zero_right]
      exact radRescale_norm ψ y
    rw [hd]
    exact hy
  · have hψ : ψ x ≠ 0 := fun h => hx (ψ.map_eq_zero_iff.mp h)
    have hcψ : ContinuousAt (fun y : V => ψ y) x :=
      (ψ : V →ₗ[ℝ] W).continuous_of_finiteDimensional.continuousAt
    have hcont : ContinuousAt (fun y : V => (‖y‖ * ‖ψ y‖⁻¹) • ψ y) x := by
      refine ContinuousAt.smul ?_ hcψ
      exact (continuous_norm.continuousAt).mul
        ((hcψ.norm).inv₀ (norm_ne_zero_iff.mpr hψ))
    refine hcont.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall (fun y => radRescale_eq_smul ψ y)

/-- `Work.KT.radRescale ψ` preserves the norm, is continuous (for finite-dimensional `V`, `W`,
where every linear map is continuous), and is inverse to the rescaling by `ψ.symm`; hence it
induces a homeomorphism of the unit balls `Ball V ≃ Ball W` mapping `bdry V` onto `bdry W`.

Proof sketch. `radRescale ψ x = (‖x‖/‖ψ x‖) • ψ x` (`smul_smul`), of norm `‖x‖`: for `x ≠ 0` use
`ψ x ≠ 0` and `‖ψ x‖⁻¹ * ‖ψ x‖ = 1`; for `x = 0` both sides vanish (`inv_zero`). For continuity,
`ContinuousAt (radRescale ψ) 0` follows from `‖radRescale ψ x‖ = ‖x‖` and elsewhere use
`ContinuousAt.congr_of_eventuallyEq` with the formula `(‖x‖ * ‖ψ x‖⁻¹) • ψ x` together with
`Filter.EventuallyEq` from `φ ≠ 0` near a point where `φ x ≠ 0` (`ContinuousAt.inv₀` has the
`f a ≠ 0` hypothesis, so a local `≠ 0` is enough). For the inverse laws, reduce to
`‖x‖ • (‖x‖⁻¹ • x) = x` for `‖x‖ ≠ 0` and `0 ↦ 0`; a useful intermediate is that
`‖ψ.symm (radRescale ψ x)‖ = ‖x‖ ^ 2 * ‖ψ x‖⁻¹` for `x ≠ 0`. -/
lemma radRescaleSpec {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (ψ : V ≃ₗ[ℝ] W) :
    (∀ x : V, ‖radRescale ψ x‖ = ‖x‖) ∧ Continuous (radRescale ψ) ∧
      (∀ x : V, radRescale ψ.symm (radRescale ψ x) = x) ∧
      (∀ y : W, radRescale ψ (radRescale ψ.symm y) = y) :=
  ⟨radRescale_norm ψ, radRescale_continuous ψ, radRescale_inv_left ψ, fun y => by
    have h := radRescale_inv_left (ψ := ψ.symm) y
    rwa [LinearEquiv.symm_symm] at h⟩

end Work.KT
