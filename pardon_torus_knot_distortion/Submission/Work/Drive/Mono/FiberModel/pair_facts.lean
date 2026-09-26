import Mathlib
import Submission.Work.Drive.Mono.FiberModel.Defs

/-!
# The pair `(⟪v,·⟫, ℓ)` is a surjective open map

For `v ≠ 0`, `ℓ v = 0` and `ℓ ≠ 0` the two functionals `⟪v,·⟫` and `ℓ` are linearly independent, so
`π = levPairCLM v ℓ : ℝ³ →L[ℝ] ℝ × ℝ` is surjective, hence open.  This is what makes the shadow of
the *open* box the interior of the shadow of the closed box.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Mono.FiberModel

noncomputable section

/-- **The pair `(⟪v,·⟫, ℓ)` is surjective** when `v ≠ 0`, `ℓ v = 0`, `ℓ ≠ 0`. -/
theorem levPairCLM_surjective {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) : Function.Surjective (levPairCLM v ℓ) := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : R3, ℓ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓne (ContinuousLinearMap.ext fun y => by simpa using h y)
  have hv2 : ‖v‖ ^ 2 ≠ 0 := by
    have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    positivity
  -- the image contains the two standard basis vectors
  have h1 : ((1 : ℝ), (0 : ℝ)) ∈ Set.range (levPairCLM v ℓ) := by
    refine ⟨(‖v‖ ^ 2)⁻¹ • v, ?_⟩
    rw [levPairCLM_apply]
    simp only [inner_smul_right, real_inner_self_eq_norm_sq, map_smul, smul_eq_mul, hℓv, mul_zero]
    rw [inv_mul_cancel₀ hv2]
  have h2 : ((0 : ℝ), (1 : ℝ)) ∈ Set.range (levPairCLM v ℓ) := by
    refine ⟨(ℓ w)⁻¹ • (w - (inner ℝ v w) • ((‖v‖ ^ 2)⁻¹ • v)), ?_⟩
    rw [levPairCLM_apply]
    simp only [map_sub, map_smul, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
      smul_eq_mul, hℓv, mul_zero, sub_zero]
    refine Prod.ext ?_ ?_
    · field_simp
      ring
    · field_simp
  intro X
  have hX : X = X.1 • ((1 : ℝ), (0 : ℝ)) + X.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  obtain ⟨y₁, hy₁⟩ := h1
  obtain ⟨y₂, hy₂⟩ := h2
  refine ⟨X.1 • y₁ + X.2 • y₂, ?_⟩
  rw [map_add, map_smul, map_smul, hy₁, hy₂]
  exact hX.symm

/-- **The pair `(⟪v,·⟫, ℓ)` is open.** -/
theorem levPairCLM_isOpenMap {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) : IsOpenMap (levPairCLM v ℓ) :=
  ContinuousLinearMap.isOpenMap _ (levPairCLM_surjective hv hℓv hℓne)

end

end Work.Drive.Mono.FiberModel
