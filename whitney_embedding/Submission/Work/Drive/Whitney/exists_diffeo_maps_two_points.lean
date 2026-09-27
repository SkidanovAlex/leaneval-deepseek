import Mathlib

/-!
# Moving any two distinct points to any two distinct points by a diffeomorphism

`Work.Drive.Whitney.exists_diffeo_maps_two_points`: for `a ≠ b` and `c ≠ d` in
`EuclideanSpace ℝ (Fin n)` there is a smooth self-map `Ψ` of `ℝⁿ` together with a smooth
two-sided inverse `Ψinv`, with `Ψ a = c` and `Ψ b = d`.

The construction is the elementary affine one: the map
`x ↦ c + R (ρ • (x - a))`, where `ρ > 0` and `R` is the linear isometry carrying
`ρ • (b - a)` onto `d - c`; such a `(R, ρ)` is produced by `exists_linearIsometryEquiv_smul_eq`
(a reflection, `Submodule.reflection_sub`).  The inverse is `y ↦ a + ρ⁻¹ • R.symm (y - c)`.
-/

namespace Work.Drive.Whitney

open scoped RealInnerProductSpace

/-- A linear isometry carrying a prescribed positive multiple of `v` onto `w`, for nonzero
`v w` in `ℝⁿ`: take `ρ = ‖w‖ / ‖v‖` and reflect in the hyperplane orthogonal to `ρ • v - w`.
This is the linear half of the two-point transitivity of the diffeomorphism group of `ℝⁿ`. -/
theorem exists_linearIsometryEquiv_smul_eq {n : ℕ} (v w : EuclideanSpace ℝ (Fin n))
    (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (ρ : ℝ),
      0 < ρ ∧ R (ρ • v) = w := by
  refine ⟨((ℝ ∙ ((‖w‖ / ‖v‖) • v - w))ᗮ).reflection, ‖w‖ / ‖v‖,
    div_pos (norm_pos_iff.mpr hw) (norm_pos_iff.mpr hv), ?_⟩
  refine Submodule.reflection_sub ?_
  rw [norm_smul, Real.norm_of_nonneg (div_pos (norm_pos_iff.mpr hw) (norm_pos_iff.mpr hv)).le,
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hv)]

theorem exists_diffeo_maps_two_points {n : ℕ} (a b c d : EuclideanSpace ℝ (Fin n))
    (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (Ψinv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψinv ∧
      Function.LeftInverse Ψinv Ψ ∧ Function.RightInverse Ψinv Ψ ∧
      Ψ a = c ∧ Ψ b = d := by
  have hab' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hcd' : d - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hcd)
  obtain ⟨R, ρ, hρpos, hR⟩ := exists_linearIsometryEquiv_smul_eq (b - a) (d - c) hab' hcd'
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  refine ⟨fun x => c + R (ρ • (x - a)), fun y => a + ρ⁻¹ • R.symm (y - c),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness of the direct map
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin n) => x - a) :=
      contDiff_id.sub contDiff_const
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin n) => ρ • (x - a)) :=
      h1.const_smul ρ
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin n) => R (ρ • (x - a))) :=
      R.contDiff.comp h2
    exact contDiff_const.add h3
  · -- smoothness of the inverse
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin n) => y - c) :=
      contDiff_id.sub contDiff_const
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin n) => R.symm (y - c)) :=
      R.symm.contDiff.comp h1
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin n) => ρ⁻¹ • R.symm (y - c)) :=
      h2.const_smul ρ⁻¹
    exact contDiff_const.add h3
  · intro x
    simp only [add_sub_cancel_left, LinearIsometryEquiv.symm_apply_apply, smul_smul,
      inv_mul_cancel₀ hρne, one_smul, add_sub_cancel]
  · intro y
    simp only [add_sub_cancel_left, LinearIsometryEquiv.apply_symm_apply, smul_smul,
      mul_inv_cancel₀ hρne, one_smul, add_sub_cancel]
  · simp
  · show c + R (ρ • (b - a)) = d
    rw [hR, add_sub_cancel]

end Work.Drive.Whitney
