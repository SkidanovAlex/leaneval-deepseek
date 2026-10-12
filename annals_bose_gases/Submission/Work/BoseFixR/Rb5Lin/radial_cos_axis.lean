import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.Rb5Lin.radial_cos_axis`

**Rotation reduction of the plane-wave factor against a radial weight.** For an arbitrary
profile `ψ : ℝ → ℝ` and an arbitrary wave vector `q`,

  `∫ x, ψ ‖x‖ * cos ⟪q, x⟫ = ∫ z, ψ ‖z‖ * cos (‖q‖ * z 2)`,

i.e. the integral only sees `‖q‖`, and `q` may be rotated onto the second coordinate axis.

The proof is the standard one: the group of linear isometry equivalences of `ℝ³` acts
transitively on the unit sphere, and the Lebesgue measure is invariant under it
(`LinearIsometryEquiv.measurePreserving`), so we may change variables by an isometry
carrying `‖q‖ • e₂` to `q`.  Concretely, for `q ≠ 0` we take `U` with
`U e₂ = ‖q‖⁻¹ • q`, so that `U.symm q = ‖q‖ • e₂` and

  `⟪q, U x⟫ = ⟪U.symm q, x⟫ = ‖q‖ * ⟪e₂, x⟫ = ‖q‖ * x 2`.

The auxiliary existential statement `exists_isometryEquiv_single_eq` (any unit vector is the
image of `e₂` under some linear isometry equivalence) is proved by extending the one-element
orthonormal family `{v}` to an orthonormal basis with `v` in slot `2` and comparing it with the
standard basis via `OrthonormalBasis.repr`.

The reduction is *unconditional* in `ψ`: no measurability or integrability is assumed.  This is
possible because `MeasureTheory.MeasurePreserving.integral_comp'` is stated for a measurable
*equivalence* and therefore needs no a.e. strong measurability of the integrand.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixR.Rb5Lin

/-- **Transitivity on the unit sphere (special shape).**  Every unit vector `v` of `ℝ³` is the
image of the second standard basis vector `e₂ = EuclideanSpace.single 2 1` under a linear
isometry equivalence.

Proof: extend the orthonormal family `{v}` to an orthonormal basis `b` with `b 2 = v`
(`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`), and let `U` be the linear
isometry equivalence which reads off the coordinates of a vector in the standard basis
`EuclideanSpace.basisFun (Fin 3) ℝ` and then re-assembles them in the basis `b`; by
construction `U e₂ = b 2 = v`. -/
theorem exists_isometryEquiv_single_eq {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1) :
    ∃ U : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      U (EuclideanSpace.single (2 : Fin 3) 1) = v := by
  set f : Fin 3 → EuclideanSpace ℝ (Fin 3) := fun i => if i = 2 then v else 0 with hf
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = Fintype.card (Fin 3) :=
    finrank_euclideanSpace
  have horth : Orthonormal ℝ ((({2} : Set (Fin 3))).domRestrict f) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : ((i : Fin 3)) = 2 := Set.mem_singleton_iff.mp i.2
    have hj : ((j : Fin 3)) = 2 := Set.mem_singleton_iff.mp j.2
    have hij : i = j := Subtype.ext (by rw [hi, hj])
    have hfi : f (i : Fin 3) = v := by simp [hf, hi]
    have hfj : f (j : Fin 3) = v := by simp [hf, hj]
    rw [Set.domRestrict_apply, Set.domRestrict_apply, hfi, hfj, if_pos hij,
      real_inner_self_eq_norm_sq, hv]
    norm_num
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard horth
  refine ⟨(EuclideanSpace.basisFun (Fin 3) ℝ).repr.trans b.repr.symm, ?_⟩
  rw [LinearIsometryEquiv.trans_apply, ← EuclideanSpace.basisFun_apply (Fin 3) ℝ 2,
      OrthonormalBasis.repr_self, ← OrthonormalBasis.repr_self b 2,
      LinearIsometryEquiv.symm_apply_apply, hb 2 (by simp)]
  simp [hf]

/-- **The rotation reduction.**  For any profile `ψ` and any wave vector `q`,
`∫ x, ψ ‖x‖ * cos ⟪q, x⟫ = ∫ z, ψ ‖z‖ * cos (‖q‖ * z 2)`.

For `q = 0` both sides are `∫ x, ψ ‖x‖`.  Otherwise take `U` with `U e₂ = ‖q‖⁻¹ • q` (so that
`U.symm q = ‖q‖ • e₂`), change variables by `U` (which preserves Lebesgue measure, and for which
the change-of-variables formula holds with no measurability assumption on `ψ` since `U` is a
measurable equivalence), and rewrite the inner product
`⟪q, U x⟫ = ⟪U.symm q, x⟫ = ‖q‖ * x 2`. -/
theorem radial_cos_axis {ψ : ℝ → ℝ} (q : EuclideanSpace ℝ (Fin 3)) :
    (∫ x : EuclideanSpace ℝ (Fin 3), ψ ‖x‖ * Real.cos (inner ℝ q x))
      = ∫ z : EuclideanSpace ℝ (Fin 3), ψ ‖z‖ * Real.cos (‖q‖ * z 2) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · have hqnorm : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
    have hv : ‖‖q‖⁻¹ • q‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg q)),
        inv_mul_cancel₀ hqnorm]
    obtain ⟨U, hU⟩ := exists_isometryEquiv_single_eq hv
    have hUsymm : U.symm q = ‖q‖ • EuclideanSpace.single (2 : Fin 3) 1 := by
      have h1 : U (‖q‖ • EuclideanSpace.single (2 : Fin 3) 1) = q := by
        rw [map_smul, hU, smul_smul, mul_inv_cancel₀ hqnorm, one_smul]
      calc U.symm q = U.symm (U (‖q‖ • EuclideanSpace.single (2 : Fin 3) 1)) := by rw [h1]
        _ = ‖q‖ • EuclideanSpace.single (2 : Fin 3) 1 :=
            LinearIsometryEquiv.symm_apply_apply U _
    have hcomp := MeasureTheory.MeasurePreserving.integral_comp' (μ := volume) (ν := volume)
        (f := U.toMeasurableEquiv) (LinearIsometryEquiv.measurePreserving U)
        (fun y : EuclideanSpace ℝ (Fin 3) => ψ ‖y‖ * Real.cos (inner ℝ q y))
    rw [← hcomp]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [LinearIsometryEquiv.coe_toMeasurableEquiv]
    have hinner : inner ℝ q (U x) = inner ℝ (U.symm q) x := by
      rw [← LinearIsometryEquiv.inner_map_map U (U.symm q) x,
        LinearIsometryEquiv.apply_symm_apply]
    have hfin : inner ℝ q (U x) = ‖q‖ * x 2 := by
      rw [hinner, hUsymm, real_inner_smul_left, ← EuclideanSpace.basisFun_apply (Fin 3) ℝ 2,
        EuclideanSpace.basisFun_inner]
    rw [LinearIsometryEquiv.norm_map, hfin]

end Work.BoseFixR.Rb5Lin
