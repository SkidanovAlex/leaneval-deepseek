import Mathlib

namespace Work.Mostow

/-- On a subspace `W` carrying a complex structure `J` (isometric, `J² = -1`) which commutes with
an isometry `T` preserving `W` and `W` under the inverse, the map
`x ↦ -(T (J x) - T⁻¹ (J x))/2` is symmetric on `W`. -/
theorem negSkwPartCompSymmetric {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : V ≃ₗᵢ[ℝ] V) (J : V →ₗ[ℝ] V) (W : Submodule ℝ V)
    (hTW : ∀ x ∈ W, T x ∈ W) (hTWi : ∀ x ∈ W, T.symm x ∈ W) (hJW : ∀ x ∈ W, J x ∈ W)
    (hJ2 : ∀ x ∈ W, J (J x) = -x) (hJi : ∀ x ∈ W, ‖J x‖ = ‖x‖)
    (hJT : ∀ x ∈ W, J (T x) = T (J x)) (hJTi : ∀ x ∈ W, J (T.symm x) = T.symm (J x)) :
    ∀ x ∈ W, ∀ y ∈ W,
      inner ℝ (-((2⁻¹ : ℝ) • (T (J x) - T.symm (J x)))) y
        = inner ℝ x (-((2⁻¹ : ℝ) • (T (J y) - T.symm (J y)))) := by
  -- `J` is an isometry for the inner product on `W` (polarization from norm preservation)
  have hJin : ∀ u ∈ W, ∀ v ∈ W, inner ℝ (J u) (J v) = inner ℝ u v := by
    intro u hu v hv
    have huv : u + v ∈ W := W.add_mem hu hv
    have h1 := norm_add_sq_real (J u) (J v)
    have h2 := norm_add_sq_real u v
    have hJuv : J (u + v) = J u + J v := map_add J u v
    have hnorm : ‖J u + J v‖ = ‖u + v‖ := by rw [← hJuv]; exact hJi (u + v) huv
    have hnu : ‖J u‖ = ‖u‖ := hJi u hu
    have hnv : ‖J v‖ = ‖v‖ := hJi v hv
    have hnorm2 : ‖J u + J v‖ ^ 2 = ‖u + v‖ ^ 2 := by rw [hnorm]
    have hnu2 : ‖J u‖ ^ 2 = ‖u‖ ^ 2 := by rw [hnu]
    have hnv2 : ‖J v‖ ^ 2 = ‖v‖ ^ 2 := by rw [hnv]
    linarith [h1, h2, hnorm2, hnu2, hnv2]
  -- hence `J` is anti-self-adjoint on `W`
  have hJorth : ∀ u ∈ W, ∀ v ∈ W, inner ℝ (J u) v = - inner ℝ u (J v) := by
    intro u hu v hv
    have hvW : J v ∈ W := hJW v hv
    have hv_eq : v = - J (J v) := by rw [hJ2 v hv, neg_neg]
    calc inner ℝ (J u) v = inner ℝ (J u) (- J (J v)) := by conv_lhs => rw [hv_eq]
      _ = - inner ℝ (J u) (J (J v)) := by rw [inner_neg_right]
      _ = - inner ℝ u (J v) := by rw [hJin u hu (J v) hvW]
  -- adjointness of `T` and `T⁻¹`
  have hadj1 : ∀ z w : V, inner ℝ (T z) w = inner ℝ z (T.symm w) := by
    intro z w
    have := LinearIsometryEquiv.inner_map_map T z (T.symm w)
    rwa [LinearIsometryEquiv.apply_symm_apply] at this
  have hadj2 : ∀ z w : V, inner ℝ (T.symm z) w = inner ℝ z (T w) := by
    intro z w
    have := LinearIsometryEquiv.inner_map_map T.symm z (T w)
    rwa [LinearIsometryEquiv.symm_apply_apply] at this
  -- the defining identity of the symmetric map
  have hmain : ∀ x ∈ W, ∀ y ∈ W,
      inner ℝ (T (J x) - T.symm (J x)) y = inner ℝ x (T (J y) - T.symm (J y)) := by
    intro x hx y hy
    have hTy : T y ∈ W := hTW y hy
    have hTiy : T.symm y ∈ W := hTWi y hy
    calc inner ℝ (T (J x) - T.symm (J x)) y
        = inner ℝ (J x) (T.symm y) - inner ℝ (J x) (T y) := by
            rw [inner_sub_left, hadj1, hadj2]
      _ = inner ℝ (J x) (T.symm y - T y) := by rw [inner_sub_right]
      _ = - inner ℝ x (J (T.symm y - T y)) := hJorth x hx (T.symm y - T y) (W.sub_mem hTiy hTy)
      _ = - inner ℝ x (T.symm (J y) - T (J y)) := by
            rw [map_sub J (T.symm y) (T y), hJTi y hy, hJT y hy]
      _ = inner ℝ x (T (J y) - T.symm (J y)) := by
            rw [show T.symm (J y) - T (J y) = -(T (J y) - T.symm (J y)) by rw [neg_sub],
                inner_neg_right, neg_neg]
  intro x hx y hy
  have hL : inner ℝ (-((2⁻¹ : ℝ) • (T (J x) - T.symm (J x)))) y
      = -(2⁻¹) * inner ℝ (T (J x) - T.symm (J x)) y := by
    rw [inner_neg_left, inner_smul_left]; simp
  have hR : inner ℝ x (-((2⁻¹ : ℝ) • (T (J y) - T.symm (J y))))
      = -(2⁻¹) * inner ℝ x (T (J y) - T.symm (J y)) := by
    rw [inner_neg_right, inner_smul_right]; ring
  rw [hL, hR, hmain x hx y hy]

end Work.Mostow
