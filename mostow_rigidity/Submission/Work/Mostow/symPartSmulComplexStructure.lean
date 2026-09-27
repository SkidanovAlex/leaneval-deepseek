import Mathlib

namespace Work.Mostow

/-- If an isometry `T` of a real inner product space satisfies `(T + T⁻¹)/2 = c • id` on a subspace
`W` with `|c| < 1`, then `J := (√(1-c²))⁻¹ • (T - c • id)` is an orthogonal complex structure
on `W`: `J (J x) = -x` and `‖J x‖ = ‖x‖` for `x ∈ W`. -/
theorem symPartSmulComplexStructure {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : V ≃ₗᵢ[ℝ] V) (W : Submodule ℝ V) (c : ℝ) (hc1 : |c| < 1)
    (hc : ∀ x ∈ W, (2⁻¹ : ℝ) • (T x + T.symm x) = c • x) :
    (∀ x ∈ W, ((Real.sqrt (1 - c^2))⁻¹ • ((T : V →ₗ[ℝ] V) - c • 1))
        (((Real.sqrt (1 - c^2))⁻¹ • ((T : V →ₗ[ℝ] V) - c • 1)) x) = -x) ∧
    (∀ x ∈ W, ‖((Real.sqrt (1 - c^2))⁻¹ • ((T : V →ₗ[ℝ] V) - c • 1)) x‖ = ‖x‖) := by
  have hpos : 0 < 1 - c^2 := by
    have h := abs_lt.mp hc1
    nlinarith [h.1, h.2]
  set s : ℝ := Real.sqrt (1 - c^2) with hs
  have hssq : s^2 = 1 - c^2 := by rw [hs]; exact Real.sq_sqrt hpos.le
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hpos
  set L : V →ₗ[ℝ] V := (T : V →ₗ[ℝ] V) - c • 1 with hL
  -- `T (T.symm y) = y` in the linear-map coercion
  have happ : ∀ y : V, (T : V →ₗ[ℝ] V) (T.symm y) = y :=
    fun y => LinearIsometryEquiv.apply_symm_apply T y
  -- `T` preserves inner products
  have himm : ∀ a b : V, inner ℝ ((T : V →ₗ[ℝ] V) a) ((T : V →ₗ[ℝ] V) b) = inner ℝ a b :=
    fun a b => LinearIsometryEquiv.inner_map_map T a b
  -- `T.symm` is the adjoint of `T`
  have hsymm_inner : ∀ u v : V, inner ℝ (T.symm u) v = inner ℝ u (T v) := by
    intro u v
    have h := LinearIsometryEquiv.inner_map_map T (T.symm u) v
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    exact h.symm
  -- `T x + T⁻¹ x = 2c x` for `x ∈ W`
  have h2 : ∀ x ∈ W, T x + T.symm x = (2 * c) • x := by
    intro x hx
    have h' : (2:ℝ) • ((2⁻¹:ℝ) • (T x + T.symm x)) = (2:ℝ) • (c • x) := by rw [hc x hx]
    rwa [smul_smul, mul_inv_cancel₀ (by norm_num : (2:ℝ) ≠ 0), one_smul, smul_smul] at h'
  -- `T² x = 2c T x - x` for `x ∈ W`
  have hTadd : ∀ x ∈ W, (T : V →ₗ[ℝ] V) ((T : V →ₗ[ℝ] V) x) =
      (2 * c) • ((T : V →ₗ[ℝ] V) x) - x := by
    intro x hx
    have h3 : (T : V →ₗ[ℝ] V) ((T : V →ₗ[ℝ] V) x) + x =
        (2 * c) • ((T : V →ₗ[ℝ] V) x) := by
      calc (T : V →ₗ[ℝ] V) ((T : V →ₗ[ℝ] V) x) + x
          = (T : V →ₗ[ℝ] V) ((T : V →ₗ[ℝ] V) x) + (T : V →ₗ[ℝ] V) (T.symm x) := by rw [happ x]
        _ = (T : V →ₗ[ℝ] V) ((T : V →ₗ[ℝ] V) x + T.symm x) := by rw [map_add]
        _ = (T : V →ₗ[ℝ] V) (T x + T.symm x) := rfl
        _ = (T : V →ₗ[ℝ] V) ((2 * c) • x) := by rw [h2 x hx]
        _ = (2 * c) • ((T : V →ₗ[ℝ] V) x) := by rw [map_smul]
    rw [eq_sub_iff_add_eq]
    exact h3
  -- `L (L x) = (c² - 1) x` for `x ∈ W`
  have hLL : ∀ x ∈ W, L (L x) = (c^2 - 1) • x := by
    intro x hx
    have hA := hTadd x hx
    rw [hL]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul]
    rw [hA]
    module
  -- `⟪T x, x⟫ = c ‖x‖²` for `x ∈ W`
  have hinner : ∀ x ∈ W, inner ℝ ((T : V →ₗ[ℝ] V) x) x = c * ‖x‖^2 := by
    intro x hx
    have h := congrArg (fun y => inner ℝ y x) (h2 x hx)
    rw [inner_add_left, real_inner_smul_left] at h
    rw [hsymm_inner] at h
    rw [show inner ℝ x (T x) = inner ℝ (T x) x from real_inner_comm _ _] at h
    rw [real_inner_self_eq_norm_sq] at h
    have hfin : inner ℝ (T x) x = c * ‖x‖^2 := by linarith
    exact hfin
  -- `‖L x‖² = (1 - c²) ‖x‖²` for `x ∈ W`
  have hLnormsq : ∀ x ∈ W, ‖L x‖^2 = (1 - c^2) * ‖x‖^2 := by
    intro x hx
    have hLx : ((T : V →ₗ[ℝ] V) - c • 1) x = (T : V →ₗ[ℝ] V) x - c • x := by
      rw [LinearMap.sub_apply, LinearMap.smul_apply]; simp
    have hncx : ‖c • x‖^2 = c^2 * ‖x‖^2 := by rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [hL]
    rw [show ‖((T : V →ₗ[ℝ] V) - c • 1) x‖^2
          = inner ℝ (((T : V →ₗ[ℝ] V) - c • 1) x) (((T : V →ₗ[ℝ] V) - c • 1) x)
        from (real_inner_self_eq_norm_sq _).symm]
    rw [hLx, inner_sub_left, inner_sub_right, inner_sub_right]
    rw [himm, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_self_eq_norm_sq, hinner x hx]
    rw [show inner ℝ x ((T : V →ₗ[ℝ] V) x) = c * ‖x‖^2 from by
      rw [real_inner_comm]; exact hinner x hx]
    rw [real_inner_self_eq_norm_sq, hncx]
    ring
  -- `‖L x‖ = s ‖x‖` for `x ∈ W`
  have hLnorm : ∀ x ∈ W, ‖L x‖ = s * ‖x‖ := by
    intro x hx
    have hnn : 0 ≤ s * ‖x‖ := mul_nonneg hspos.le (norm_nonneg x)
    calc ‖L x‖ = Real.sqrt (‖L x‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt ((1 - c^2) * ‖x‖^2) := by rw [hLnormsq x hx]
      _ = Real.sqrt (s^2 * ‖x‖^2) := by rw [← hssq]
      _ = Real.sqrt ((s * ‖x‖)^2) := by congr 1; ring
      _ = s * ‖x‖ := Real.sqrt_sq hnn
  constructor
  · intro x hx
    have h := hLL x hx
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, smul_smul, h, smul_smul]
    have hcoef : s⁻¹ * s⁻¹ * (c^2 - 1) = -1 := by
      field_simp
      nlinarith [hssq]
    rw [hcoef, neg_one_smul]
  · intro x hx
    rw [LinearMap.smul_apply, norm_smul, hLnorm x hx,
      Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hspos))]
    rw [← mul_assoc, inv_mul_cancel₀ hspos.ne', one_mul]

end Work.Mostow
