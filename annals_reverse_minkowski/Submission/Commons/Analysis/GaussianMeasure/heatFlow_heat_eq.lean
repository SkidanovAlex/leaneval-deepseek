import Submission.Commons.Analysis.GaussianMeasure.heatFlow_contdiff

open MeasureTheory
open scoped Topology

namespace Commons.Analysis.GaussianMeasure

open Commons.Analysis.Gaussian
open HeatFlow

noncomputable section

/-! ## The pointwise heat identity for the Gaussian kernel `K`

The kernel `K u x y = u * exp (-π u² (y-x)²)` is (up to scaling) the Gaussian heat kernel.
Its second derivative in `x` and its derivative in `u` are related by
`K_xx = -2π u³ • K_u`, which is exactly the heat equation for the parametrization
`u = (√t)⁻¹`. -/

theorem K_xx_eq_neg_two_pi_cube_mul_K_u (u x y : ℝ) :
    K_xx u x y = (-2 * Real.pi * u ^ 3) * K_u u x y := by
  simp only [K_xx, K_u]
  ring

/-! ## Integrability of the integrands -/

theorem integrable_q_mul_K (q : ℝ → ℝ) (hq : AEStronglyMeasurable q volume)
    (hq1 : ∀ x, |q x| ≤ 1) {u : ℝ} (hu : 0 ≤ u) (x : ℝ) :
    Integrable (fun y => q y * K u x y) := by
  refine Integrable.mono' (integrable_K u x) (hq.mul (continuous_K_y u x).aestronglyMeasurable) ?_
  filter_upwards with y
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hK : 0 ≤ K u x y := by unfold K; positivity
  calc |q y| * |K u x y| ≤ 1 * |K u x y| := by gcongr; exact hq1 y
    _ = K u x y := by rw [one_mul, abs_of_nonneg hK]

theorem integrable_q_mul_K_x (q : ℝ → ℝ) (hq : AEStronglyMeasurable q volume)
    (hq1 : ∀ x, |q x| ≤ 1) {u x : ℝ} (hu : 0 < u) :
    Integrable (fun y => q y * K_x u x y) := by
  obtain ⟨δ, hδpos, _, B, hBint, _, hb2, _, _, _⟩ := gaussian_kernel_partial_bounds u x hu
  refine Integrable.mono' hBint (hq.mul (continuous_K_x_y u x).aestronglyMeasurable) ?_
  filter_upwards with y
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h : |K_x u x y| ≤ B y :=
    hb2 u x y (by rw [sub_self, abs_zero]; exact hδpos) (by rw [sub_self, abs_zero]; exact hδpos)
  calc |q y| * |K_x u x y| ≤ 1 * |K_x u x y| := by gcongr; exact hq1 y
    _ = |K_x u x y| := one_mul _
    _ ≤ B y := h

theorem integrable_q_mul_K_u (q : ℝ → ℝ) (hq : AEStronglyMeasurable q volume)
    (hq1 : ∀ x, |q x| ≤ 1) {u x : ℝ} (hu : 0 < u) :
    Integrable (fun y => q y * K_u u x y) := by
  obtain ⟨δ, hδpos, _, B, hBint, hb1, _, _, _, _⟩ := gaussian_kernel_partial_bounds u x hu
  refine Integrable.mono' hBint (hq.mul (continuous_K_u_y u x).aestronglyMeasurable) ?_
  filter_upwards with y
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h : |K_u u x y| ≤ B y :=
    hb1 u x y (by rw [sub_self, abs_zero]; exact hδpos) (by rw [sub_self, abs_zero]; exact hδpos)
  calc |q y| * |K_u u x y| ≤ 1 * |K_u u x y| := by gcongr; exact hq1 y
    _ = |K_u u x y| := one_mul _
    _ ≤ B y := h

/-! ## Differentiation under the integral sign for the smoothed function -/

theorem hasDerivAt_integral_q_mul_K_x (q : ℝ → ℝ) (hq : AEStronglyMeasurable q volume)
    (hq1 : ∀ x, |q x| ≤ 1) {u x : ℝ} (hu : 0 < u) :
    HasDerivAt (fun x' => ∫ y, q y * K u x' y) (∫ y, q y * K_x u x y) x := by
  obtain ⟨δ, hδpos, _, B, hBint, _, hb2, _, _, _⟩ := gaussian_kernel_partial_bounds u x hu
  have hs : Set.Ioo (x - δ) (x + δ) ∈ 𝓝 x := Ioo_mem_nhds (by linarith) (by linarith)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun x' y => q y * K u x' y)
    (F' := fun x' y => q y * K_x u x' y) (bound := B) (s := Set.Ioo (x - δ) (x + δ)) hs
    ?_ ?_ ?_ ?_ hBint ?_).2
  · filter_upwards with x'
    exact hq.mul (continuous_K_y u x').aestronglyMeasurable
  · exact integrable_q_mul_K q hq hq1 hu.le x
  · exact hq.mul (continuous_K_x_y u x).aestronglyMeasurable
  · filter_upwards with y x' hx'
    rw [Real.norm_eq_abs]
    have h : |K_x u x' y| ≤ B y := by
      refine hb2 u x' y ?_ ?_
      · rw [sub_self, abs_zero]; exact hδpos
      · rw [abs_lt]; exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
    calc |q y * K_x u x' y| = |q y| * |K_x u x' y| := abs_mul _ _
      _ ≤ 1 * |K_x u x' y| := by gcongr; exact hq1 y
      _ = |K_x u x' y| := one_mul _
      _ ≤ B y := h
  · filter_upwards with y x' hx'
    exact (hasDerivAt_K_x u x' y).const_mul (q y)

theorem hasDerivAt_integral_q_mul_K_xx (q : ℝ → ℝ) (hq : AEStronglyMeasurable q volume)
    (hq1 : ∀ x, |q x| ≤ 1) {u x : ℝ} (hu : 0 < u) :
    HasDerivAt (fun x' => ∫ y, q y * K_x u x' y) (∫ y, q y * K_xx u x y) x := by
  obtain ⟨δ, hδpos, _, B, hBint, _, _, _, _, hb5⟩ := gaussian_kernel_partial_bounds u x hu
  have hs : Set.Ioo (x - δ) (x + δ) ∈ 𝓝 x := Ioo_mem_nhds (by linarith) (by linarith)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun x' y => q y * K_x u x' y)
    (F' := fun x' y => q y * K_xx u x' y) (bound := B) (s := Set.Ioo (x - δ) (x + δ)) hs
    ?_ ?_ ?_ ?_ hBint ?_).2
  · filter_upwards with x'
    exact hq.mul (continuous_K_x_y u x').aestronglyMeasurable
  · exact integrable_q_mul_K_x q hq hq1 hu
  · exact hq.mul (continuous_K_xx_y u x).aestronglyMeasurable
  · filter_upwards with y x' hx'
    rw [Real.norm_eq_abs]
    have h : |K_xx u x' y| ≤ B y :=
      le_trans (abs_K_xx_le_add u x' y hu.le)
        (hb5 u x' y (by rw [sub_self, abs_zero]; exact hδpos)
          (by rw [abs_lt]; exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩))
    calc |q y * K_xx u x' y| = |q y| * |K_xx u x' y| := abs_mul _ _
      _ ≤ 1 * |K_xx u x' y| := by gcongr; exact hq1 y
      _ = |K_xx u x' y| := one_mul _
      _ ≤ B y := h
  · filter_upwards with y x' hx'
    exact (hasDerivAt_K_xx u x' y).const_mul (q y)

theorem hasDerivAt_integral_q_mul_K_u (q : ℝ → ℝ) (hq : AEStronglyMeasurable q volume)
    (hq1 : ∀ x, |q x| ≤ 1) {u x : ℝ} (hu : 0 < u) :
    HasDerivAt (fun u' => ∫ y, q y * K u' x y) (∫ y, q y * K_u u x y) u := by
  obtain ⟨δ, hδpos, _, B, hBint, hb1, _, _, _, _⟩ := gaussian_kernel_partial_bounds u x hu
  have hs : Set.Ioo (u - δ) (u + δ) ∈ 𝓝 u := Ioo_mem_nhds (by linarith) (by linarith)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun u' y => q y * K u' x y)
    (F' := fun u' y => q y * K_u u' x y) (bound := B) (s := Set.Ioo (u - δ) (u + δ)) hs
    ?_ ?_ ?_ ?_ hBint ?_).2
  · filter_upwards with u'
    exact hq.mul (continuous_K_y u' x).aestronglyMeasurable
  · exact integrable_q_mul_K q hq hq1 hu.le x
  · exact hq.mul (continuous_K_u_y u x).aestronglyMeasurable
  · filter_upwards with y u' hu'
    rw [Real.norm_eq_abs]
    have h : |K_u u' x y| ≤ B y := by
      refine hb1 u' x y ?_ ?_
      · rw [abs_lt]; exact ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
      · rw [sub_self, abs_zero]; exact hδpos
    calc |q y * K_u u' x y| = |q y| * |K_u u' x y| := abs_mul _ _
      _ ≤ 1 * |K_u u' x y| := by gcongr; exact hq1 y
      _ = |K_u u' x y| := one_mul _
      _ ≤ B y := h
  · filter_upwards with y u' hu'
    exact (hasDerivAt_K_u u' x y).const_mul (q y)

/-! ## Derivative of `t ↦ (√t)⁻¹` -/

theorem hasDerivAt_sqrt_inv (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (Real.sqrt s)⁻¹) (-(1 / 2) * ((Real.sqrt t)⁻¹) ^ 3) t := by
  have htne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have h := (Real.hasDerivAt_sqrt (ne_of_gt ht)).inv htne
  refine h.congr_deriv ?_
  rw [inv_pow]
  field_simp

/-! ## The heat equation for the Gaussian-smoothed function -/

theorem heatFlow_heat_eq (q : ℝ → ℝ) (hq : ∀ x, |q x| ≤ 1) :
    ∀ t : ℝ, 0 < t → ∀ x : ℝ,
      deriv (fun y : ℝ => deriv (fun y' : ℝ => ∫ z, q (y' + Real.sqrt t * z) * Real.exp (-Real.pi * z ^ 2)) y) x
        = 4 * Real.pi * deriv (fun s : ℝ => ∫ z, q (x + Real.sqrt s * z) * Real.exp (-Real.pi * z ^ 2)) t := by
  intro t ht x
  have hu : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr (Real.sqrt_pos.2 ht)
  -- The right-hand side, as a function of the time parameter, is eventually the kernel form.
  have hR : (fun s : ℝ => ∫ z, q (x + Real.sqrt s * z) * Real.exp (-Real.pi * z ^ 2)) =ᶠ[𝓝 t]
      (fun s : ℝ => ∫ y, q y * K ((Real.sqrt s)⁻¹) x y) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact subst_K q hs
  rw [hR.deriv_eq]
  -- The left-hand side inner function is the kernel form at time `t`.
  have hFfun : (fun y' : ℝ => ∫ z, q (y' + Real.sqrt t * z) * Real.exp (-Real.pi * z ^ 2))
      = fun y' : ℝ => ∫ y, q y * K ((Real.sqrt t)⁻¹) y' y := by
    funext y'
    exact subst_K q ht
  rw [hFfun]
  by_cases hmeas : AEStronglyMeasurable q volume
  · -- Measurable case: differentiate under the integral sign.
    have hLHS : deriv (fun y : ℝ => deriv (fun y' : ℝ => ∫ y, q y * K ((Real.sqrt t)⁻¹) y' y) y) x
        = ∫ y, q y * K_xx ((Real.sqrt t)⁻¹) x y := by
      have hfun : (fun y : ℝ => deriv (fun y' : ℝ => ∫ w, q w * K ((Real.sqrt t)⁻¹) y' w) y)
          = fun y : ℝ => ∫ w, q w * K_x ((Real.sqrt t)⁻¹) y w := by
        funext y
        exact (hasDerivAt_integral_q_mul_K_x q hmeas hq hu (x := y)).deriv
      rw [hfun]
      exact (hasDerivAt_integral_q_mul_K_xx q hmeas hq hu).deriv
    have hRHS : deriv (fun s : ℝ => ∫ y, q y * K ((Real.sqrt s)⁻¹) x y) t
        = (∫ y, q y * K_u ((Real.sqrt t)⁻¹) x y) * (-(1 / 2) * ((Real.sqrt t)⁻¹) ^ 3) := by
      have hP : HasDerivAt (fun u' : ℝ => ∫ y, q y * K u' x y)
          (∫ y, q y * K_u ((Real.sqrt t)⁻¹) x y) ((Real.sqrt t)⁻¹) :=
        hasDerivAt_integral_q_mul_K_u q hmeas hq hu (u := (Real.sqrt t)⁻¹) (x := x)
      exact (hP.comp t (hasDerivAt_sqrt_inv t ht)).deriv
    rw [hLHS, hRHS]
    -- pointwise heat identity for the kernel
    have hpt : (fun y : ℝ => q y * K_xx ((Real.sqrt t)⁻¹) x y)
        = fun y : ℝ => (-2 * Real.pi * ((Real.sqrt t)⁻¹) ^ 3) *
            (q y * K_u ((Real.sqrt t)⁻¹) x y) := by
      funext y
      rw [K_xx_eq_neg_two_pi_cube_mul_K_u]
      ring
    rw [hpt, integral_const_mul]
    ring
  · -- Non-measurable case: every integral vanishes.
    have hzero : ∀ (w s : ℝ), 0 < s → (∫ y, q y * K ((Real.sqrt s)⁻¹) w y) = 0 := by
      intro w s hs
      exact integral_non_aestronglyMeasurable
        (not_aesm_mul_K (inv_pos.mpr (Real.sqrt_pos.2 hs)) hmeas)
    have hL : (fun y' : ℝ => ∫ y, q y * K ((Real.sqrt t)⁻¹) y' y) = fun _ : ℝ => (0 : ℝ) := by
      funext y'
      exact hzero y' t ht
    have hR0 : (fun s : ℝ => ∫ y, q y * K ((Real.sqrt s)⁻¹) x y) = fun _ : ℝ => (0 : ℝ) := by
      funext s
      by_cases hs : 0 < s
      · exact hzero x s hs
      · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hs), inv_zero]
        simp [K]
    rw [hL, hR0]
    simp

end

end Commons.Analysis.GaussianMeasure
