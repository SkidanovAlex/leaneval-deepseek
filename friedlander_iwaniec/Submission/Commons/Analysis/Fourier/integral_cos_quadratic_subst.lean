import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Analysis.Fourier

/-- If `F` vanishes to the right of `√X`, its integral over `[0,∞)` equals its integral over
`[0, √X]`. -/
private lemma integral_Ici_eq_integral_sqrt_of_vanishes (F : ℝ → ℝ) (X : ℝ)
    (hF : ∀ t, Real.sqrt X < t → F t = 0) :
    (∫ t in Set.Ici (0 : ℝ), F t) = ∫ t in (0 : ℝ)..(Real.sqrt X), F t := by
  have h1 : (∫ t in Set.Ici (0 : ℝ), F t) = ∫ t in Set.Icc (0 : ℝ) (Real.sqrt X), F t := by
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici ?_ ?_
    · intro x hx
      exact hx.1
    · intro x hx
      rw [Set.mem_sdiff, Set.mem_Ici, Set.mem_Icc] at hx
      have hx' : Real.sqrt X < x := by
        by_contra h
        exact hx.2 ⟨hx.1, not_lt.mp h⟩
      exact hF x hx'
  rw [h1, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (Real.sqrt_nonneg X)]

theorem integral_cos_quadratic_subst (f : ℝ → ℝ) (X D b : ℝ) (hX : 0 < X) (hD : 0 < D)
    (k : ℕ) (hk : 1 ≤ k) (hsupp : ∀ u, X < u → f u = 0) :
    (∫ t in Set.Ici (0 : ℝ), f (t ^ 2 + b ^ 2) * Real.cos (2 * Real.pi * (k : ℝ) * t / D))
      = (Real.sqrt X / (k : ℝ)) * ∫ u in (0 : ℝ)..(k : ℝ),
          f (X * u ^ 2 / (k : ℝ) ^ 2 + b ^ 2)
            * Real.cos (2 * Real.pi * Real.sqrt X * u / D) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkR_ne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  set c : ℝ := Real.sqrt X / (k : ℝ) with hc_def
  set G : ℝ → ℝ := fun t => f (t ^ 2 + b ^ 2) * Real.cos (2 * Real.pi * (k : ℝ) * t / D)
    with hG_def
  set H : ℝ → ℝ := fun u => f (X * u ^ 2 / (k : ℝ) ^ 2 + b ^ 2)
    * Real.cos (2 * Real.pi * Real.sqrt X * u / D) with hH_def
  have hc_sq : c ^ 2 = X / (k : ℝ) ^ 2 := by
    rw [hc_def, div_pow, Real.sq_sqrt (le_of_lt hX)]
  have hck : c * (k : ℝ) = Real.sqrt X := by
    rw [hc_def]; field_simp
  have hc_ne : c ≠ 0 := by
    rw [hc_def]; exact div_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hX)) hkR_ne
  have hHu : ∀ u : ℝ, G (c * u) = H u := by
    intro u
    have h1 : (c * u) ^ 2 + b ^ 2 = X * u ^ 2 / (k : ℝ) ^ 2 + b ^ 2 := by
      rw [mul_pow, hc_sq]; ring
    have h2 : 2 * Real.pi * (k : ℝ) * (c * u) / D = 2 * Real.pi * Real.sqrt X * u / D := by
      have hkc : (k : ℝ) * (c * u) = Real.sqrt X * u := by
        have hkc' : (k : ℝ) * c = Real.sqrt X := by rw [mul_comm, hck]
        rw [← mul_assoc, hkc']
      rw [mul_assoc (2 * Real.pi) (k : ℝ) (c * u), hkc]
      ring
    rw [hG_def, hH_def]
    simp only
    rw [h1, h2]
  have hGvanish : ∀ t, Real.sqrt X < t → G t = 0 := by
    intro t ht
    rw [hG_def]
    simp only
    have ht2 : X < t ^ 2 := by
      have h1 : 0 < t - Real.sqrt X := sub_pos.mpr ht
      have h2 : 0 < t + Real.sqrt X := by linarith [Real.sqrt_nonneg X, ht]
      have hmul := mul_pos h1 h2
      have hsq : X = Real.sqrt X ^ 2 := (Real.sq_sqrt (le_of_lt hX)).symm
      nlinarith [hmul]
    have hXt : X < t ^ 2 + b ^ 2 := by nlinarith [sq_nonneg b, ht2]
    rw [hsupp _ hXt, zero_mul]
  have hstep1 : (∫ t in Set.Ici (0 : ℝ), G t) = ∫ t in (0 : ℝ)..(Real.sqrt X), G t :=
    integral_Ici_eq_integral_sqrt_of_vanishes G X hGvanish
  have hcomp : (∫ u in (0 : ℝ)..(k : ℝ), G (c * u))
      = c⁻¹ * ∫ x in (0 : ℝ)..(Real.sqrt X), G x := by
    rw [intervalIntegral.integral_comp_mul_left (f := G) (hc := hc_ne)]
    rw [mul_zero, hck, smul_eq_mul]
  have hB : (∫ x in (0 : ℝ)..(Real.sqrt X), G x)
      = c * ∫ u in (0 : ℝ)..(k : ℝ), G (c * u) := by
    rw [hcomp, ← mul_assoc, mul_inv_cancel₀ hc_ne, one_mul]
  have hC : (∫ u in (0 : ℝ)..(k : ℝ), G (c * u))
      = ∫ u in (0 : ℝ)..(k : ℝ), H u :=
    intervalIntegral.integral_congr (fun u _ => hHu u)
  rw [hstep1, hB, hC, hc_def]

end Commons.Analysis.Fourier