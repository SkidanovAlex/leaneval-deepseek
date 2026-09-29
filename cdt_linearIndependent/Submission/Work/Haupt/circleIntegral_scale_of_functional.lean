import Mathlib

/-!
# Scaling of a weighted circle integral under the functional equation `f (x² t) = f t / (x t)`

If `f : ℂ → ℂ` satisfies `f (x ^ 2 * t) = f t / (x * t)` for every `t ≠ 0`, then reparametrising
the circle `C(0, ρ)` by `t = x ^ 2 * u`, where `u` runs over the circle `C(0, ρ / ‖x‖ ^ 2)`, gives

`∮ t in C(0, ρ), t ^ (-(n+1)) * f t = x ^ (-(2n+1)) * ∮ u in C(0, ρ / ‖x‖ ^ 2), u ^ (-(n+2)) * f u`.

The two parametrisations differ by the rotation `x ^ 2 / ‖x‖ ^ 2` of the unit circle; since a
period of the integrand is `2π`, the corresponding shift in the parameter does not change the
integral.  Nothing is assumed about `f` itself (in particular no regularity), so the argument is
purely a change of variable for the parametrised integral.
-/

namespace Work.Haupt

open Complex MeasureTheory intervalIntegral

/-- `a * a ^ k = a ^ (1 + k)` for `a ≠ 0`, phrased so that the `ℤ`-powers combine. -/
lemma mul_zpow_one (a : ℂ) (ha : a ≠ 0) (k : ℤ) : a * a ^ k = a ^ (1 + k) := by
  have h := (zpow_add₀ ha 1 k).symm
  rwa [zpow_one] at h

/-- Algebraic core of the change of variables: for nonzero `x`, `u` the two monomials coincide. -/
lemma circleIntegral_scale_alg (x u fu : ℂ) (hx : x ≠ 0) (hu : u ≠ 0) (n : ℤ) :
    (x ^ 2 * u * I) * ((x ^ 2 * u) ^ (-(n + 1)) * (fu / (x * u))) =
      x ^ (-(2 * n + 1)) * ((u * I) * (u ^ (-(n + 2)) * fu)) := by
  have hx3 : x ^ (2 : ℤ) * x ^ (2 * (-(n + 1))) * x ^ (-1 : ℤ) = x ^ (-(2 * n + 1)) := by
    rw [← zpow_add₀ hx, ← zpow_add₀ hx]; congr 1; ring
  have hu2 : u * u ^ (-(n + 2)) = u ^ (-(n + 1)) := by
    rw [mul_zpow_one u hu]; congr 1; ring
  have hu3 : u * u ^ (-(n + 1)) * u ^ (-1 : ℤ) = u ^ (-(n + 1)) := by
    rw [mul_zpow_one u hu, ← zpow_add₀ hu]; congr 1; ring
  rw [div_eq_mul_inv, mul_inv, mul_zpow]
  rw [show x ^ 2 = x ^ (2 : ℤ) by exact (zpow_natCast x 2).symm]
  rw [← zpow_mul]
  rw [show x⁻¹ = x ^ (-1 : ℤ) by rw [zpow_neg_one],
      show u⁻¹ = u ^ (-1 : ℤ) by rw [zpow_neg_one]]
  calc x ^ (2 : ℤ) * u * I * (x ^ (2 * (-(n + 1))) * u ^ (-(n + 1)) *
          (fu * (x ^ (-1 : ℤ) * u ^ (-1 : ℤ))))
      = (x ^ (2 : ℤ) * x ^ (2 * (-(n + 1))) * x ^ (-1 : ℤ)) *
          (u * u ^ (-(n + 1)) * u ^ (-1 : ℤ)) * I * fu := by ring
    _ = x ^ (-(2 * n + 1)) * u ^ (-(n + 1)) * I * fu := by rw [hx3, hu3]
    _ = x ^ (-(2 * n + 1)) * (u * I * (u ^ (-(n + 2)) * fu)) := by rw [← hu2]; ring

theorem circleIntegral_scale_of_functional (x : ℂ) (hx0 : x ≠ 0) {f : ℂ → ℂ}
    (hf : ∀ t : ℂ, t ≠ 0 → f (x ^ 2 * t) = f t / (x * t)) (n : ℤ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∮ t in C(0, ρ), t ^ (-(n + 1)) * f t) =
      x ^ (-(2 * n + 1)) * (∮ u in C(0, ρ / ‖x‖ ^ 2), u ^ (-(n + 2)) * f u) := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set D : ℂ := ((‖x‖ ^ 2 : ℝ) : ℂ) with hD
  -- a real angle `ψ` with `exp (ψ I) = x² / ‖x‖²`
  have hnormz : ‖x ^ 2 / D‖ = 1 := by
    have hDn : ‖D‖ = ‖x‖ ^ 2 := by rw [hD]; simp
    rw [norm_div, norm_pow, hDn, div_self (ne_of_gt (pow_pos hxpos 2))]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ, cexp (↑ψ * I) = x ^ 2 / D := by
    refine ⟨(x ^ 2 / D).arg, ?_⟩
    have h := Complex.norm_mul_exp_arg_mul_I (x ^ 2 / D)
    rw [hnormz] at h
    simpa using h
  set σ : ℝ := ρ / ‖x‖ ^ 2 with hσ
  have hσpos : 0 < σ := by rw [hσ]; positivity
  let F : ℝ → ℂ := fun θ =>
    deriv (circleMap 0 ρ) θ • ((circleMap 0 ρ θ) ^ (-(n + 1)) * f (circleMap 0 ρ θ))
  let G : ℝ → ℂ := fun θ =>
    deriv (circleMap 0 σ) θ • ((circleMap 0 σ θ) ^ (-(n + 2)) * f (circleMap 0 σ θ))
  have hL : (∮ t in C(0, ρ), t ^ (-(n + 1)) * f t) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), F θ := rfl
  have hR : (∮ u in C(0, σ), u ^ (-(n + 2)) * f u) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), G θ := rfl
  -- the integrand of the `ρ`-integral is `2π`-periodic
  have hper : Function.Periodic F (2 * Real.pi) := by
    intro θ
    simp only [F]
    rw [deriv_circleMap, deriv_circleMap, periodic_circleMap 0 ρ θ]
  -- shifting the parameter by `ψ` converts one integrand into the other
  have hshift : ∀ θ, F (θ + ψ) = x ^ (-(2 * n + 1)) * G θ := by
    intro θ
    set u : ℂ := circleMap 0 σ θ with hu_def
    have hu_ne : u ≠ 0 := by
      rw [hu_def, circleMap_zero]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hσpos.ne') (Complex.exp_ne_zero _)
    have hv : circleMap 0 ρ (θ + ψ) = x ^ 2 * u := by
      rw [hu_def, circleMap_zero, circleMap_zero]
      rw [show (↑(θ + ψ) : ℂ) * I = ↑θ * I + ↑ψ * I by push_cast; ring]
      rw [Complex.exp_add, hψ]
      have hσc : (↑σ : ℂ) = ↑ρ / D := by rw [hσ, hD]; push_cast; ring
      rw [hσc]
      ring
    have hft : f (x ^ 2 * u) = f u / (x * u) := hf u hu_ne
    simp only [F, G, deriv_circleMap, smul_eq_mul]
    rw [hv, hft, ← hu_def]
    exact circleIntegral_scale_alg x u (f u) hx0 hu_ne n
  have hstep : (∫ θ in (0 : ℝ)..(2 * Real.pi), F θ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), F (θ + ψ) := by
    rw [intervalIntegral.integral_comp_add_right]
    rw [zero_add, show (2 * Real.pi : ℝ) + ψ = ψ + 2 * Real.pi by ring]
    have h1 := hper.intervalIntegral_add_eq 0 ψ
    simpa using h1
  calc (∮ t in C(0, ρ), t ^ (-(n + 1)) * f t)
      = ∫ θ in (0 : ℝ)..(2 * Real.pi), F θ := hL
    _ = ∫ θ in (0 : ℝ)..(2 * Real.pi), F (θ + ψ) := hstep
    _ = ∫ θ in (0 : ℝ)..(2 * Real.pi), x ^ (-(2 * n + 1)) * G θ := by
          apply intervalIntegral.integral_congr
          intro θ _
          exact hshift θ
    _ = x ^ (-(2 * n + 1)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), G θ := by
          rw [intervalIntegral.integral_const_mul]
    _ = x ^ (-(2 * n + 1)) * (∮ u in C(0, σ), u ^ (-(n + 2)) * f u) := by rw [hR]
    _ = x ^ (-(2 * n + 1)) * (∮ u in C(0, ρ / ‖x‖ ^ 2), u ^ (-(n + 2)) * f u) := by rw [hσ]

end Work.Haupt
