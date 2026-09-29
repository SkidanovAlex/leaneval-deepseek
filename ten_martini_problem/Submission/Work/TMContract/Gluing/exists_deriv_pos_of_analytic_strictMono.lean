import Mathlib

namespace Work.TMContract.Gluing

/-- A real-analytic function that is strictly monotone on an open interval `(a,b)` has a
positive derivative at some interior point.

Indeed a strictly increasing (or decreasing) differentiable function has nonnegative
derivative wherever the derivative exists; if the derivative vanished at every interior
point, then the analytic (hence differentiable) function `N` would be constant on the
connected open set `(a,b)`, contradicting strict monotonicity. -/
theorem exists_deriv_pos_of_analytic_strictMono {N : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hN : AnalyticOnNhd ℝ N (Set.Ioo a b)) (hmono : StrictMonoOn N (Set.Ioo a b)) :
    ∃ x₀ ∈ Set.Ioo a b, 0 < deriv N x₀ := by
  by_contra h
  push Not at h
  -- `h : ∀ x, x ∈ Ioo a b → deriv N x ≤ 0`
  have hdiff : DifferentiableOn ℝ N (Set.Ioo a b) := hN.differentiableOn
  -- Monotonicity forces `0 ≤ deriv N x`; with `h` this says the derivative vanishes on `(a,b)`.
  have hzero : Set.EqOn (deriv N) 0 (Set.Ioo a b) := by
    intro x hx
    have hnn : 0 ≤ deriv N x := by
      have h1 : 0 ≤ derivWithin N (Set.Ioo a b) x := (hmono.monotoneOn).derivWithin_nonneg
      rwa [derivWithin_of_isOpen isOpen_Ioo hx] at h1
    exact le_antisymm (h x hx) hnn
  -- Two distinct interior points, at which `N` then takes equal values.
  set x : ℝ := (2 * a + b) / 3 with hxdef
  set y : ℝ := (a + 2 * b) / 3 with hydef
  have hx : x ∈ Set.Ioo a b := by
    refine ⟨?_, ?_⟩ <;> rw [hxdef] <;> linarith
  have hy : y ∈ Set.Ioo a b := by
    refine ⟨?_, ?_⟩ <;> rw [hydef] <;> linarith
  have hxy : x < y := by rw [hxdef, hydef]; linarith
  have hlt : N x < N y := hmono hx hy hxy
  -- Constancy of `N` on the connected open interval contradicts `N x < N y`.
  have heq : N x = N y :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero hx hy
  linarith

end Work.TMContract.Gluing
