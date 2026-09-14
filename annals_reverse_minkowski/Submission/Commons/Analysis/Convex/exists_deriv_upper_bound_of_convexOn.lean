import Mathlib

namespace Commons.Analysis.Convex

open MeasureTheory Set Filter
open scoped Real Topology

/-- For a convex differentiable potential `V` with `V → +∞` at `-∞`, the derivative `V'` is
bounded above by a negative constant on a half-line `(-∞, x₁]`. -/
theorem exists_deriv_upper_bound_of_convexOn (V : ℝ → ℝ) (hV : ConvexOn ℝ Set.univ V)
    (hVd : ∀ x, DifferentiableAt ℝ V x) (hbot : Filter.Tendsto V Filter.atBot Filter.atTop) :
    ∃ x₁ c : ℝ, 0 < c ∧ ∀ x, x ≤ x₁ → deriv V x ≤ -c := by
  by_contra h
  have hneg : ∀ x₁ c : ℝ, 0 < c → ∃ x, x ≤ x₁ ∧ -c < deriv V x := by
    intro x₁ c hc
    by_contra hcon
    push Not at hcon
    exact h ⟨x₁, c, hc, hcon⟩
  have hmono : Monotone (deriv V) := fun x y hxy =>
    hV.monotoneOn_deriv (fun x _ => hVd x) (mem_univ x) (mem_univ y) hxy
  have hge : ∀ x, 0 ≤ deriv V x := by
    intro x
    by_contra hx
    rw [not_le] at hx
    obtain ⟨y, hxy, hy⟩ := hneg x (-deriv V x) (by linarith)
    have := hmono hxy
    linarith
  have hmonoV : Monotone V := monotone_of_deriv_nonneg hVd hge
  obtain ⟨a, ha⟩ := (tendsto_atBot_atTop.mp hbot) (V 0 + 1)
  have h1 : V 0 + 1 ≤ V (min a 0) := ha (min a 0) (min_le_left a 0)
  have h2 : V (min a 0) ≤ V 0 := hmonoV (min_le_right a 0)
  linarith

end Commons.Analysis.Convex
