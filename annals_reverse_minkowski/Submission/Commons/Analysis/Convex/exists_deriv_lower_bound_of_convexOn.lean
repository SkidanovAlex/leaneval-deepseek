import Mathlib

namespace Commons.Analysis.Convex

open MeasureTheory Set Filter
open scoped Real Topology

/-- For a convex differentiable coercive potential `V` with `V → +∞` at `+∞`, the derivative
`V'` is bounded below by a positive constant on a half-line. -/
theorem exists_deriv_lower_bound_of_convexOn (V : ℝ → ℝ) (hV : ConvexOn ℝ Set.univ V)
    (hVd : ∀ x, DifferentiableAt ℝ V x) (htop : Filter.Tendsto V Filter.atTop Filter.atTop) :
    ∃ x₁ c : ℝ, 0 < c ∧ ∀ x, x₁ ≤ x → c ≤ deriv V x := by
  by_contra h
  have hneg : ∀ x₁ c : ℝ, 0 < c → ∃ x, x₁ ≤ x ∧ deriv V x < c := by
    intro x₁ c hc
    by_contra hcon
    push Not at hcon
    exact h ⟨x₁, c, hc, hcon⟩
  have hmono : Monotone (deriv V) := fun x y hxy =>
    hV.monotoneOn_deriv (fun x _ => hVd x) (mem_univ x) (mem_univ y) hxy
  have hle : ∀ x, deriv V x ≤ 0 := by
    intro x
    by_contra hx
    rw [not_le] at hx
    obtain ⟨y, hxy, hy⟩ := hneg x (deriv V x) hx
    have := hmono hxy
    linarith
  have hanti : Antitone V := antitone_of_deriv_nonpos hVd hle
  obtain ⟨a, ha⟩ := (tendsto_atTop_atTop.mp htop) (V 0 + 1)
  have h1 : V 0 + 1 ≤ V (max a 0) := ha (max a 0) (le_max_left a 0)
  have h2 : V (max a 0) ≤ V 0 := hanti (le_max_right a 0)
  linarith

end Commons.Analysis.Convex
