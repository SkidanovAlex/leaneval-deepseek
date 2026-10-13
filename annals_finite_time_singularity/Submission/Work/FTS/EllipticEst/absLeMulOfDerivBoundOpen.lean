import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open Set

/-- Lagrange mean-value bound on an interval: if `u` is continuous on `[a, b]`, differentiable
on `(a, b)` and `|u'| ≤ M` on `(a, b)`, then `|u b - u a| ≤ (b - a) · M`.  No sign hypothesis on
`M` is needed: when `a = b` both sides vanish, and when `a < b` the mean value theorem gives a
point `c` with `u b - u a = (b - a) · u' c`, so the bound follows from `b - a > 0`. -/
private lemma abs_sub_le_mul_of_deriv_bound {u : ℝ → ℝ} {M a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn u (Set.Icc a b)) (hdiff : DifferentiableOn ℝ u (Set.Ioo a b))
    (hbd : ∀ x ∈ Set.Ioo a b, |deriv u x| ≤ M) :
    |u b - u a| ≤ (b - a) * M := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · -- Lagrange mean value theorem on `[a, b]`.
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope u hlt hcont hdiff
    have hcb : 0 < b - a := sub_pos.mpr hlt
    have h2 : u b - u a = (b - a) * deriv u c := by rw [hcd]; field_simp
    rw [h2, abs_mul, abs_of_pos hcb]
    exact mul_le_mul_of_nonneg_left (hbd c hc) (le_of_lt hcb)
  · -- Degenerate interval: `a = b`.
    rw [heq]; simp

/-- Two mean-value bounds for a Dirichlet slice: if `u` is differentiable on the open interval
`(0, π/2)`, continuous on `[0, π/2]`, vanishes at both endpoints, and `|u'| ≤ M` on `(0, π/2)`,
then `|u θ| ≤ θ·M` and `|u θ| ≤ (π/2 - θ)·M` for every `θ ∈ [0, π/2]`.  Declaration to be placed
in namespace `Work.FTS.EllipticEst` (module
`Submission.Work.FTS.EllipticEst.absLeMulOfDerivBoundOpen`).

Route: `exists_deriv_eq_slope` on `[0, θ]` (resp. `[θ, π/2]`) for `0 < θ < π/2` gives
`ξ` with `deriv u ξ = (u θ - u 0)/θ` (resp. `= (u (π/2) - u θ)/(π/2 - θ)`); combine with
`h0`, `h1`, `hbd`.  Note `0 ≤ M` follows from `hbd` at any interior point.  The endpoints
`θ = 0, π/2` are immediate from `h0`, `h1`. -/
theorem absLeMulOfDerivBoundOpen {u : ℝ → ℝ} {M : ℝ}
    (hdiff : DifferentiableOn ℝ u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2))) (h0 : u 0 = 0) (h1 : u (Real.pi / 2) = 0)
    (hbd : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), |deriv u x| ≤ M) :
    (∀ θ ∈ Set.Icc 0 (Real.pi / 2), |u θ| ≤ θ * M) ∧
      (∀ θ ∈ Set.Icc 0 (Real.pi / 2), |u θ| ≤ (Real.pi / 2 - θ) * M) := by
  constructor
  · -- The left half of the interval: apply the mean-value bound on `[0, θ]`.
    intro θ hθ
    have key := abs_sub_le_mul_of_deriv_bound (u := u) (M := M) hθ.1
      (hcont.mono (Set.Icc_subset_Icc le_rfl hθ.2))
      (hdiff.mono (Set.Ioo_subset_Ioo le_rfl hθ.2))
      (fun x hx => hbd x (Set.Ioo_subset_Ioo le_rfl hθ.2 hx))
    rw [h0, sub_zero] at key
    simpa using key
  · -- The right half of the interval: apply the mean-value bound on `[θ, π/2]`.
    intro θ hθ
    have key := abs_sub_le_mul_of_deriv_bound (u := u) (M := M) hθ.2
      (hcont.mono (Set.Icc_subset_Icc hθ.1 le_rfl))
      (hdiff.mono (Set.Ioo_subset_Ioo hθ.1 le_rfl))
      (fun x hx => hbd x (Set.Ioo_subset_Ioo hθ.1 le_rfl hx))
    rw [h1, zero_sub, abs_neg] at key
    exact key

end Work.FTS.EllipticEst
