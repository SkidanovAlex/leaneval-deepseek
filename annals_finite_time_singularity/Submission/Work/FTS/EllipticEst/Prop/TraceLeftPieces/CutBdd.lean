import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Prop.TraceLeftPieces.ChiCutDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Boundedness of the first two derivatives of a smoothed step

If `χ` is `C²` and is constantly `1` on `(-∞, a]` and constantly `0` on `[b, ∞)` with `a < b`,
then `χ` is constant off the compact interval `[a,b]`, so `deriv χ` and `deriv (deriv χ)` both
vanish off `[a,b]`; continuity on the compact interval then gives a common bound `K ≥ 1`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.EllipticEst.Prop.TraceLeftPieces

/-- A `C²` plateau function has bounded first and second derivatives. -/
theorem deriv_bdd_of_plateau (χ : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hcont : ContDiff ℝ 2 χ) (h1 : ∀ θ : ℝ, θ ≤ a → χ θ = 1)
    (h0 : ∀ θ : ℝ, b ≤ θ → χ θ = 0) :
    ∃ K : ℝ, 1 ≤ K ∧ (∀ θ : ℝ, |deriv χ θ| ≤ K) ∧ (∀ θ : ℝ, |deriv (deriv χ) θ| ≤ K) := by
  have hcd : Continuous (deriv χ) := hcont.continuous_deriv (by norm_num)
  have h1' : ContDiff ℝ 1 (deriv χ) := hcont.deriv' (n := 1)
  have hcd2 : Continuous (deriv (deriv χ)) := h1'.continuous_deriv_one
  have hz1 : ∀ y : ℝ, y < a → deriv χ y = 0 := by
    intro y hy
    have hloc : χ =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds hy] with z hz
      exact h1 z (le_of_lt hz)
    exact ((hasDerivAt_const y (1 : ℝ)).congr_of_eventuallyEq hloc).deriv
  have hz2 : ∀ y : ℝ, b < y → deriv χ y = 0 := by
    intro y hy
    have hloc : χ =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
      exact h0 z (le_of_lt hz)
    exact ((hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hloc).deriv
  have hz3 : ∀ y : ℝ, y < a → deriv (deriv χ) y = 0 := by
    intro y hy
    have hloc : deriv χ =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds hy] with z hz
      exact hz1 z hz
    rw [hloc.deriv_eq, deriv_const]
  have hz4 : ∀ y : ℝ, b < y → deriv (deriv χ) y = 0 := by
    intro y hy
    have hloc : deriv χ =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
      exact hz2 z hz
    rw [hloc.deriv_eq, deriv_const]
  obtain ⟨K₁, hK₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcd.continuousOn.mono (Set.subset_univ _) : ContinuousOn (deriv χ) (Set.Icc a b))
  obtain ⟨K₂, hK₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcd2.continuousOn.mono (Set.subset_univ _) : ContinuousOn (deriv (deriv χ)) (Set.Icc a b))
  refine ⟨max 1 (max K₁ K₂), le_max_left _ _, ?_, ?_⟩
  · intro θ
    by_cases h : θ ∈ Set.Icc a b
    · have h1' := hK₁ θ h
      rw [Real.norm_eq_abs] at h1'
      exact h1'.trans (le_trans (le_max_left K₁ K₂) (le_max_right 1 (max K₁ K₂)))
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
      have hθ : deriv χ θ = 0 := by
        rcases h with h | h
        · exact hz1 θ h
        · exact hz2 θ h
      rw [hθ]
      simpa using le_trans (by norm_num : |(0 : ℝ)| ≤ 1) (le_max_left (1 : ℝ) (max K₁ K₂))
  · intro θ
    by_cases h : θ ∈ Set.Icc a b
    · have h2' := hK₂ θ h
      rw [Real.norm_eq_abs] at h2'
      exact h2'.trans (le_trans (le_max_right K₁ K₂) (le_max_right 1 (max K₁ K₂)))
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
      have hθ : deriv (deriv χ) θ = 0 := by
        rcases h with h | h
        · exact hz3 θ h
        · exact hz4 θ h
      rw [hθ]
      simpa using le_trans (by norm_num : |(0 : ℝ)| ≤ 1) (le_max_left (1 : ℝ) (max K₁ K₂))

end Work.FTS.EllipticEst.Prop.TraceLeftPieces
