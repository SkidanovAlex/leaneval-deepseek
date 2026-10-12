import Mathlib.Analysis.InnerProductSpace.PiL2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BSKinetic.Decomp

/-- A compactly supported real-valued function on `ℝ³` vanishes outside a large
ball: there is a radius `R ≥ 0` beyond which `ψ` is identically zero.

This is the standard consequence of `tsupport ψ` being compact, hence bounded:
if `‖x‖` exceeds every norm attained on `tsupport ψ`, then `x ∉ tsupport ψ`, so
`ψ x = 0` (since `Function.support ψ ⊆ tsupport ψ`). -/
theorem exists_radius_eq_zero_of_hasCompactSupport {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hcs : HasCompactSupport ψ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ → ψ x = 0 := by
  obtain ⟨C, hC⟩ := (hcs.isCompact.isBounded).exists_norm_le
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro x hx
  by_contra hne
  have hxsupp : x ∈ Function.support ψ := by
    simpa [Function.mem_support] using hne
  have hle : ‖x‖ ≤ C := hC x (subset_tsupport ψ hxsupp)
  have hlt : max C 0 < ‖x‖ := by linarith
  have : C < ‖x‖ := lt_of_le_of_lt (le_max_left C 0) hlt
  linarith

end Work.BSKinetic.Decomp
