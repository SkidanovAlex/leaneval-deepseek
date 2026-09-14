import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Topology.Metric

/-- A smooth compactly supported function on `ℝ` is bounded. -/
theorem exists_norm_le_of_contDiff_hasCompactSupport {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    {ξ : ℝ → F} (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ) (hc : HasCompactSupport ξ) :
    ∃ M : ℝ, ∀ t : ℝ, ‖ξ t‖ ≤ M :=
  hc.exists_bound_of_continuous h.continuous

end Commons.Topology.Metric