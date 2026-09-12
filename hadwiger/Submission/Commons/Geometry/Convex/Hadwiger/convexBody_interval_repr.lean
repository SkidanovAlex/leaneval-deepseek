import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Geometry.Convex.Hadwiger

open Set

/-- A convex body in the real line is exactly a closed interval `[a, b]`. -/
theorem convexBody_interval_repr (K : ConvexBody ℝ) :
    ∃ a b : ℝ, a ≤ b ∧ (K : Set ℝ) = Set.Icc a b := by
  refine ⟨sInf (K : Set ℝ), sSup (K : Set ℝ), ?_, ?_⟩
  · obtain ⟨x, hx⟩ : (K : Set ℝ).Nonempty := K.nonempty
    exact
      le_trans (csInf_le K.isCompact.bddBelow hx) (le_csSup K.isCompact.bddAbove hx)
  · exact eq_Icc_of_connected_compact (K.convex.isConnected K.nonempty) K.isCompact

end Commons.Geometry.Convex.Hadwiger