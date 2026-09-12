import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Geometry.Convex.Hadwiger

theorem interval_interior_empty_iff {a b : ℝ} (hab : a ≤ b) :
    interior (Set.Icc a b : Set ℝ) = ∅ ↔ a = b := by
  constructor
  · intro h
    by_contra hne
    have hlt : a < b := lt_of_le_of_ne hab hne
    rw [interior_Icc] at h
    exact (Set.nonempty_Ioo.mpr hlt).ne_empty h
  · intro h
    subst b
    simp

end Commons.Geometry.Convex.Hadwiger