import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.Reconstruct

/-- In a compact Hausdorff topological group, the kernel of a homomorphism with
infinite range cannot be open: an open subgroup of a compact group has finite
index, so the quotient — hence the range — is finite. -/
theorem not_isOpen_ker_of_infinite_range {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] {C : Type*} [Group C] (φ : G →* C)
    (h : ¬ Finite φ.range) : ¬ IsOpen ((φ.ker : Subgroup G) : Set G) := by
  intro hopen
  -- An open subgroup has discrete quotient.
  letI : DiscreteTopology (G ⧸ φ.ker) := QuotientGroup.discreteTopology hopen
  -- The quotient of a compact group is compact, hence (discrete + compact) finite.
  have hfin : Finite (G ⧸ φ.ker) := finite_of_compact_of_discrete
  -- The first isomorphism theorem transports finiteness to the range.
  exact h ((QuotientGroup.quotientKerEquivRange φ).finite_iff.mp hfin)

end NK.Reconstruct
