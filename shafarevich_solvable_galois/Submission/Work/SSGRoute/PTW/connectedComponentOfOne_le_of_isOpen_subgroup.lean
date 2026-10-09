import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The identity component lies in every open subgroup

An open subgroup of a topological group is clopen (its complement is a union of translates of it),
and a clopen set containing `1` contains the connected component of `1`.  Consequently every open
subgroup of `C_K` contains the identity component `C_K^0`; this is the reduction step that lets the
`p`-power criterion in the idèle class group be tested only modulo `C_K^0`.
-/

set_option autoImplicit false

namespace Work.SSGRoute.PTW

/-- **The identity component is contained in every open subgroup.** -/
theorem connectedComponentOfOne_le_of_isOpen_subgroup
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Subgroup G) (hV : IsOpen (V : Set G)) :
    Subgroup.connectedComponentOfOne G ≤ V :=
  fun _ hx => (IsClopen.connectedComponent_subset ⟨Subgroup.isClosed_of_isOpen V hV, hV⟩
    V.one_mem) hx

end Work.SSGRoute.PTW
