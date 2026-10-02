import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The boundary of a cube is dense when the index type is infinite

Mathlib defines the boundary of the cube `I^N = N → I` as
`Cube.boundary N = {y | ∃ i, y i = 0 ∨ y i = 1}`.

When `N` is finite this set is closed and proper, hence not dense.  When `N` is
infinite the situation is the opposite: any basic open set of the product
topology only constrains finitely many coordinates, so one can move a coordinate
outside the constrained finite set to `0` and land in the boundary.  Hence
`Cube.boundary N` is dense in `I^N`.
-/

namespace Work.Stems

/-- For an infinite index type `N`, the boundary of the cube `I^N` is dense. -/
theorem dense_boundary {N : Type*} [Infinite N] : Dense (Cube.boundary N) := by
  classical
  rw [dense_iff_inter_open]
  intro U hU ⟨x, hx⟩
  -- Decompose `U` via the product basis: it contains a finitely supported `pi`-box around `x`.
  obtain ⟨I0, u, hu, hsub⟩ := (isOpen_pi_iff.mp hU) x hx
  -- Pick a coordinate outside the (finite) support of the box.
  obtain ⟨i, hi⟩ := I0.exists_notMem
  -- Move that coordinate to `0`; the resulting point stays in `U` and lies on the boundary.
  refine ⟨Function.update x i 0, ?_, ?_⟩
  · apply hsub
    rw [Set.mem_pi]
    intro a ha
    have hne : a ≠ i := fun h => hi (h ▸ ha)
    rw [Function.update_of_ne hne]
    exact (hu a ha).2
  · exact ⟨i, Or.inl (Function.update_self i 0 x)⟩

end Work.Stems
