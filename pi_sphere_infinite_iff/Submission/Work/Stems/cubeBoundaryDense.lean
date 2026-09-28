import Mathlib

/-!
# The boundary of the cube is dense for an infinite index type

Mathlib's generalised loops `Ω^N X x` (`GenLoop N X x`) are the continuous maps `N → I → X` which
send the "boundary" `Cube.boundary N = {y | ∃ i, y i = 0 ∨ y i = 1}` to `x`, and `HomotopyGroup N X x`
quotients them by homotopy relative to that boundary.

This file records the elementary but crucial observation that for an **infinite** index type `N`
the boundary is **dense** in the product `N → I`: in the product topology every basic open set
constrains only finitely many coordinates, so a coordinate outside that finite set can always be
put equal to `0`.

This is the reason why the naive "collar" construction of the basepoint-change map (which needs a
closed core with non-empty interior inside the cube) is impossible for infinite `N`, and why the
basepoint change nevertheless behaves trivially there.
-/

open Set Function
open scoped Topology unitInterval

namespace Work.Stems

/-- For an infinite index type `N`, the boundary `Cube.boundary N` of the cube `N → I` is dense. -/
theorem dense_cubeBoundary_of_infinite (N : Type*) [Infinite N] :
    Dense (Cube.boundary N : Set (N → I)) := by
  classical
  rw [dense_iff_inter_open]
  rintro U hU ⟨f, hfU⟩
  obtain ⟨s, u, hu, hsub⟩ := isOpen_pi_iff.mp hU f hfU
  obtain ⟨j, hj⟩ := Finset.exists_notMem s
  refine ⟨Function.update f j 0, hsub ?_, ⟨j, by simp⟩⟩
  rw [Set.mem_pi]
  intro a ha
  have haj : a ≠ j := by rintro rfl; exact hj ha
  rw [Function.update_of_ne haj]
  exact (hu a ha).2

end Work.Stems
