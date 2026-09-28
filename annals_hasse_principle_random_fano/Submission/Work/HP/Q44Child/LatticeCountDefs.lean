import Mathlib

/-!
# Counting lattice points in a ball via the Voronoi cell

This file sets up the geometry-of-numbers input for `Work.HP.Q44Child.lattice_count_le`:

if `L ⊆ E` is a `ℤ`-lattice, `V` is the closed Voronoi cell of the origin
(`voronoiCell L = {x | ∀ u : L, ‖x‖ ≤ ‖x - u‖}`), then

* `V` is closed (`voronoiCell_isClosed`), hence measurable;
* `0 ∈ V`;
* if every point of `E` is within `μ` of a lattice point, then `V ⊆ closedBall 0 μ`.

The Voronoi cell is the fundamental domain used to bound the number of lattice points in
`closedBall 0 T` from above by `volume (ball 0 (T + μ)) / covolume L`: the translates
`u + V` for lattice points `u` of norm `≤ T` are (a.e.) disjoint and all lie in
`closedBall 0 (T + μ)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Metric Set

namespace Work.HP.Q44Child

variable {E : Type*}

/-- The closed Voronoi cell of the origin for the lattice `L`: the set of points that are at
least as close to `0` as to any lattice point. -/
def voronoiCell [NormedAddCommGroup E] (L : Submodule ℤ E) : Set E :=
  {x | ∀ u : L, ‖x‖ ≤ ‖x - (u : E)‖}

@[simp] lemma mem_voronoiCell [NormedAddCommGroup E] {L : Submodule ℤ E} {x : E} :
    x ∈ voronoiCell L ↔ ∀ u : L, ‖x‖ ≤ ‖x - (u : E)‖ := Iff.rfl

lemma zero_mem_voronoiCell [NormedAddCommGroup E] (L : Submodule ℤ E) :
    (0 : E) ∈ voronoiCell L := by
  intro u; simp

lemma voronoiCell_isClosed [NormedAddCommGroup E] (L : Submodule ℤ E) :
    IsClosed (voronoiCell L) := by
  have h : voronoiCell L = ⋂ u : L, {x : E | ‖x‖ ≤ ‖x - (u : E)‖} := by
    ext x; simp [voronoiCell]
  rw [h]
  exact isClosed_iInter fun u => isClosed_le continuous_norm
    ((continuous_id.sub continuous_const).norm)

lemma voronoiCell_subset_closedBall [NormedAddCommGroup E] (L : Submodule ℤ E) {μ : ℝ}
    (hcov : ∀ x : E, ∃ u : L, ‖x - (u : E)‖ ≤ μ) :
    voronoiCell L ⊆ closedBall (0 : E) μ := by
  intro x hx
  obtain ⟨u, hu⟩ := hcov x
  rw [mem_closedBall_zero_iff]
  exact le_trans (hx u) hu

end Work.HP.Q44Child
