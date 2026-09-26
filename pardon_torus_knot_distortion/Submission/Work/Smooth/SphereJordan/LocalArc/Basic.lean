import Mathlib

/-!
# Charts for spaces that are locally an arc

A space is *locally an arc* if every point `x` has an open neighbourhood `V` homeomorphic to
`ℝ` (with `0 ↔ x`).  A compact, connected, non-trivial locally-arc space is a simple closed
curve; this file sets up the vocabulary (an `ArcChart` at a point, and the predicate
`IsLocallyArc`) together with the elementary lemmas about charts that the classification proof
uses.
-/

namespace Work.Smooth.SphereJordan

open Set Function

noncomputable section

/-- An **arc chart** at a point `x` of a topological space: an open neighbourhood `V` of `x`
together with a homeomorphism `ℝ ≃ₜ V` sending `0` to `x`. -/
structure ArcChart (X : Type*) [TopologicalSpace X] (x : X) where
  /-- the chart neighbourhood -/
  V : Set X
  /-- the chart neighbourhood is open -/
  isOpen_V : IsOpen V
  /-- the chart neighbourhood contains the base point -/
  mem_V : x ∈ V
  /-- the chart homeomorphism -/
  homeo : ℝ ≃ₜ V
  /-- the chart sends `0` to the base point -/
  homeo_zero : homeo 0 = ⟨x, mem_V⟩

namespace ArcChart

variable {X : Type*} [TopologicalSpace X] {x : X} (c : ArcChart X x)

/-- The chart map, as a map to the ambient space. -/
def map : ℝ → X := fun t => (c.homeo t : X)

@[simp] lemma map_apply (t : ℝ) : c.map t = (c.homeo t : X) := rfl

lemma continuous_map : Continuous c.map :=
  continuous_subtype_val.comp c.homeo.continuous

lemma range_map : Set.range c.map = c.V := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact (c.homeo t).2
  · intro hy
    exact ⟨c.homeo.symm ⟨y, hy⟩, by simp [map]⟩

lemma injective_map : Function.Injective c.map := by
  intro s t hst
  exact c.homeo.injective (Subtype.ext hst)

lemma map_zero : c.map 0 = x := by simp [map, c.homeo_zero]

lemma map_mem (t : ℝ) : c.map t ∈ c.V := (c.homeo t).2

/-- The coordinate of a point of the chart neighbourhood. -/
def coord (y : c.V) : ℝ := c.homeo.symm y

lemma coord_apply_map (t : ℝ) : c.coord ⟨c.map t, c.map_mem t⟩ = t := by
  simp [coord, map]

lemma continuous_coord : Continuous c.coord := c.homeo.symm.continuous

lemma map_coord (y : c.V) : c.map (c.coord y) = (y : X) := by
  simp [coord, map]

lemma injective_coord : Function.Injective c.coord := c.homeo.symm.injective

end ArcChart

/-- A space is **locally an arc** if every point has an arc chart. -/
def IsLocallyArc (X : Type*) [TopologicalSpace X] : Prop := ∀ x : X, Nonempty (ArcChart X x)

/-- A chosen arc chart at a point. -/
noncomputable def chartOf {X : Type*} [TopologicalSpace X] (H : IsLocallyArc X) (x : X) :
    ArcChart X x := Classical.choice (H x)

end

end Work.Smooth.SphereJordan
