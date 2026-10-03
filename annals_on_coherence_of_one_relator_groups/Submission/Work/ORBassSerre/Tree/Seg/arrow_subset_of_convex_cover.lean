import Mathlib
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORBassSerre.Tree.Seg.geodesic_edge_dichotomy

namespace Work.ORBassSerre.Tree.Seg

open Quiver

/-- For a path `p : Path a b` and an arrow `e : b ⟶ c`, the vertex `b` occurs in the vertex list
of the path `p.comp e.toPath`. -/
theorem mem_vertices_comp_toPath {V : Type*} [Quiver V] {a b c : V}
    (p : Quiver.Path a b) (e : b ⟶ c) : b ∈ (p.comp e.toPath).vertices := by
  rw [Quiver.Path.comp_toPath_eq_cons, Quiver.Path.mem_vertices_cons]
  exact Or.inl (Quiver.Path.end_mem_vertices p)

/-- In a tree, if `f : a ⟶ b` is an arrow and `z` is any vertex, then `a` lies on the geodesic
from `z` to `b`, or `b` lies on the geodesic from `z` to `a`. -/
theorem adjacent_mem_reducedSpan {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hT : Work.ORBassSerre.IsTree V} {a b z : V} (f : a ⟶ b) :
    a ∈ Work.ORBassSerre.reducedSpan z b ∨ b ∈ Work.ORBassSerre.reducedSpan z a := by
  rcases geodesic_edge_dichotomy (hT := hT) (z := z) f with h | ⟨g, hg⟩
  · left
    rw [hT.reducedSpan_eq, h]
    exact mem_vertices_comp_toPath (hT.geodesic z a) f
  · right
    rw [hT.reducedSpan_eq, hg]
    exact mem_vertices_comp_toPath (hT.geodesic z b) g

/-- In a tree, if two convex sets `Q₁`, `Q₂` meet in a vertex `z`, an arrow `f : a ⟶ b` with
`a ∈ Q₁` and `b ∈ Q₂` forces `a ∈ Q₂` or `b ∈ Q₁`. -/
theorem mixed_case {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hT : Work.ORBassSerre.IsTree V} {Q₁ Q₂ : Set V}
    (h₁ : Work.ORBassSerre.IsConvexSet Q₁) (h₂ : Work.ORBassSerre.IsConvexSet Q₂)
    {z a b : V} (hz₁ : z ∈ Q₁) (hz₂ : z ∈ Q₂) (f : a ⟶ b)
    (ha₁ : a ∈ Q₁) (hb₂ : b ∈ Q₂) : a ∈ Q₂ ∨ b ∈ Q₁ := by
  rcases adjacent_mem_reducedSpan (hT := hT) (z := z) f with h | h
  · exact Or.inl (h₂.reducedSpan_subset hz₂ hb₂ h)
  · exact Or.inr (h₁.reducedSpan_subset hz₁ ha₁ h)

/-- In a tree, if an arrow joins two vertices of the union of two convex sets `Q₁`, `Q₂` which
meet in a common vertex `z`, then both endpoints of the arrow lie in `Q₁` or both lie in `Q₂`. -/
theorem arrow_subset_of_convex_cover {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hT : Work.ORBassSerre.IsTree V} {Q₁ Q₂ : Set V}
    (h₁ : Work.ORBassSerre.IsConvexSet Q₁) (h₂ : Work.ORBassSerre.IsConvexSet Q₂)
    {z a b : V} (hz₁ : z ∈ Q₁) (hz₂ : z ∈ Q₂) (f : a ⟶ b)
    (ha : a ∈ Q₁ ∪ Q₂) (hb : b ∈ Q₁ ∪ Q₂) :
    (a ∈ Q₁ ∧ b ∈ Q₁) ∨ (a ∈ Q₂ ∧ b ∈ Q₂) := by
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exact Or.inl ⟨ha, hb⟩
    · rcases mixed_case (hT := hT) h₁ h₂ hz₁ hz₂ f ha hb with h | h
      · exact Or.inr ⟨h, hb⟩
      · exact Or.inl ⟨ha, h⟩
  · rcases hb with hb | hb
    · rcases mixed_case (hT := hT) h₂ h₁ hz₂ hz₁ f ha hb with h | h
      · exact Or.inl ⟨h, hb⟩
      · exact Or.inr ⟨ha, h⟩
    · exact Or.inr ⟨ha, hb⟩

end Work.ORBassSerre.Tree.Seg
