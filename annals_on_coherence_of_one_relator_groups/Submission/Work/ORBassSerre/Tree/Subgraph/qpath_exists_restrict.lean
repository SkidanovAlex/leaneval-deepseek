import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic

namespace Work.ORBassSerre.Tree.Subgraph

open Quiver

/-- A path all of whose vertices lie in a set `S` is the image of a path in the induced subgraph
on `S`. -/
theorem qpath_exists_restrict {V : Type*} [Quiver V] {S : Set V} {a b : V} (ha : a ∈ S)
    (hb : b ∈ S) (p : Quiver.Path a b) (hp : ∀ v ∈ p.vertices, v ∈ S) :
    ∃ p' : Quiver.Path (⟨a, ha⟩ : S) ⟨b, hb⟩,
      (Work.ORBassSerre.subtypePrefunctor S).mapPath p' = p := by
  induction p with
  | nil => exact ⟨Quiver.Path.nil, rfl⟩
  | cons q e ih =>
    -- `q : Path a b✝`, `e : b✝ ⟶ c✝`; the source `b✝` of `e` is a vertex of `q`, hence in `S`.
    have hbq : _ ∈ S :=
      hp _ (Quiver.Path.mem_vertices_cons q e |>.mpr (Or.inl (Quiver.Path.end_mem_vertices q)))
    have hq : ∀ v ∈ q.vertices, v ∈ S :=
      fun v hv => hp v (Quiver.Path.mem_vertices_cons q e |>.mpr (Or.inl hv))
    obtain ⟨q', hq'⟩ := ih hbq hq
    exact ⟨q'.cons e, by rw [Prefunctor.mapPath_cons, hq']; rfl⟩

end Work.ORBassSerre.Tree.Subgraph
