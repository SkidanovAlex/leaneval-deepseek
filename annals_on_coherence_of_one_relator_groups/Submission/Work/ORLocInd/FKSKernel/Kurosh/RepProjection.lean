import Mathlib
import Submission.Work.ORLocInd.FKSKernel.Kurosh.TreeDatum

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORLocInd.FKSKernel.Kurosh

open Work.ORBassSerre

/-!
# The nearest representative of a vertex orbit

Let `G` act on a tree `V` and let `d : TreeDatum G V` be the spanning tree datum of the action:
`d.vert A` is a chosen representative of the vertex orbit `A`, and the arrows `d.parArrow A`
join the representatives of `A` and of its parent orbit.

This file sets up the *projection* onto the set of chosen representatives: `nearestRep hT d v`
is the representative closest to `v`.  It is the technical tool for the "ping-pong" proof that
the vertex stabilisers of the representatives generate a free product: the sets
`{v | nearestRep hT d v = d.vert A}` are disjoint nonempty `vgroup A`-traps.

The mathematical content is developed in the companion files; here only the definitions and
their elementary unfolding lemmas are recorded.
-/

universe u

variable {G : Type u} {V : Type u} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-- The set of chosen representatives of the vertex orbits. -/
def repSet (d : TreeDatum G V) : Set V := Set.range d.vert

theorem mem_repSet {d : TreeDatum G V} {v : V} : v ∈ repSet d ↔ ∃ A, d.vert A = v := Iff.rfl

theorem vert_mem_repSet (d : TreeDatum G V) (A : Work.ORBassSerre.orbitV G V) :
    d.vert A ∈ repSet d := ⟨A, rfl⟩

/-- The distance in a tree: the length of the (unique) reduced path between two vertices. -/
noncomputable def dist (hT : Work.ORBassSerre.IsTree V) (u w : V) : ℕ :=
  (hT.geodesic u w).length

theorem dist_self (hT : Work.ORBassSerre.IsTree V) (u : V) : dist hT u u = 0 := by
  rw [dist, hT.geodesic_self]
  rfl

theorem dist_eq_zero_iff (hT : Work.ORBassSerre.IsTree V) {u w : V} :
    dist hT u w = 0 ↔ u = w := by
  constructor
  · intro h
    exact Quiver.Path.eq_of_length_zero (hT.geodesic u w) h
  · rintro rfl
    exact dist_self hT u

/-- **The nearest representative exists.**  For every vertex there is a representative of a
vertex orbit whose distance to the vertex is minimal. -/
theorem exists_nearestRep (hT : Work.ORBassSerre.IsTree V) (d : TreeDatum G V) (v : V) :
    ∃ r : V, r ∈ repSet d ∧ ∀ s ∈ repSet d, dist hT v r ≤ dist hT v s := by
  classical
  have hne : ∃ n : ℕ, ∃ A : Work.ORBassSerre.orbitV G V, dist hT v (d.vert A) = n :=
    ⟨dist hT v (d.vert d.root), d.root, rfl⟩
  obtain ⟨A, hA⟩ := Nat.find_spec hne
  refine ⟨d.vert A, vert_mem_repSet d A, ?_⟩
  rintro s ⟨B, rfl⟩
  by_contra hcon
  rw [not_le] at hcon
  rw [hA] at hcon
  exact Nat.find_min hne hcon ⟨B, rfl⟩

/-- **The nearest representative of a vertex**: the chosen representative closest to `v`. -/
noncomputable def nearestRep (hT : Work.ORBassSerre.IsTree V) (d : TreeDatum G V)
    (v : V) : V :=
  Classical.choose (exists_nearestRep hT d v)

theorem nearestRep_mem (hT : Work.ORBassSerre.IsTree V) (d : TreeDatum G V) (v : V) :
    nearestRep hT d v ∈ repSet d :=
  (Classical.choose_spec (exists_nearestRep hT d v)).1

theorem nearestRep_le (hT : Work.ORBassSerre.IsTree V) (d : TreeDatum G V) (v : V)
    (A : Work.ORBassSerre.orbitV G V) :
    dist hT v (nearestRep hT d v) ≤ dist hT v (d.vert A) :=
  (Classical.choose_spec (exists_nearestRep hT d v)).2 (d.vert A) (vert_mem_repSet d A)

end Work.ORLocInd.FKSKernel.Kurosh
