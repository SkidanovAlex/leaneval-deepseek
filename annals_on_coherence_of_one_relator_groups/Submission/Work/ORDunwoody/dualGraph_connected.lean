/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The dual graph of Dunwoody's pattern is connected

`Dunwoody/TrackWall.lean` defines the dual graph `dualGraph` on the regions of the pattern: two
regions are adjacent when a track is incident with the pair (`Track.regPair = s(R, R')`).

Here we prove the *connectedness* half of Dunwoody's theorem that the dual graph is a tree.

The argument is elementary and uses only the connectivity of the 1-skeleton `Λ''`
(`Work.ORDunwoody.graph_reachable`) together with the defining property of a track being incident
with the two regions on either side of its cells:

* For every cell `e`, the pattern point `e.mid` lies on a track `trackOf e.mid` whose `regPair` is
  `s(Region.mk e.src, Region.mk e.tgt)`.  Hence *the two old vertices at the ends of a cell have
  either the same region or adjacent regions in the dual graph* (`dualGraph_adj_or_eq_projRegion`).
* The projection `projRegion` of the vertices of `Λ''` to the regions — a pattern point going to the
  region on the source side of its cell — therefore carries every edge of the 1-skeleton to an edge
  of the dual graph or to an equality of regions.  A walk in the 1-skeleton maps to a dual walk
  (`projRegion_reachable`).
* Since `Λ''` is connected, any two old vertices are joined by a walk, so their regions are joined
  in the dual graph; as every region has an old vertex as representative, the dual graph is
  preconnected, and it is nonempty.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.TrackWall
import Submission.Work.ORDunwoody.graph_reachable

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Cayley

namespace Dunwoody

open scoped Sym2

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-! ## The projection of `Λ''` to the regions of the pattern -/

/-- The projection of the vertices of `Λ''` to the regions of the pattern: an old vertex goes to
its region, and a pattern point goes to the region on the *source* side of its cell. -/
def projRegion (D : GeoData T t₀ P) : Vertex D → Region D
  | Sum.inl u => Region.mk D u
  | Sum.inr m => Region.mk D m.src

@[simp] theorem projRegion_inl (u : BaseV D) :
    projRegion D (Sum.inl u : Vertex D) = Region.mk D u := rfl

@[simp] theorem projRegion_inr (m : MidV D) :
    projRegion D (Sum.inr m : Vertex D) = Region.mk D m.src := rfl

/-! ## Every edge of the 1-skeleton maps to a dual edge or an equality -/

/-- The two ends of a cell have the same region or adjacent regions in the dual graph: the track
of the cell's pattern point is incident with exactly the pair of the two regions. -/
theorem dualGraph_adj_or_eq_projRegion_of_stepRel {v w : Vertex D} (h : StepRel v w) :
    (dualGraph D).Adj (projRegion D v) (projRegion D w) ∨ projRegion D v = projRegion D w := by
  rcases h with ⟨e, h1 | h1⟩ | ⟨a, j, hL, h1, h2⟩
  · -- the source end of a cell and its pattern point lie on the same side
    right
    rw [h1.1, h1.2]
    rfl
  · -- the pattern point of a cell and its target end: the track of the pattern point is incident
    -- with the pair of the two regions
    rw [h1.1, h1.2]
    by_cases hc : Region.mk D e.src = Region.mk D e.tgt
    · exact Or.inr hc
    · refine Or.inl ?_
      rw [dualGraph_adj_iff]
      exact ⟨hc, trackOf e.mid, rfl⟩
  · -- a collapsed generator edge joins two old vertices in the same region
    right
    rw [h1, h2]
    exact Region.mk_eq_mk (D := D) (Or.inl ⟨a, j, hL, Or.inl ⟨rfl, rfl⟩⟩)

/-- The same, for an arbitrary edge of the 1-skeleton. -/
theorem dualGraph_adj_or_eq_projRegion {v w : Vertex D} (h : (graph (D := D)).Adj v w) :
    (dualGraph D).Adj (projRegion D v) (projRegion D w) ∨ projRegion D v = projRegion D w := by
  obtain ⟨_, hstep⟩ := (graph_adj_iff (D := D)).1 h
  rcases hstep with hstep | hstep
  · exact dualGraph_adj_or_eq_projRegion_of_stepRel hstep
  · rcases dualGraph_adj_or_eq_projRegion_of_stepRel hstep with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr h'.symm

/-! ## Reachability transfers from `Λ''` to the dual graph -/

/-- A map of vertex types that carries every edge to an edge or to an equality of images carries
reachability to reachability. -/
theorem reachable_map_of_adj {α β : Type*} {Γ : SimpleGraph α} {Δ : SimpleGraph β}
    (f : α → β) (hf : ∀ ⦃a b⦄, Γ.Adj a b → Δ.Adj (f a) (f b) ∨ f a = f b) {a b : α}
    (h : Γ.Reachable a b) : Δ.Reachable (f a) (f b) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
      rcases hf hbc with h' | he
      · exact ih.tail h'
      · exact he ▸ ih

/-- A walk in the 1-skeleton of `Λ''` projects to a walk in the dual graph. -/
theorem projRegion_reachable {v w : Vertex D} (h : (graph (D := D)).Reachable v w) :
    (dualGraph D).Reachable (projRegion D v) (projRegion D w) :=
  reachable_map_of_adj (projRegion D)
    (fun _ _ hab => dualGraph_adj_or_eq_projRegion hab) h

end Dunwoody

/-! ## The dual graph is connected -/

theorem dualGraph_connected {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    (D : Work.ORDunwoody.Cayley.GeoData T t₀ P) :
    (Work.ORDunwoody.Dunwoody.dualGraph D).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨Dunwoody.Region.mk D ((1 : G), Sum.inl ()), ?_⟩
  intro R
  refine Quotient.inductionOn R (fun u => ?_)
  exact Dunwoody.projRegion_reachable
    (Work.ORDunwoody.graph_reachable D (Sum.inl ((1 : G), Sum.inl ())) (Sum.inl u))

end Work.ORDunwoody
