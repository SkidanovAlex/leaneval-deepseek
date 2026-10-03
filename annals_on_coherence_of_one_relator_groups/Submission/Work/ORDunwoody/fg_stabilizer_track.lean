/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The stabiliser of a track is finitely generated

Let `G` be a group acting on a tree `T` with `t₀ : V`, `P` a finite presentation of `G` and
`D : GeoData T t₀ P` the geometric data of the Dunwoody construction (`Λ''` is the subdivided
Cayley complex of `P`).  The *tracks* of the pattern are the connected components `τ` of the chord
graph on the pattern points `MidV D`; they are the walls of Dunwoody's construction.

This file proves the finite generation of the stabiliser of a track,

    (MulAction.stabilizer G τ).FG,

which is one of the inputs of `S.HasFGStab` for the dual tree of the wall system
(`DESIGN_N13.md` §4d).  The proof puts the stabiliser `H = MulAction.stabilizer G τ` in the scope
of `Work.WallSystem.fg_of_free_cocompact_graph`: `H` acts **freely** on the set `trackVerts τ` of
pattern points of the track, this action preserves the graph `trackGraph τ` induced by the chord
graph, and

* `trackGraph τ` is **connected** (`trackGraph_connected`: the pattern points of `τ` are the
  support of a connected component of the chord graph),
* `H` has **finitely many orbits** on `trackVerts τ` (`finite_orbits_trackVerts`),
* `trackGraph τ` is **locally finite** (`chordAdj_neighbors_finite`: a pattern point lies on only
  finitely many faces, hence has finitely many chord neighbours; the graph on the track inherits
  this, `trackGraph_neighborSet_finite` below).

The last two are proved in the delegated files
`Submission/Work/ORDunwoody/finite_orbits_trackVerts.lean` and
`Submission/Work/ORDunwoody/chordAdj_neighbors_finite.lean`; the remaining pieces (the action of
the stabiliser on the track, its freeness, and the connectedness of the chord graph on a track)
are in `Submission/Work/ORDunwoody/Dunwoody/TrackGraph.lean`.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.TrackWall
import Submission.Work.ORDunwoody.Dunwoody.TrackGraph
import Submission.Work.ORDunwoody.finite_orbits_track
import Submission.Work.ORDunwoody.finite_orbits_vertex
import Submission.Work.ORDunwoody.chordAdj_neighbors_finite
import Submission.Work.ORDunwoody.finite_orbits_trackVerts
import Submission.Work.WallSystem.fg_of_free_cocompact_graph

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Dunwoody

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G} {D : Cayley.GeoData T t₀ P}

/-- **Local finiteness of the chord graph on a track.**  A pattern point of a track has only
finitely many chord neighbours in the ambient chord graph (`chordAdj_neighbors_finite`); passing
to the graph induced on the track only removes neighbours, and the subtype inclusion is
injective. -/
theorem trackGraph_neighborSet_finite (τ : Track D)
    (h : ∀ m : MidV D, {m' : MidV D | ChordAdj m m'}.Finite) :
    ∀ x : trackVerts τ, {y : trackVerts τ | (trackGraph τ).Adj x y}.Finite := by
  intro x
  refine Set.Finite.of_finite_image (f := fun y : trackVerts τ => (y : MidV D)) ?_ ?_
  · refine (h x.1).subset ?_
    rintro z ⟨y, hy, rfl⟩
    exact (trackGraph_adj_iff.mp hy).1
  · intro a _ b _ hab
    exact Subtype.ext hab

theorem fg_stabilizer_track {G : Type u} [Group G] {V : Type u} [MulAction G V]
    [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}
    (τ : Work.ORDunwoody.Dunwoody.Track D) :
    (MulAction.stabilizer G τ).FG := by
  -- The stabiliser of the track acts freely on a connected, locally finite graph with finitely
  -- many orbits of vertices: the chord graph on the pattern points of the track.
  have hne : Nonempty (trackVerts τ) := trackVerts_nonempty τ
  exact (Group.fg_iff_subgroup_fg (MulAction.stabilizer G τ)).mp
    (Work.WallSystem.fg_of_free_cocompact_graph (trackGraph τ)
      (fun h x y hxy => trackGraph_smul_adj τ h hxy)
      (trackGraph_connected τ)
      (fun _ m hm => trackVerts_smul_eq_self hm)
      (finite_orbits_trackVerts (D := D) τ)
      (trackGraph_neighborSet_finite τ
        (fun m => chordAdj_neighbors_finite (D := D) (m := m))))

end Work.ORDunwoody
