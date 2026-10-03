/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The pattern points of a track, and the chord graph on them

`Dunwoody/Track.lean` defines a *track* as a connected component of the chord graph on the pattern
points `MidV D`.  In this file we fix, for a track `τ`,

* `trackVerts τ` — the set of pattern points of `τ`, i.e. the vertices of the component;
* the action of the stabiliser `MulAction.stabilizer G τ` on `trackVerts τ`, induced by the
  action of `G` on `MidV D`;
* `trackGraph τ` — the graph induced on `trackVerts τ` by the chord graph (`SimpleGraph.induce`).

The point of the construction is that the stabiliser `H = MulAction.stabilizer G τ`

* acts **freely** on `trackVerts τ` (`trackVerts_smul_eq_self`) because `G` acts freely on `MidV D`;
* preserves the graph `trackGraph τ` (`trackGraph_smul_adj`);
* and `trackGraph τ` is **connected** (`trackGraph_connected`: `trackVerts τ` is the support of a
  connected component of the chord graph, and the graph induced on the support of a connected
  component is connected).

Together with the finiteness of the orbit space of `H` on `trackVerts τ` and the local finiteness
of `trackGraph τ` (proved elsewhere, see `finite_orbits_trackVerts.lean` and
`chordAdj_neighbors_finite.lean`), this puts `H` in the scope of
`Work.WallSystem.fg_of_free_cocompact_graph`, so that `H` is finitely generated.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.TrackWall

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Dunwoody

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G} {D : Cayley.GeoData T t₀ P}

/-- **The pattern points of a track**: the vertices of the connected component `τ` of the chord
graph. -/
def trackVerts (τ : Track D) : Set (MidV D) := {m | trackOf m = τ}

/-- The stabiliser of a track acts on the pattern points of the track: the action is the
restriction of the action of `G` on the pattern points, which preserves the track. -/
instance trackVertsMulAction (τ : Track D) :
    MulAction (MulAction.stabilizer G τ) (trackVerts τ) where
  smul h m := ⟨(h : G) • m.1, by
    show trackOf ((h : G) • m.1) = τ
    have hh : (h : G) • τ = τ := MulAction.mem_stabilizer_iff.mp h.2
    rw [trackOf_smul, m.2, hh]⟩
  one_smul m := Subtype.ext (one_smul G m.1)
  mul_smul h k m := Subtype.ext (mul_smul (h : G) (k : G) m.1)

@[simp] theorem trackVerts_smul_coe {τ : Track D} (h : MulAction.stabilizer G τ)
    (m : trackVerts τ) :
    ((h • m : trackVerts τ) : MidV D) = (h : G) • (m : MidV D) := rfl

/-- **The chord graph on the pattern points of a track**, induced from the chord graph. -/
def trackGraph (τ : Track D) : SimpleGraph (trackVerts τ) :=
  SimpleGraph.induce (trackVerts τ) (chordGraph D)

theorem trackGraph_adj_iff {τ : Track D} {a b : trackVerts τ} :
    (trackGraph τ).Adj a b ↔ (chordGraph D).Adj a.1 b.1 :=
  SimpleGraph.induce_adj

/-- The action of `G` on the pattern points is free. -/
theorem midV_smul_eq_self {m : MidV D} {g : G} (h : g • m = m) : g = 1 := by
  have h2 : g * m.1 = m.1 := congrArg Prod.fst h
  calc g = g * m.1 * m.1⁻¹ := by group
    _ = m.1 * m.1⁻¹ := by rw [h2]
    _ = 1 := by group

/-- **The stabiliser of a track acts freely on the pattern points of the track.** -/
theorem trackVerts_smul_eq_self {τ : Track D} {h : MulAction.stabilizer G τ}
    {m : trackVerts τ} (hm : h • m = m) : h = 1 := by
  refine Subtype.ext (midV_smul_eq_self (m := (m : MidV D)) ?_)
  exact congrArg Subtype.val hm

/-- A track has at least one pattern point (it is a connected component of a graph). -/
theorem trackVerts_nonempty (τ : Track D) : Nonempty (trackVerts τ) := by
  obtain ⟨m, hm⟩ :=
    Quotient.mk_surjective (s := SimpleGraph.reachableSetoid (chordGraph D)) τ
  exact ⟨⟨m, hm⟩⟩

/-- **The graph on the pattern points of a track is connected**: the pattern points of a track are
the support of a connected component of the chord graph, and the induced graph on the support of
a connected component is connected. -/
theorem trackGraph_connected (τ : Track D) : (trackGraph τ).Connected := by
  have h := SimpleGraph.ConnectedComponent.connected_toSimpleGraph τ
  exact h

/-- **The stabiliser of a track preserves the chord graph on the track.** -/
theorem trackGraph_smul_adj (τ : Track D) (h : MulAction.stabilizer G τ) {x y : trackVerts τ}
    (hxy : (trackGraph τ).Adj x y) : (trackGraph τ).Adj (h • x) (h • y) := by
  have hxy' : (chordGraph D).Adj x.1 y.1 := trackGraph_adj_iff.mp hxy
  rw [trackGraph_adj_iff]
  show (chordGraph D).Adj ((h : G) • x.1) ((h : G) • y.1)
  exact chordGraph_smul_adj (h : G) hxy'

end Work.ORDunwoody
