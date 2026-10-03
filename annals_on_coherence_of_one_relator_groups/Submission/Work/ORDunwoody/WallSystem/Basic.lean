/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# Wall systems: the abstract form of "the dual of Dunwoody's pattern is a tree"

`dunwoodyResolution` (GL17 Prop. 2.17 / Cor. 2.18, constant case) is proved by Dunwoody's
pattern/tracks/dual construction inside the universal cover `Λ` of a finite presentation
2-complex: the *pattern* is `P = φ⁻¹(midpoints)`, its components are the *tracks*, the
components of `Λ ∖ P` are the *regions*, and the *dual* `S` (regions for vertices, tracks for
edges) is the desired tree.

This file isolates the **abstract graph-theoretic content** of the proof that the dual is a
tree, so that it can be proved once and for all, independently of the (substantial) 2-complex
theory needed to *produce* the side functions.

## The data

* a type `Wall` of tracks and a type `Region` of regions;
* an incidence relation `Inc w a b` — "the wall `w` separates the regions `a` and `b`";
* for every wall `w` a *side function* `side w : Region → ZMod 2` with
  * `Inc w a b → side w a ≠ side w b`  (`side_ne`: the two regions adjacent along `w` lie on
    opposite sides of `w`);
  * `Inc w a b → w' ≠ w → side w' a = side w' b`  (`side_other`: a wall different from `w`
    does not separate the two regions adjacent along `w`).

The last field, `few_inc`, is the geometric input that *every wall is incident with at most
two regions*: this is where local finiteness of the tracks and the "each local side of a
track meets exactly one region" fact enter (they are proved in the geometric development).

## The theorem

`System.isAcyclic`: the dual graph, with `a` adjacent to `b` when some wall separates them, is
acyclic.  Consequently (`System.isTree`) it is a tree as soon as it is connected.

The proof is the classical one: a cycle of the dual would give a closed curve crossing a fixed
track exactly once, which is impossible because each track separates.  In the graph-theoretic
formulation: walking around the cycle, all edges except the one through a fixed wall `w` leave
`side w` unchanged, so `side w` takes the same value at the two ends of the edge through `w` —
contradiction with `side_ne`.
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

universe u

namespace Work.ORDunwoody.WallSystem

open SimpleGraph

/-- A **wall system**: a family of "walls" (tracks) separating pairs of "regions", together
with a consistent notion of *side* of every region with respect to every wall.  See the module
docstring for the geometric meaning of the fields. -/
structure System (Wall : Type u) (Region : Type u) where
  /-- `Inc w a b` means: the wall `w` separates the region `a` from the region `b` (the
  regions `a` and `b` touch `w` from its two sides, at a common point). -/
  Inc : Wall → Region → Region → Prop
  /-- Incidence is symmetric. -/
  inc_symm : ∀ ⦃w : Wall⦄ ⦃a b : Region⦄, Inc w a b → Inc w b a
  /-- The side of a region with respect to a wall: `0` or `1` according to which component of
  the complement of the wall the region lies in. -/
  side : Wall → Region → ZMod 2
  /-- The two regions adjacent along a wall are on opposite sides of it. -/
  side_ne : ∀ ⦃w : Wall⦄ ⦃a b : Region⦄, Inc w a b → side w a ≠ side w b
  /-- The side with respect to a wall `w'` is the same on both regions adjacent along a
  *different* wall `w`. -/
  side_other : ∀ ⦃w : Wall⦄ ⦃a b : Region⦄, Inc w a b →
    ∀ ⦃w' : Wall⦄, w' ≠ w → side w' a = side w' b
  /-- Every wall is incident with at most two regions. -/
  few_inc : ∀ ⦃w : Wall⦄ ⦃a b c : Region⦄,
    (∃ b' : Region, Inc w a b') → (∃ b' : Region, Inc w b b') →
    (∃ c' : Region, Inc w c c') → a = b ∨ b = c ∨ a = c

namespace System

variable {Wall : Type u} {Region : Type u} (S : System Wall Region)

/-- Two regions related by a wall are distinct. -/
theorem inc_ne {w : Wall} {a b : Region} (h : S.Inc w a b) : a ≠ b := fun hab =>
  S.side_ne h (by rw [hab])

/-- A pair of regions is separated by at most one wall. -/
theorem inc_unique {w w' : Wall} {a b : Region} (h : S.Inc w a b) (h' : S.Inc w' a b) :
    w = w' := by
  by_contra hne
  exact S.side_ne h (S.side_other h' hne)

/-- If a wall separates `a` from `b`, then any region `x` incident with the same wall is one
of `a`, `b`. -/
theorem eq_or_eq_of_inc {w : Wall} {a b : Region} (h : S.Inc w a b)
    {x y : Region} (hx : S.Inc w x y) : x = a ∨ x = b := by
  rcases S.few_inc ⟨b, h⟩ ⟨a, S.inc_symm h⟩ ⟨y, hx⟩ with h1 | h1 | h1
  · exact absurd h1 (S.inc_ne h)
  · exact Or.inr h1.symm
  · exact Or.inl h1.symm

/-- Two walls incident with two-element sets of regions act on the same two regions: a wall is
incident with at most two regions, and a pair of distinct regions it separates is determined
by it. -/
theorem pair_eq_of_inc {w : Wall} {a b a' b' : Region} (h : S.Inc w a b) (h' : S.Inc w a' b') :
    s(a, b) = s(a', b') := by
  rcases S.eq_or_eq_of_inc h h' with h1 | h1 <;>
    rcases S.eq_or_eq_of_inc h (S.inc_symm h') with h2 | h2
  · exact absurd (h1.trans h2.symm) (S.inc_ne h')
  · rw [h1, h2]
  · rw [h1, h2]
    exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)
  · exact absurd (h1.trans h2.symm) (S.inc_ne h')

/-- The dual graph: regions are adjacent when some wall separates them. -/
def graph : SimpleGraph Region where
  Adj a b := ∃ w : Wall, S.Inc w a b
  symm := ⟨fun a b h => ⟨h.choose, S.inc_symm h.choose_spec⟩⟩
  loopless := ⟨fun a h => S.inc_ne h.choose_spec rfl⟩

theorem graph_adj_iff {a b : Region} : S.graph.Adj a b ↔ ∃ w : Wall, S.Inc w a b := Iff.rfl

/-- The wall separating two adjacent regions (well defined by `inc_unique`). -/
noncomputable def trackOf {a b : Region} (h : S.graph.Adj a b) : Wall := Classical.choose h

theorem trackOf_inc {a b : Region} (h : S.graph.Adj a b) : S.Inc (S.trackOf h) a b :=
  Classical.choose_spec h

/-- Two steps carried by the same wall have the same underlying edge. -/
theorem pair_eq_of_trackOf_eq {a b a' b' : Region} (h : S.graph.Adj a b) (h' : S.graph.Adj a' b')
    (ht : S.trackOf h = S.trackOf h') : s(a, b) = s(a', b') :=
  S.pair_eq_of_inc (S.trackOf_inc h) (ht.symm ▸ S.trackOf_inc h')

/-- A **route** in the dual graph: a chain of adjacent regions, parametrised by its successive
vertices. -/
inductive Route : Region → Region → Type u where
  /-- The trivial route. -/
  | nil (a : Region) : Route a a
  /-- A route starting with a step. -/
  | cons {a b c : Region} : S.graph.Adj a b → Route b c → Route a c

namespace Route

variable {S} {a b c : Region}

/-- The successive walls of a route. -/
noncomputable def tracks : Route S a b → List Wall :=
  Route.rec (S := S) (motive := fun _ _ _ => List Wall) (fun _ => [])
    (fun {x _ _} h _ acc => S.trackOf h :: acc)

@[simp] theorem tracks_cons (h : S.graph.Adj a b) (r : Route S b c) :
    (Route.cons h r).tracks = S.trackOf h :: r.tracks := rfl

@[simp] theorem tracks_nil (a : Region) : (Route.nil (S := S) a).tracks = [] := rfl

/-- The successive (undirected) edges of a route. -/
noncomputable def pairs : Route S a b → List (Sym2 Region) :=
  Route.rec (S := S) (motive := fun _ _ _ => List (Sym2 Region)) (fun _ => [])
    (fun {x y _} _ _ acc => s(x, y) :: acc)

@[simp] theorem pairs_cons (h : S.graph.Adj a b) (r : Route S b c) :
    (Route.cons h r).pairs = s(a, b) :: r.pairs := rfl

@[simp] theorem pairs_nil (a : Region) : (Route.nil (S := S) a).pairs = [] := rfl

/-- The side function is constant along a route that does not use a given wall. -/
theorem side_eq_of_not_mem : ∀ {a b : Region} (r : Route S a b) {w : Wall},
    w ∉ r.tracks → S.side w a = S.side w b
  | _, _, .nil _, w, _ => rfl
  | _, _, .cons h r, w, hw => by
      rw [tracks_cons, List.mem_cons, not_or] at hw
      obtain ⟨hw1, hw2⟩ := hw
      exact (S.side_other (S.trackOf_inc h) hw1).trans (side_eq_of_not_mem r hw2)

/-- A step of a route whose wall is a prescribed wall `w`. -/
theorem exists_step_of_mem_tracks : ∀ {a b : Region} (r : Route S a b) {w : Wall},
    w ∈ r.tracks → ∃ (c d : Region) (h : S.graph.Adj c d), S.trackOf h = w
  | _, _, .nil _, w, hw => by
      rw [tracks_nil] at hw
      exact absurd hw List.not_mem_nil
  | _, _, .cons h r, w, hw => by
      rw [tracks_cons, List.mem_cons] at hw
      rcases hw with hw | hw
      · exact ⟨_, _, h, hw.symm⟩
      · obtain ⟨c, d, h', hh'⟩ := exists_step_of_mem_tracks r hw
        exact ⟨c, d, h', hh'⟩

/-- A step of a route whose wall is a prescribed wall `w`, together with its edge. -/
theorem exists_pair_of_mem_tracks : ∀ {a b : Region} (r : Route S a b) {w : Wall},
    w ∈ r.tracks → ∃ (c d : Region) (h : S.graph.Adj c d),
      S.trackOf h = w ∧ s(c, d) ∈ r.pairs
  | _, _, .nil _, w, hw => by
      rw [tracks_nil] at hw
      exact absurd hw List.not_mem_nil
  | _, _, .cons h r, w, hw => by
      rw [tracks_cons, List.mem_cons] at hw
      rcases hw with hw | hw
      · exact ⟨_, _, h, hw.symm, by rw [pairs_cons]; exact List.mem_cons_self ..⟩
      · obtain ⟨c, d, h', hh', hp⟩ := exists_pair_of_mem_tracks r hw
        exact ⟨c, d, h', hh', by rw [pairs_cons]; exact List.mem_cons_of_mem _ hp⟩

/-- If the edges of a route are pairwise distinct then so are the walls it uses. -/
theorem tracks_nodup_of_pairs_nodup : ∀ {a b : Region} (r : Route S a b),
    r.pairs.Nodup → r.tracks.Nodup
  | _, _, .nil _, hp => by simpa using hp
  | _, _, .cons h r, hp => by
      rw [pairs_cons] at hp
      obtain ⟨hp1, hp2⟩ := List.nodup_cons.mp hp
      rw [tracks_cons]
      refine List.nodup_cons.mpr ⟨?_, tracks_nodup_of_pairs_nodup r hp2⟩
      rintro hc
      obtain ⟨c, d, h', htr, hpr⟩ := exists_pair_of_mem_tracks r hc
      refine hp1 ((S.pair_eq_of_trackOf_eq h h' htr.symm).symm ▸ hpr)

/-- A `SimpleGraph.Walk` is a route. -/
def ofWalk : ∀ {a b : Region}, S.graph.Walk a b → Route S a b
  | _, _, .nil => .nil _
  | _, _, .cons h p => .cons h (ofWalk p)

@[simp] theorem ofWalk_nil (a : Region) :
    ofWalk (S := S) (SimpleGraph.Walk.nil : S.graph.Walk a a) = .nil a := by
  simp only [ofWalk]

@[simp] theorem ofWalk_cons (h : S.graph.Adj a b) (p : S.graph.Walk b c) :
    ofWalk (S := S) (SimpleGraph.Walk.cons h p) = .cons h (ofWalk p) := by
  simp only [ofWalk]

theorem pairs_ofWalk : ∀ {a b : Region} (c : S.graph.Walk a b),
    (ofWalk (S := S) c).pairs = c.edges
  | _, _, .nil => by simp only [ofWalk]; rfl
  | _, _, .cons h p => by
      rw [ofWalk_cons, pairs_cons, pairs_ofWalk p, SimpleGraph.Walk.edges_cons]

end Route

/-- **The dual graph of a wall system is acyclic.** -/
theorem isAcyclic : S.graph.IsAcyclic := by
  intro v c hc
  cases c with
  | nil => exact hc.ne_nil rfl
  | cons h p =>
      have hw' : S.trackOf h ∉ (Route.ofWalk (S := S) p).tracks := by
        have hnod : (Route.ofWalk (S := S) (SimpleGraph.Walk.cons h p)).tracks.Nodup := by
          refine Route.tracks_nodup_of_pairs_nodup _ ?_
          rw [Route.pairs_ofWalk]
          exact hc.edges_nodup
        rw [Route.ofWalk_cons, Route.tracks_cons] at hnod
        exact (List.nodup_cons.mp hnod).1
      exact (S.side_ne (S.trackOf_inc h))
        (Route.side_eq_of_not_mem (Route.ofWalk (S := S) p) hw').symm

/-- If moreover the dual graph is connected, it is a tree. -/
theorem isTree (hc : S.graph.Connected) : S.graph.IsTree :=
  ⟨hc, S.isAcyclic⟩

end System

end Work.ORDunwoody.WallSystem
