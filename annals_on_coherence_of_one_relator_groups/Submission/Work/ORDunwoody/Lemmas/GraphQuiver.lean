/-
Copyright: work of the ORDunwoody subproject (node N13).

# The edge quiver of a simple graph

A `SimpleGraph` is a simplicial graph; a `Quiver` with an involutive reversal of arrows
(`Quiver.HasInvolutiveReverse`) is the same notion with a *set* of arrows between two
vertices.  This file sets up the translation between the two languages, used to compare
`Work.ORDunwoody.GTree` (a `SimpleGraph` plus an action) with the Bass--Serre notion of a
`G`-tree `Work.ORBassSerre.IsTree` (a quiver with an involutive reversal).

## Main definitions

* `Work.ORDunwoody.Lemmas.graphQuiver`: one arrow `u ⟶ v` for each edge `u–v` of `G`;
* `pathToWalk` / `walkToPath`: the translations between paths in the edge quiver and walks
  of the graph;
* `SimpleGraph.Walk.BacktrackFree`: a walk has no immediate backtracking;
* `graphQuiverAction`: if `G` acts on a `SimpleGraph` tree preserving adjacency, it acts on
  its edge quiver;
* `totalEquivAdjPair`: the arrows of the edge quiver are the oriented edges of the graph.

The arrow type is `ULift {_ : Unit // G.Adj u v}`; the `ULift` only serves to place the
arrows in an arbitrary universe.  Because the quiver instance `graphQuiver G` is not a
type class instance (it depends on `G`), statements below use the wrappers `qnil`, `qcons`,
`qcomp`, `qlen`, `qReduced` and explicit `@`-applications, while proofs start with
`letI : Quiver V := graphQuiver G` so that the usual notations are available.
-/
import Mathlib
import Submission.Work.ORDunwoody.Basic
import Submission.Work.ORBassSerre.Action.Basic

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe u x

namespace Work.ORDunwoody.Lemmas

open SimpleGraph

variable {V : Type u}

/-- The quiver attached to a simple graph `G`: exactly one arrow for every oriented edge of
`G`. -/
abbrev graphQuiver {V : Type u} (G : SimpleGraph V) : Quiver.{x, u} V :=
  ⟨fun a b => ULift.{x, 0} {_x : Unit // G.Adj a b}⟩

instance graphQuiverSubsingleton {V : Type u} (G : SimpleGraph V) (a b : V) :
    Subsingleton (@Quiver.Hom V (graphQuiver G) a b) := by
  refine ⟨fun p q => ?_⟩
  exact ULift.ext (x := p) (y := q) (Subtype.ext (Subsingleton.elim p.down.1 q.down.1))

instance graphQuiverHasReverse {V : Type u} (G : SimpleGraph V) :
    @Quiver.HasReverse V (graphQuiver G) := by
  refine @Quiver.HasReverse.mk V (graphQuiver G) ?_
  intro a b e
  exact ULift.up ⟨(), e.down.2.symm⟩

instance graphQuiverHasInvolutiveReverse {V : Type u} (G : SimpleGraph V) :
    @Quiver.HasInvolutiveReverse V (graphQuiver G) := by
  refine @Quiver.HasInvolutiveReverse.mk V (graphQuiver G) (graphQuiverHasReverse G) ?_
  intro a b e
  exact Subsingleton.elim _ _

/-- Adjacency of a graph, read in its edge quiver. -/
theorem nonempty_hom_iff_adj {V : Type u} (G : SimpleGraph V) (a b : V) :
    Nonempty (@Quiver.Hom V (graphQuiver G) a b) ↔ G.Adj a b := by
  constructor
  · rintro ⟨e⟩; exact e.down.2
  · intro h; exact ⟨ULift.up ⟨(), h⟩⟩

/-- The trivial path at a vertex of the edge quiver. -/
abbrev qnil {V : Type u} (G : SimpleGraph V) (a : V) : @Quiver.Path V (graphQuiver G) a a :=
  @Quiver.Path.nil V (graphQuiver G) a

/-- Appending an arrow to a path in the edge quiver. -/
abbrev qcons {V : Type u} (G : SimpleGraph V) {a b c : V}
    (p : @Quiver.Path V (graphQuiver G) a b) (e : @Quiver.Hom V (graphQuiver G) b c) :
    @Quiver.Path V (graphQuiver G) a c :=
  @Quiver.Path.cons V (graphQuiver G) a b c p e

/-- Composition of paths in the edge quiver. -/
abbrev qcomp {V : Type u} (G : SimpleGraph V) {a b c : V}
    (p : @Quiver.Path V (graphQuiver G) a b) (q : @Quiver.Path V (graphQuiver G) b c) :
    @Quiver.Path V (graphQuiver G) a c :=
  @Quiver.Path.comp V (graphQuiver G) a b c p q

/-- The length of a path in the edge quiver. -/
abbrev qlen {V : Type u} (G : SimpleGraph V) {a b : V}
    (p : @Quiver.Path V (graphQuiver G) a b) : ℕ :=
  @Quiver.Path.length V (graphQuiver G) a b p

/-- Reducedness of a path in the edge quiver. -/
abbrev qReduced {V : Type u} (G : SimpleGraph V) {a b : V}
    (p : @Quiver.Path V (graphQuiver G) a b) : Prop :=
  @Quiver.Path.IsReduced V (graphQuiver G) a b (graphQuiverHasReverse G) p

@[simp] theorem qnil_eq {V : Type u} (G : SimpleGraph V) (a : V) :
    qnil G a = @Quiver.Path.nil V (graphQuiver G) a := rfl

@[simp] theorem qcons_eq {V : Type u} (G : SimpleGraph V) {a b c : V}
    (p : @Quiver.Path V (graphQuiver G) a b) (e : @Quiver.Hom V (graphQuiver G) b c) :
    qcons G p e = @Quiver.Path.cons V (graphQuiver G) a b c p e := rfl

@[simp] theorem qcomp_eq {V : Type u} (G : SimpleGraph V) {a b c : V}
    (p : @Quiver.Path V (graphQuiver G) a b) (q : @Quiver.Path V (graphQuiver G) b c) :
    qcomp G p q = @Quiver.Path.comp V (graphQuiver G) a b c p q := rfl

@[simp] theorem qlen_eq {V : Type u} (G : SimpleGraph V) {a b : V}
    (p : @Quiver.Path V (graphQuiver G) a b) :
    qlen G p = @Quiver.Path.length V (graphQuiver G) a b p := rfl

@[simp] theorem qReduced_eq {V : Type u} (G : SimpleGraph V) {a b : V}
    (p : @Quiver.Path V (graphQuiver G) a b) :
    qReduced G p = @Quiver.Path.IsReduced V (graphQuiver G) a b (graphQuiverHasReverse G) p := rfl

/-- The walk of `G` associated with a path in the edge quiver of `G`. -/
def pathToWalk {V : Type u} (G : SimpleGraph V) :
    {a b : V} → @Quiver.Path V (graphQuiver G) a b → G.Walk a b :=
  fun {a b} p =>
    @Quiver.Path.rec V (graphQuiver G) a (fun b _ => G.Walk a b) (SimpleGraph.Walk.nil)
      (fun {b c} _ e ih => ih.concat e.down.2) b p

/-- The path in the edge quiver of `G` associated with a walk of `G`. -/
def walkToPath {V : Type u} (G : SimpleGraph V) :
    {a b : V} → G.Walk a b → @Quiver.Path V (graphQuiver G) a b
  | _, _, .nil => @Quiver.Path.nil V (graphQuiver G) _
  | _, _, .cons h p =>
      @Quiver.Path.comp V (graphQuiver G) _ _ _
        (@Quiver.Hom.toPath V (graphQuiver G) _ _ (ULift.up ⟨(), h⟩))
        (walkToPath G p)

@[simp] theorem pathToWalk_nil {V : Type u} (G : SimpleGraph V) (a : V) :
    pathToWalk G (qnil G a) = SimpleGraph.Walk.nil := rfl

@[simp] theorem pathToWalk_cons {V : Type u} (G : SimpleGraph V) {a b c : V}
    (p : @Quiver.Path V (graphQuiver G) a b) (e : @Quiver.Hom V (graphQuiver G) b c) :
    pathToWalk G (qcons G p e) = (pathToWalk G p).concat e.down.2 := rfl

@[simp] theorem walkToPath_nil {V : Type u} (G : SimpleGraph V) (a : V) :
    walkToPath G (SimpleGraph.Walk.nil : G.Walk a a) = qnil G a := rfl

/-- The length of the walk of a path is the length of the path. -/
theorem pathToWalk_length {V : Type u} (G : SimpleGraph V) {a b : V}
    (p : @Quiver.Path V (graphQuiver G) a b) : (pathToWalk G p).length = qlen G p := by
  letI : Quiver V := graphQuiver G
  show (pathToWalk G p).length = p.length
  induction p with
  | nil => rfl
  | cons p e ih => rw [pathToWalk_cons, SimpleGraph.Walk.length_concat, ih,
      Quiver.Path.length_cons]

/-- `pathToWalk` turns composition of paths into concatenation of walks. -/
theorem pathToWalk_comp {V : Type u} (G : SimpleGraph V) {a b c : V}
    (p : @Quiver.Path V (graphQuiver G) a b) (q : @Quiver.Path V (graphQuiver G) b c) :
    pathToWalk G (qcomp G p q) = (pathToWalk G p).append (pathToWalk G q) := by
  letI : Quiver V := graphQuiver G
  show pathToWalk G (p.comp q) = (pathToWalk G p).append (pathToWalk G q)
  induction q with
  | nil => simp
  | cons q e ih =>
    rw [Quiver.Path.comp_cons, pathToWalk_cons, ih, pathToWalk_cons,
      SimpleGraph.Walk.concat_eq_append, SimpleGraph.Walk.concat_eq_append,
      SimpleGraph.Walk.append_assoc]

/-- A closed path in the edge quiver is trivial iff its walk is. -/
theorem pathToWalk_eq_nil_iff {V : Type u} (G : SimpleGraph V) {a : V}
    (p : @Quiver.Path V (graphQuiver G) a a) :
    pathToWalk G p = (SimpleGraph.Walk.nil : G.Walk a a) ↔ p = qnil G a := by
  constructor
  · intro h
    have hlen : qlen G p = 0 := by rw [← pathToWalk_length G p, h]; rfl
    have hlen' : (@Quiver.Path.length V (graphQuiver G) a a p) = 0 := hlen
    exact @Quiver.Path.eq_nil_of_length_zero V (graphQuiver G) a p hlen'
  · rintro rfl; rfl

/-- The path of a walk starting with an edge. -/
theorem walkToPath_cons' {V : Type u} (G : SimpleGraph V) {a b c : V} (h : G.Adj a b)
    (p : G.Walk b c) :
    walkToPath G (SimpleGraph.Walk.cons h p)
      = @Quiver.Path.comp V (graphQuiver G) a b c
          (@Quiver.Hom.toPath V (graphQuiver G) a b (ULift.up ⟨(), h⟩)) (walkToPath G p) :=
  rfl

/-- The walk of a single arrow of the edge quiver. -/
theorem pathToWalk_homToPath {V : Type u} (G : SimpleGraph V) {a b : V}
    (e : @Quiver.Hom V (graphQuiver G) a b) :
    pathToWalk G (@Quiver.Hom.toPath V (graphQuiver G) a b e) = e.down.2.toWalk := by
  show pathToWalk G (qcons G (qnil G a) e) = e.down.2.toWalk
  rw [pathToWalk_cons, pathToWalk_nil]
  rfl

/-- The path of a single-edge walk. -/
theorem walkToPath_toWalk {V : Type u} (G : SimpleGraph V) {a b : V} (h : G.Adj a b) :
    walkToPath G h.toWalk = @Quiver.Hom.toPath V (graphQuiver G) a b (ULift.up ⟨(), h⟩) := by
  show walkToPath G (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil) = _
  rw [walkToPath_cons']
  exact @Quiver.Path.comp_nil V (graphQuiver G) a b
    (@Quiver.Hom.toPath V (graphQuiver G) a b (ULift.up ⟨(), h⟩))

/-- `walkToPath` turns concatenation of walks into composition of paths. -/
theorem walkToPath_append {V : Type u} (G : SimpleGraph V) {a b c : V} (p : G.Walk a b)
    (q : G.Walk b c) :
    walkToPath G (p.append q) = qcomp G (walkToPath G p) (walkToPath G q) := by
  induction p with
  | nil => simpa only [SimpleGraph.Walk.nil_append, walkToPath_nil, qcomp_eq]
      using (@Quiver.Path.nil_comp V (graphQuiver G) _ _ (walkToPath G q)).symm
  | cons h p ih =>
    simp only [qcomp_eq] at *
    rw [SimpleGraph.Walk.cons_append, walkToPath_cons', ih, walkToPath_cons',
      @Quiver.Path.comp_assoc V (graphQuiver G) _ _ _ _ _ _]

/-- `walkToPath` is a section of `pathToWalk`. -/
theorem walkToPath_pathToWalk {V : Type u} (G : SimpleGraph V) {a b : V}
    (p : @Quiver.Path V (graphQuiver G) a b) : walkToPath G (pathToWalk G p) = p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    show walkToPath G (pathToWalk G p |>.concat e.down.2) = qcons G p e
    rw [SimpleGraph.Walk.concat_eq_append, walkToPath_append, ih, walkToPath_toWalk]
    refine (@Quiver.Path.comp_toPath_eq_cons V (graphQuiver G) _ _ _ p _).trans ?_
    exact congrArg (fun f => qcons G p f) (Subsingleton.elim _ _)

/-- `pathToWalk` is a section of `walkToPath`. -/
theorem pathToWalk_walkToPath {V : Type u} (G : SimpleGraph V) {a b : V} (w : G.Walk a b) :
    pathToWalk G (walkToPath G w) = w := by
  induction w with
  | nil => rfl
  | cons h p ih =>
    rw [show walkToPath G (SimpleGraph.Walk.cons h p)
        = qcomp G (@Quiver.Hom.toPath V (graphQuiver G) _ _ (ULift.up ⟨(), h⟩))
            (walkToPath G p) from rfl]
    rw [pathToWalk_comp, pathToWalk_homToPath, ih]
    rfl

/-- Adjacency of the endpoints of an arrow of the edge quiver. -/
theorem hom_dart_adj {V : Type u} {G : SimpleGraph V} {a b : V}
    (e : @Quiver.Hom V (graphQuiver G) a b) : G.Adj a b := e.down.2

end Work.ORDunwoody.Lemmas

namespace SimpleGraph

namespace Walk

variable {V : Type u}

/-- A walk of a graph has no immediate backtracking if no two consecutive darts of the walk
are reverses of one another. -/
def BacktrackFree {G : SimpleGraph V} {a b : V} (w : G.Walk a b) : Prop :=
  w.darts.IsChain (fun d d' => d' ≠ d.symm)

theorem backtrackFree_nil {G : SimpleGraph V} (a : V) :
    (SimpleGraph.Walk.nil : G.Walk a a).BacktrackFree := by
  simp [SimpleGraph.Walk.BacktrackFree]

end Walk

end SimpleGraph

namespace Work.ORDunwoody.Lemmas

open SimpleGraph

variable {V : Type u}

section Action

variable {G : Type*} [Group G] [MulAction G V]

/-- A `G`-action on a graph preserving adjacency induces a `G`-action on its edge quiver. -/
def graphQuiverAction (T : Work.ORDunwoody.GTree G V) :
    @Work.ORBassSerre.GraphAction G V _ (graphQuiver T.graph)
      (graphQuiverHasReverse T.graph) _ := by
  refine @Work.ORBassSerre.GraphAction.mk G V _ (graphQuiver T.graph)
    (graphQuiverHasReverse T.graph) _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro g e
    letI : Quiver V := graphQuiver T.graph
    exact ⟨g • e.left, g • e.right, ULift.up ⟨(), T.smul_adj g e.hom.down.2⟩⟩
  · intro e
    letI : Quiver V := graphQuiver T.graph
    refine Quiver.Total.ext (one_smul G e.left) (one_smul G e.right) ?_
    refine Subsingleton.helim ?_ _ _
    exact (congrArg (fun y => @Quiver.Hom V (graphQuiver T.graph) ((1 : G) • e.left) y)
        (one_smul G e.right)).trans
      (congrArg (fun x' => @Quiver.Hom V (graphQuiver T.graph) x' e.right)
        (one_smul G e.left))
  · intro g h e
    letI : Quiver V := graphQuiver T.graph
    refine Quiver.Total.ext (mul_smul g h e.left) (mul_smul g h e.right) ?_
    refine Subsingleton.helim ?_ _ _
    exact (congrArg (fun y => @Quiver.Hom V (graphQuiver T.graph) ((g * h) • e.left) y)
        (mul_smul g h e.right)).trans
      (congrArg (fun x' => @Quiver.Hom V (graphQuiver T.graph) x' (g • (h • e.right)))
        (mul_smul g h e.left))
  · intro g e
    rfl
  · intro g e
    rfl
  · intro g e
    letI : Quiver V := graphQuiver T.graph
    refine Quiver.Total.ext rfl rfl ?_
    exact heq_iff_eq.mpr (Subsingleton.elim _ _)

/-- The oriented edge underlying an arrow of the edge quiver. -/
def totalToAdjPair (T : Work.ORDunwoody.GTree G V)
    (e : @Quiver.Total V (graphQuiver T.graph)) : T.AdjPair :=
  ⟨(@Quiver.Total.left V (graphQuiver T.graph) e,
    @Quiver.Total.right V (graphQuiver T.graph) e),
    (@Quiver.Total.hom V (graphQuiver T.graph) e).down.2⟩

/-- The arrow of the edge quiver with a given oriented edge. -/
def adjPairToTotal (T : Work.ORDunwoody.GTree G V) (p : T.AdjPair) :
    @Quiver.Total V (graphQuiver T.graph) :=
  @Quiver.Total.mk V (graphQuiver T.graph) p.1.1 p.1.2 (ULift.up ⟨(), p.2⟩)

@[simp] theorem totalToAdjPair_val (T : Work.ORDunwoody.GTree G V)
    (e : @Quiver.Total V (graphQuiver T.graph)) :
    (totalToAdjPair T e).1 = (@Quiver.Total.left V (graphQuiver T.graph) e,
      @Quiver.Total.right V (graphQuiver T.graph) e) := rfl

@[simp] theorem totalToAdjPair_left (T : Work.ORDunwoody.GTree G V)
    (e : @Quiver.Total V (graphQuiver T.graph)) :
    (totalToAdjPair T e).1.1 = @Quiver.Total.left V (graphQuiver T.graph) e := rfl

@[simp] theorem totalToAdjPair_right (T : Work.ORDunwoody.GTree G V)
    (e : @Quiver.Total V (graphQuiver T.graph)) :
    (totalToAdjPair T e).1.2 = @Quiver.Total.right V (graphQuiver T.graph) e := rfl

@[simp] theorem adjPairToTotal_left (T : Work.ORDunwoody.GTree G V) (p : T.AdjPair) :
    @Quiver.Total.left V (graphQuiver T.graph) (adjPairToTotal T p) = p.1.1 := rfl

@[simp] theorem adjPairToTotal_right (T : Work.ORDunwoody.GTree G V) (p : T.AdjPair) :
    @Quiver.Total.right V (graphQuiver T.graph) (adjPairToTotal T p) = p.1.2 := rfl

/-- The action on oriented edges of a tree, written out. -/
@[simp] theorem GTree_AdjPair_smul {G : Type*} [Group G] {V : Type*} [MulAction G V]
    (T : Work.ORDunwoody.GTree G V) (g : G) (p : T.AdjPair) :
    g • p = (⟨(g • p.1.1, g • p.1.2), T.smul_adj g p.2⟩ : T.AdjPair) := rfl

/-- The arrows of the edge quiver of a graph are exactly the oriented edges of the graph. -/
def totalEquivAdjPair (T : Work.ORDunwoody.GTree G V) :
    @Quiver.Total V (graphQuiver T.graph) ≃ T.AdjPair where
  toFun := totalToAdjPair T
  invFun := adjPairToTotal T
  left_inv e := by
    refine Quiver.Total.ext rfl rfl ?_
    exact heq_iff_eq.mpr (Subsingleton.elim _ _)
  right_inv p := by
    cases p with
    | mk p h => rfl

@[simp] theorem totalEquivAdjPair_apply (T : Work.ORDunwoody.GTree G V)
    (e : @Quiver.Total V (graphQuiver T.graph)) :
    totalEquivAdjPair T e = totalToAdjPair T e := rfl

/-- The equivalence between the arrows of the edge quiver and the oriented edges of the
graph is compatible with the `G`-actions. -/
theorem totalEquivAdjPair_smul (T : Work.ORDunwoody.GTree G V)
    (hA : @Work.ORBassSerre.GraphAction G V _ (graphQuiver T.graph)
      (graphQuiverHasReverse T.graph) _) (g : G)
    (e : @Quiver.Total V (graphQuiver T.graph)) :
    totalEquivAdjPair T (hA.smulTotal g e) = g • totalEquivAdjPair T e := by
  refine Subtype.ext ?_
  simp only [totalEquivAdjPair_apply, totalToAdjPair_val, Work.ORBassSerre.GraphAction.smul_left,
    Work.ORBassSerre.GraphAction.smul_right, GTree_AdjPair_smul]
end Action

end Work.ORDunwoody.Lemmas
