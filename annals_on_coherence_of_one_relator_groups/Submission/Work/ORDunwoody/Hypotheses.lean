/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The named mathematical inputs of JL §4

Theorems 4.4 and 4.5 of Jaikin-Zapirain–Linton are proved here from a small number of
named statements, each of which is a piece of mathematics that properly belongs to a
neighbouring node of the route design.  They are stated as `Prop`s (not axioms), so the
final theorems are conditional only on these explicitly listed facts; each fact is quoted
below with its source.

* `BieriStrebel`  — JL Lemma 4.3 = Bieri–Strebel [BS78, Lemma 2.1]              (node N11)
* `DunwoodyResolution` — GL17 Proposition 2.17, constant-sequence case          (node N13)
* `FP2TreePromotion` — the descent step in the proof of JL Theorem 4.4
  (Serre, *Trees*, §5 / JL Lemma 4.1 applied to the normal closures of the elliptic
  subgroups of the resolution tree)                                             (node N12/N13)
* `CocompactSubtree` — a finitely generated group acting on a tree has a cocompact
  invariant subtree (standard Bass–Serre theory)                                (node N12)
* `BassSerreFinitelyPresented` — a group acting cocompactly on a tree with finitely
  generated edge stabilizers and finitely presented vertex stabilizers is finitely
  presented (structure theorem for groups acting on trees)                      (node N12)

Each statement is *universe-monomorphic*: all the types it quantifies over live in the
universe of its explicit argument(s), so that the statement has no universe parameter of
its own and can be used as a hypothesis of a theorem without universe friction.
-/
import Submission.Work.ORDunwoody.Basic
import Submission.Work.ORDunwoody.FP2
import Submission.Work.ORDunwoody.Tracks.PartialSubdivision

set_option autoImplicit false

set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

/-- **Bieri–Strebel [BS78, Lemma 2.1] = JL Lemma 4.3.**
For a commutative ring `k` (with `1 ≠ 0`) and a group `G`: `G` is of type `FP₂(k)` if and
only if there is a short exact sequence `1 → N → H → G → 1` with `H` finitely presented and
`N^{ab} ⊗_ℤ k = 0`. -/
def BieriStrebel (k : Type u) [CommRing k] : Prop :=
  ∀ (G : Type u) [Group G],
    IsFP2 k G ↔ ∃ (H : Type u) (_ : Group H) (π : H →* G),
      Function.Surjective π ∧ Group.IsFinitelyPresented H ∧ AbelianizationTensorVanishes k π.ker

/-- **Guirardel–Levitt [GL17, Proposition 2.17], constant-sequence case = Dunwoody's
resolution theorem** (Dunwoody [Dun85], Bestvina–Feighn folding).  If a finitely presented
group `G` acts cocompactly on a tree `T`, then there is a cocompact `G`-tree `S` with
finitely generated vertex and edge stabilizers which dominates `T`. -/
def DunwoodyResolution (G : Type u) [Group G] {V : Type u} [MulAction G V]
    (T : GTree G V) : Prop :=
  Group.IsFinitelyPresented G → T.IsCocompact →
  ∃ (W : Type u) (_ : MulAction G W) (S : GTree G W),
    S.IsCocompact ∧ S.HasFGStab ∧ Dominates S T

/-- A finitely generated subgroup `H ≤ G` acting on a tree `T` has a cocompact `H`-invariant
subtree `S`, and the inclusion `S ↪ T` is a domination map over `H.subtype`. -/
def CocompactSubtree (G : Type u) [Group G] {V : Type u} [MulAction G V]
    (T : GTree G V) : Prop :=
  ∀ (H : Subgroup G), H.FG →
    ∃ (W : Type u) (_ : MulAction H W) (S : GTree H W),
      S.IsCocompact ∧ DominatesOver H.subtype S T

/-- **Structure theorem for groups acting on trees, finitely presented form.**
If `G` acts cocompactly on a tree `T` with finitely generated edge stabilizers and finitely
presented vertex stabilizers, then `G` is finitely presented: split `G` along `T` (a finite
graph of groups with vertex groups the vertex stabilizers), and a finite graph of groups
with finitely presented vertex groups and finitely generated edge groups has a finite
presentation. -/
def BassSerreFinitelyPresented (G : Type u) [Group G] {V : Type u} [MulAction G V]
    (T : GTree G V) : Prop :=
  T.IsCocompact → T.HasFGEdgeStab →
  (∀ v : V, Group.IsFinitelyPresented (T.vertexStab v)) → Group.IsFinitelyPresented G

/-- **The descent step in the proof of JL Theorem 4.4.**  Let `π : H ↠ G` be a surjection
with `ker π^{ab} ⊗_ℤ k = 0`.  Suppose `T` is a cocompact `G`-tree which is `π`-dominated by
a cocompact `H`-tree `S'` with finitely generated vertex and edge stabilizers.  Then `T` is
dominated by a cocompact `G`-tree with finitely generated vertex and edge stabilizers.

This is the passage from the `H`-tree produced by `DunwoodyResolution` to a `G`-tree in the
proof of JL Theorem 4.4: one forms `S'/⟨⟨N ∩ H_1, …, N ∩ H_n⟩⟩`, where `N = ker π` and the
`H_i` are vertex stabilizers of `S'`; by Serre's structure theorem (JL Lemma 4.1) this is a
tree for `Q = H/⟨⟨N_i⟩⟩`; the image of `N` in `Q` acts freely on it, hence is free, and has
vanishing `k`-abelianization, hence is trivial; so `Q = G`. -/
def FP2TreePromotion (k : Type u) [CommRing k] : Prop :=
  ∀ (G : Type u) [Group G] (H : Type u) [Group H] (π : H →* G),
    Function.Surjective π → AbelianizationTensorVanishes k π.ker →
    ∀ {V : Type u} [MulAction G V] (T : GTree G V), T.IsCocompact →
    ∀ {W : Type u} [MulAction H W] (S' : GTree H W), S'.IsCocompact → S'.HasFGStab →
      DominatesOver π S' T →
      ∃ (X : Type u) (_ : MulAction G X) (S : GTree G X),
        S.IsCocompact ∧ S.HasFGStab ∧ Dominates S T


/-- `DunwoodyResolution` for every group in the universe of the anchor `X` (the anchor only
serves to fix the universe). -/
def DunwoodyResolutionAll (X : Type u) : Prop :=
  ∀ (G : Type u) [Group G] {V : Type u} [MulAction G V] (T : GTree G V),
    DunwoodyResolution G T

/-- `BassSerreFinitelyPresented` for every group in the universe of the anchor `X`. -/
def BassSerreFinitelyPresentedAll (X : Type u) : Prop :=
  ∀ (G : Type u) [Group G] {V : Type u} [MulAction G V] (T : GTree G V),
    BassSerreFinitelyPresented G T


/-- **Serre, *Trees*, §5 = JL Lemma 4.1, in the form used by the proof of JL Theorem 4.4.**
Let `S'` be an `H`-tree, `A` a finite set of vertices meeting every `H`-orbit of vertices,
and for each `v ∈ A` a subgroup `N v ≤ S'.vertexStab v`.  Let `K` be the normal closure of
the subgroups `N v`.  Then there is a `Q = H ⧸ K`-tree `S` with a surjection `g : W → X` of
vertex sets which is equivariant over `H → H ⧸ K`, which reflects adjacency *downwards*
(clause `lift`: every edge of `S` comes from an edge of `S'`), for which the *fibres* of `g`
are exactly the `K`-orbits (clause `fibre`), and whose vertex stabilizers are the images of
the corresponding vertex stabilizers of `S'` (clause `stab`).  `S` is cocompact and has
finitely generated stabilizers whenever `S'` does.

The argument `Y` is only a universe anchor: the statement is about all groups in the
universe of `Y`.

This is the construction of Serre §5 in the guise of JL Lemma 4.1: the normal closure of
subgroups generated by elliptic elements acts with tree quotient `S'/K`, whose vertex set is
the set of `K`-orbits of vertices of `S'` (whence `g = Quotient.mk''` and `fibre`), whose
edges are the `K`-orbits of edges of `S'` (whence `lift`); that the quotient is cocompact and
has finitely generated stabilizers is the bookkeeping of JL's proof of Theorem 4.4 ("the edge
stabilisers are conjugates of quotients of the edge stabilisers of the `H`-tree `S'`").
Owner: node N12 ("G-trees and quotient graphs", "JL Lemma 4.1"). -/
def SerreQuotientTree (Y : Type u) : Prop :=
  ∀ (H : Type u) [Group H] {W : Type u} [MulAction H W] (S' : GTree H W)
    (A : Finset W) (N : (w : W) → w ∈ A → Subgroup H)
    (hN : ∀ (w : W) (hw : w ∈ A), N w hw ≤ S'.vertexStab w)
    (hA : ∀ w : W, ∃ h : H, h • w ∈ A)
    (K : Subgroup H) [K.Normal]
    (hK : K = Subgroup.normalClosure (⋃ (w : W) (hw : w ∈ A), (N w hw : Set H)))
    (hc : S'.IsCocompact) (hfg : S'.HasFGStab),
    ∃ (X : Type u) (_ : MulAction (H ⧸ K) X) (S : GTree (H ⧸ K) X) (g : W → X)
      (hg : Function.Surjective g),
      S.IsCocompact ∧ S.HasFGStab ∧
      -- equivariance of the quotient map
      (∀ (h : H) (w : W), g (h • w) = QuotientGroup.mk' K h • g w) ∧
      -- (`lift`) every edge of the quotient comes from an edge of `S'`
      (∀ ⦃x y : X⦄, S.Adj x y → ∃ u v : W, S'.Adj u v ∧ g u = x ∧ g v = y) ∧
      -- (`fibre`) the fibres of `g` are the `K`-orbits
      (∀ u v : W, g u = g v ↔ ∃ k : K, (k : H) • u = v) ∧
      -- (`stab`) vertex stabilizers of the quotient are images of vertex stabilizers
      (∀ x : X,
        S.vertexStab x = (S'.vertexStab (Function.surjInv hg x)).map (QuotientGroup.mk' K))

/-- **Freeness criteria for group actions on trees** (Bass–Serre; node N12).

Two statements, both classical:

* (`free`) a group acting on a tree with trivial vertex stabilizers **and without inversions**
  is free.  The no-inversion hypothesis is *necessary*: `ZMod 2` acting on a single edge by
  swapping its endpoints has trivial vertex stabilizers and is not free
  (`Submission/Work/ORBassSerre/Assembly/freeOnTreeIsFree_of_noInversions.lean`).
* (`quotient`) the quotient form actually needed by the descent step of JL Theorem 4.4: if
  `G` acts on a tree without inversions and `K` is the normal closure of the vertex
  stabilizers, then `G ⧸ K` is free.  Without inversions the setwise stabilizer of an edge is
  its pointwise stabilizer, so `K` contains every edge stabilizer too, and `G ⧸ K` is the
  fundamental group of the quotient graph of `S` — a graph with trivial vertex *and* edge
  groups — hence free.  This is the statement Serre's §I.5 structure theorem gives; see
  `RESOLUTION_PLAN_2.md`.  Note that the hypothesis on `K` cannot be relaxed to "`K` contains
  every vertex stabilizer": `ℤ` acting on the line by translation by `2` has trivial vertex
  stabilizers, and `ℤ ⧸ 2ℤ` is not free.

Owner: node N12. -/
def FreeOnTreeIsFree (Y : Type u) : Prop :=
  (∀ (G : Type u) [Group G] {V : Type u} [MulAction G V] (S : GTree G V),
      (∀ v : V, S.vertexStab v = ⊥) →
      (∀ (g : G) ⦃u v : V⦄, S.Adj u v → g • u = v → g • v = u → g = 1) →
      ∃ (α : Type u), Nonempty (G ≃* FreeGroup α)) ∧
    (∀ (G : Type u) [Group G] {V : Type u} [MulAction G V] (S : GTree G V)
      (K : Subgroup G) [K.Normal],
      (∀ (g : G) ⦃u v : V⦄, S.Adj u v → g • u = v → g • v = u → g = 1) →
      (K = Subgroup.normalClosure (⋃ v : V, (S.vertexStab v : Set G))) →
      ∃ (α : Type u), Nonempty ((G ⧸ K) ≃* FreeGroup α))

/-- **The partial subdivision service of node N12.**  For a `G`-tree `T` and a `G`-invariant
set `R` of edges of `T`, the graph obtained by subdividing exactly the edges in `R` (and keeping
the others as edges between old vertices) is again a `G`-tree: an old vertex is joined to the
midpoint of each marked edge containing it, two old vertices are joined exactly along the
unmarked edges, no two midpoints are joined, and `G` acts by mapping old vertices to old
vertices and midpoints to midpoints.  It is cocompact and has finitely generated stabilizers
whenever `T` does.

This is the missing tree construction of the descent step of JL Theorem 4.4, where one has to
subdivide exactly the edges of `S'` that the domination map collapses: those are the edges that
elements of `N = ker π` can invert, and subdividing them moves those inversions into the vertex
stabilizers (so that they are absorbed by the normal closure `K` of the vertex stabilizers),
while the edges that are *not* collapsed stay untouched, so that the domination map to `T`
still exists (a midpoint of an edge that some `h` inverts with non-collapsed image would have to
be mapped to a `π h`-fixed vertex of `T`, which need not exist).

Owner: node N12. -/
def PartialSubdivision (Y : Type u) : Prop :=
  ∀ (G : Type u) [Group G] (V : Type u) [MulAction G V] (R : EdgeInv G V),
    R.tree.IsCocompact → R.tree.HasFGStab →
    ∃ (S : GTree G (PSubV R)),
      (∀ u v : V, S.Adj (Sum.inl u) (Sum.inl v) ↔ R.tree.Adj u v ∧ s(u, v) ∉ R.edges) ∧
      (∀ (u : V) (e : {e : Sym2 V // e ∈ R.edges}),
        S.Adj (Sum.inl u) (Sum.inr e) ↔ u ∈ (e : Sym2 V)) ∧
      (∀ (e e' : {e : Sym2 V // e ∈ R.edges}), ¬ S.Adj (Sum.inr e) (Sum.inr e')) ∧
      (∀ (g : G) (v : V), g • (Sum.inl v : PSubV R) = Sum.inl (g • v)) ∧
      (∀ (g : G) (e : {e : Sym2 V // e ∈ R.edges}),
        ∃ e' : {e : Sym2 V // e ∈ R.edges}, g • (Sum.inr e : PSubV R) = Sum.inr e') ∧
      (∀ v : V, S.vertexStab (Sum.inl v) = R.tree.vertexStab v) ∧
      (∀ e : {e : Sym2 V // e ∈ R.edges},
        S.vertexStab (Sum.inr e) =
          {g : G | Sym2.map (fun v : V => g • v) (e : Sym2 V) = (e : Sym2 V)}) ∧
      S.IsCocompact ∧ S.HasFGStab

/-- **The tree-construction services of node N12 used by the descent step of JL Theorem 4.4**:
Serre's §5 quotient-tree construction (`SerreQuotientTree`) together with the partial
subdivision of a tree along an invariant set of edges (`PartialSubdivision`).  Both are
constructions of `G`-trees out of a given `G`-tree; they are bundled under this name so that
the signatures of `Theorem44.lean`, `Theorem45.lean` and `Corollaries.lean` stay unchanged.
Each conjunct is a theorem of node N12, recorded unconditionally in `Interface.lean`. -/
def QuotientTreeByNormalClosureOfElliptic (Y : Type u) : Prop :=
  SerreQuotientTree Y ∧ PartialSubdivision Y

end Work.ORDunwoody
