/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The subdivided Cayley complex `Λ''` of the Dunwoody construction (step (G2))

This file builds the *source* complex of Dunwoody's pattern construction:

* `Λ` is the Cayley complex of a finite presentation `P` of `G` (`Cayley/Complex.lean`), a
  simply connected 2-complex with a free cocompact `G`-action;
* `Λ'` is the subdivision of `Λ` in which the generator edge `(c, x)` is replaced by a path of
  length `L x` (the geodesic data `GeoData`), so that the `G`-equivariant map `φ : Λ' → T`
  becomes *edge-to-edge*;
* `Λ''` is the subdivision of `Λ'` at the midpoints of its edges.  The midpoints are the
  **pattern points**: `L = φ⁻¹(midpoints of the edges of T)`.

The vertices of `Λ''` split into

* **old vertices** `BaseV`: a group element `c` (the base point of the subdivision) or an
  interior point of a generator edge;
* **mid-vertices** `MidV`: the midpoint of a cell `(c, j, k)` of `Λ'`; these are the pattern
  points, and each carries the *label* `Sym2 V` of the edge of `T` that the cell maps onto.

A cell `(c, j, k)` of `Λ'` (a sub-edge of the generator edge `(j, true)` starting at `c`) runs
from `pos c j k` to `pos c j (k+1)`; when the generator is "collapsed" (`L (j,true) = 0`) the
whole generator edge is a single cell `plain c j` from `(c, ∗)` to `(c * genE (j,true), ∗)` with
no midpoint.

## Implementation notes

Following `DESIGN_N13.md` §7c, a cell of `Λ'` is indexed by its *canonical* representation: the
sub-edge `k` of the **positive** letter `(j, true)`.  The negative letter `(j, false)` at `c` is
the reverse of the positive letter at `c * (genE (j,true))⁻¹`, so its sub-edges are the same
cells with the index reversed; this removes the need for a quotient of the vertex type by the
reversal relation.

Nothing here depends on the simple connectivity of `Λ`: the side functions of the wall system
are built from `φ` (the label of a region in `T`) and not from passage counts — see
`DESIGN_N13.md`.
-/
import Mathlib
import Submission.Work.ORDunwoody.Cayley.GeoData
import Submission.Work.ORDunwoody.Tracks.even_edges_count

open scoped Sym2

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-! ## The vertices of `Λ''` -/

/-- The interior points of the generator edge `(j,true)`: `L (j,true) - 1` of them. -/
abbrev InnerIdx (D : GeoData T t₀ P) (j : Fin P.n) : Type := Fin (D.L (j, true) - 1)

/-- The vertex orbits of `Λ''` that are *not* pattern points: the base point, and the interior
points of the generator edges. -/
abbrev BaseV₀ (D : GeoData T t₀ P) : Type := Unit ⊕ (Σ j : Fin P.n, InnerIdx D j)

/-- The old (non-pattern) vertices of `Λ''`: `G × BaseV₀`. -/
abbrev BaseV (D : GeoData T t₀ P) : Type u := G × BaseV₀ D

/-- The orbits of pattern points (midpoints of the cells of `Λ'`): a generator index and the
index of the cell along that generator edge. -/
structure MidIdx (D : GeoData T t₀ P) where
  /-- The generator-with-sign, always the positive one. -/
  j : Fin P.n
  /-- The index of the cell along the generator edge. -/
  k : Fin (D.L (j, true))

/-- The pattern points of `Λ''`: the midpoints of the cells of `Λ'`. -/
abbrev MidV (D : GeoData T t₀ P) : Type u := G × MidIdx D

/-- The vertices of `Λ''`. -/
abbrev Vertex (D : GeoData T t₀ P) : Type u := BaseV D ⊕ MidV D

/-- Whether a vertex of `Λ''` is a pattern point. -/
def Vertex.isMid : Vertex D → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

@[simp] theorem Vertex.isMid_inl (v : BaseV D) :
    Vertex.isMid (Sum.inl v : Vertex D) = false := rfl

@[simp] theorem Vertex.isMid_inr (v : MidV D) :
    Vertex.isMid (Sum.inr v : Vertex D) = true := rfl

/-! ## The `G`-action

The action of `G` on `Λ''` is induced by the free action on the first factor; it is free, and
this is what makes the stabilisers of the tracks and the regions finitely generated. -/

instance instMulActionBaseV : MulAction G (BaseV D) where
  smul g p := (g * p.1, p.2)
  one_smul p := Prod.ext (one_mul p.1) rfl
  mul_smul g h p := Prod.ext (mul_assoc g h p.1) rfl

@[simp] theorem baseV_smul (g : G) (p : BaseV D) : g • p = (g * p.1, p.2) := rfl

instance instMulActionMidV : MulAction G (MidV D) where
  smul g p := (g * p.1, p.2)
  one_smul p := Prod.ext (one_mul p.1) rfl
  mul_smul g h p := Prod.ext (mul_assoc g h p.1) rfl

@[simp] theorem midV_smul (g : G) (p : MidV D) : g • p = (g * p.1, p.2) := rfl

instance instMulActionVertex : MulAction G (Vertex D) where
  smul g := Sum.map (fun p => g • p) (fun p => g • p)
  one_smul v := by
    cases v with
    | inl p => exact congrArg Sum.inl (one_smul G p)
    | inr p => exact congrArg Sum.inr (one_smul G p)
  mul_smul g h v := by
    cases v with
    | inl p => exact congrArg Sum.inl (mul_smul g h p)
    | inr p => exact congrArg Sum.inr (mul_smul g h p)

@[simp] theorem vertex_smul_inl (g : G) (p : BaseV D) :
    g • (Sum.inl p : Vertex D) = Sum.inl (g • p) := rfl

@[simp] theorem vertex_smul_inr (g : G) (p : MidV D) :
    g • (Sum.inr p : Vertex D) = Sum.inr (g • p) := rfl

/-- The action of `G` on `Λ''` is free. -/
theorem vertex_smul_eq_self {g : G} {v : Vertex D} (h : g • v = v) : g = 1 := by
  cases v with
  | inl p =>
      have h' : g • p = p := Sum.inl.inj h
      have h2 : g * p.1 = p.1 := congrArg Prod.fst h'
      calc g = g * p.1 * p.1⁻¹ := by group
        _ = p.1 * p.1⁻¹ := by rw [h2]
        _ = 1 := by group
  | inr p =>
      have h' : g • p = p := Sum.inr.inj h
      have h2 : g * p.1 = p.1 := congrArg Prod.fst h'
      calc g = g * p.1 * p.1⁻¹ := by group
        _ = p.1 * p.1⁻¹ := by rw [h2]
        _ = 1 := by group

/-! ## Positions along a generator edge and the cells of `Λ'` -/

/-- The vertex of `Λ''` at position `i` along the generator edge `(j,true)` based at `c`.
Position `0` is the base point `c`, position `L` is `c * genE (j,true)`, and the intermediate
positions are the interior points of the edge.  (Only positions `0 ≤ i ≤ L` are meaningful;
for a *collapsed* generator, `L = 0`, the single edge is handled by `Step.plain`.) -/
def pos (D : GeoData T t₀ P) (c : G) (j : Fin P.n) : ℕ → BaseV D
  | 0 => (c, Sum.inl ())
  | (i + 1) =>
      if h : i + 1 < D.L (j, true) then (c, Sum.inr ⟨j, ⟨i, by omega⟩⟩)
      else (c * CayV.genE P (j, true), Sum.inl ())

@[simp] theorem pos_zero (D : GeoData T t₀ P) (c : G) (j : Fin P.n) :
    pos D c j 0 = (c, Sum.inl ()) := rfl

theorem pos_succ_of_lt (D : GeoData T t₀ P) (c : G) (j : Fin P.n) {i : ℕ}
    (h : i + 1 < D.L (j, true)) :
    pos D c j (i + 1) = (c, Sum.inr ⟨j, ⟨i, by omega⟩⟩) := by
  rw [pos, dif_pos h]

theorem pos_succ_of_not_lt (D : GeoData T t₀ P) (c : G) (j : Fin P.n) {i : ℕ}
    (h : ¬ (i + 1 < D.L (j, true))) :
    pos D c j (i + 1) = (c * CayV.genE P (j, true), Sum.inl ()) := by
  rw [pos, dif_neg h]

/-- Positions carry the action of `G`. -/
theorem pos_smul (D : GeoData T t₀ P) (g c : G) (j : Fin P.n) :
    ∀ i : ℕ, pos D (g * c) j i = g • pos D c j i
  | 0 => by rw [pos_zero, pos_zero, baseV_smul]
  | (i + 1) => by
      rcases lt_or_ge (i + 1) (D.L (j, true)) with h | h
      · rw [pos_succ_of_lt D (g * c) j h, pos_succ_of_lt D c j h]; simp [baseV_smul]
      · rw [pos_succ_of_not_lt D (g * c) j (by omega), pos_succ_of_not_lt D c j (by omega)]
        simp [baseV_smul, mul_assoc]

/-- A cell of `Λ'`: the sub-edge number `k` of the generator edge `(j,true)` based at `c`.  These
are exactly the cells that carry a pattern point; a generator edge with `L (j,true) = 0` has no
such cell (it is a single collapsed edge, see `Step.plain`). -/
structure Cell (D : GeoData T t₀ P) where
  /-- The base point of the cell. -/
  c : G
  /-- The generator-with-sign, always the positive one. -/
  j : Fin P.n
  /-- The index of the cell along the generator edge. -/
  k : Fin (D.L (j, true))

instance instMulActionCell : MulAction G (Cell D) where
  smul g e := ⟨g * e.c, e.j, e.k⟩
  one_smul e := congrArg (fun x => (⟨x, e.j, e.k⟩ : Cell D)) (one_mul e.c)
  mul_smul g h e := congrArg (fun x => (⟨x, e.j, e.k⟩ : Cell D)) (mul_assoc g h e.c)

@[simp] theorem cell_smul (g : G) (e : Cell D) : g • e = ⟨g * e.c, e.j, e.k⟩ := rfl

/-- The base point of a cell. -/
def Cell.src (e : Cell D) : BaseV D := pos D e.c e.j e.k

/-- The far endpoint of a cell. -/
def Cell.tgt (e : Cell D) : BaseV D := pos D e.c e.j (e.k + 1)

/-- The pattern point of a cell: its midpoint. -/
def Cell.mid (e : Cell D) : MidV D := ⟨e.c, ⟨e.j, e.k⟩⟩

theorem Cell.src_smul (g : G) (e : Cell D) : (g • e).src = g • e.src := by
  simp only [Cell.src, cell_smul, pos_smul]

theorem Cell.tgt_smul (g : G) (e : Cell D) : (g • e).tgt = g • e.tgt := by
  simp only [Cell.tgt, cell_smul, pos_smul]

theorem Cell.mid_smul (g : G) (e : Cell D) : (g • e).mid = g • e.mid := rfl

/-- The label of a cell: the (unordered pair of endpoints of the) edge of `T` that the cell
maps onto.  Two pattern points lie in the same track precisely when their labels agree. -/
def Cell.label (e : Cell D) : Sym2 V :=
  s(e.c • D.geo (e.j, true) ⟨e.k, by have := e.k.isLt; omega⟩,
    e.c • D.geo (e.j, true) ⟨e.k + 1, by have := e.k.isLt; omega⟩)

/-- The label of a pattern point, i.e. of the cell it is the midpoint of. -/
def MidV.label (p : MidV D) : Sym2 V :=
  s(p.1 • D.geo (p.2.j, true) ⟨p.2.k, by have := p.2.k.isLt; omega⟩,
    p.1 • D.geo (p.2.j, true) ⟨p.2.k + 1, by have := p.2.k.isLt; omega⟩)

theorem Cell.label_eq_MidV_label (e : Cell D) : e.label = (e.mid).label := rfl

/-- The cell's label is a genuine edge of `T`. -/
theorem Cell.label_mem_edgeSet (e : Cell D) : e.label ∈ T.graph.edgeSet :=
  (SimpleGraph.mem_edgeSet T.graph).mpr (T.smul_adj e.c (D.geo_adj (e.j, true) e.k))

/-! ## The steps of a boundary walk -/

/-- A step of a boundary walk of `Λ''`: either the traversal of a cell (which visits the cell's
pattern point) or the traversal of a collapsed generator edge (which visits none). -/
inductive Step (D : GeoData T t₀ P) : Type u
  /-- The traversal of a cell: visits the pattern point at its midpoint. -/
  | crossed (e : Cell D) : Step D
  /-- The traversal of a collapsed generator edge: `L (j,true) = 0`. -/
  | plain (c : G) (j : Fin P.n) : Step D

namespace Step

variable {D : GeoData T t₀ P}

/-- The pattern point visited by a step, if any. -/
def mid? : Step D → Option (MidV D)
  | .crossed e => some e.mid
  | .plain _ _ => none

/-- The starting vertex of a step. -/
def src : Step D → BaseV D
  | .crossed e => e.src
  | .plain c j => (c, Sum.inl ())

/-- The terminal vertex of a step. -/
def tgt : Step D → BaseV D
  | .crossed e => e.tgt
  | .plain c j => (c * CayV.genE P (j, true), Sum.inl ())

@[simp] theorem mid?_crossed (e : Cell D) : (Step.crossed e).mid? = some e.mid := rfl

@[simp] theorem mid?_plain (c : G) (j : Fin P.n) : (Step.plain (D := D) c j).mid? = none := rfl

@[simp] theorem src_plain (c : G) (j : Fin P.n) :
    (Step.plain (D := D) c j).src = (c, Sum.inl ()) := rfl

@[simp] theorem tgt_plain (c : G) (j : Fin P.n) :
    (Step.plain (D := D) c j).tgt = (c * CayV.genE P (j, true), Sum.inl ()) := rfl

@[simp] theorem src_crossed (e : Cell D) : (Step.crossed e).src = e.src := rfl

@[simp] theorem tgt_crossed (e : Cell D) : (Step.crossed e).tgt = e.tgt := rfl

/-- Left-translation of a step by a group element. -/
def smul (e : Step D) (g : G) : Step D :=
  match e with
  | .crossed e => .crossed (g • e)
  | .plain c j => .plain (g * c) j

@[simp] theorem smul_crossed (g : G) (e : Cell D) :
    (Step.crossed e).smul g = .crossed (g • e) := rfl

@[simp] theorem smul_plain (g c : G) (j : Fin P.n) :
    (Step.plain (D := D) c j).smul g = .plain (g * c) j := rfl

theorem src_smul (g : G) (e : Step D) : (e.smul g).src = g • e.src := by
  cases e with
  | crossed e => simp only [smul_crossed, src_crossed, baseV_smul]; exact Cell.src_smul g e
  | plain c j => simp [baseV_smul]

theorem tgt_smul (g : G) (e : Step D) : (e.smul g).tgt = g • e.tgt := by
  cases e with
  | crossed e => simp only [smul_crossed, tgt_crossed, baseV_smul]; exact Cell.tgt_smul g e
  | plain c j => simp [mul_assoc]

theorem mid?_smul (g : G) (e : Step D) : (e.smul g).mid? = (e.mid?).map (fun p => g • p) := by
  cases e with
  | crossed e => simp only [smul_crossed, mid?_crossed, Cell.mid_smul, Option.map_some]
  | plain c j => rfl

end Step

/-! ## The 1-skeleton of `Λ''`

The vertices of `Λ''` are joined by an edge when they are the two halves of a cell, or the two
ends of a collapsed generator edge.  This is the graph on which the tracks and the regions live,
and on which the relevant stabilisers act freely. -/

/-- The elementary step relation of `Λ''`: the two halves of a cell (an old vertex and the
pattern point at its midpoint), or a collapsed generator edge (`L (j,true) = 0`). -/
def StepRel (v w : Vertex D) : Prop :=
  (∃ e : Cell D,
      (v = Sum.inl e.src ∧ w = Sum.inr e.mid) ∨ (v = Sum.inr e.mid ∧ w = Sum.inl e.tgt))
    ∨ (∃ (a : G) (j : Fin P.n), D.L (j, true) = 0 ∧ v = Sum.inl (a, Sum.inl ()) ∧
        w = Sum.inl (a * CayV.genE P (j, true), Sum.inl ()))

/-- **The 1-skeleton of `Λ''`.** -/
def graph : SimpleGraph (Vertex D) := SimpleGraph.fromRel StepRel

theorem graph_adj_iff {v w : Vertex D} :
    (graph (D := D)).Adj v w ↔ v ≠ w ∧ (StepRel v w ∨ StepRel w v) :=
  SimpleGraph.fromRel_adj StepRel v w

/-- The elementary step relation is `G`-equivariant. -/
theorem StepRel_smul (g : G) {v w : Vertex D} (h : StepRel v w) : StepRel (g • v) (g • w) := by
  rcases h with ⟨e, h1 | h1⟩ | ⟨a, j, hL, h1, h2⟩
  · left
    refine ⟨g • e, Or.inl ⟨?_, ?_⟩⟩
    · rw [h1.1, vertex_smul_inl, Cell.src_smul]
    · rw [h1.2, vertex_smul_inr, Cell.mid_smul]
  · left
    refine ⟨g • e, Or.inr ⟨?_, ?_⟩⟩
    · rw [h1.1, vertex_smul_inr, Cell.mid_smul]
    · rw [h1.2, vertex_smul_inl, Cell.tgt_smul]
  · right
    refine ⟨g * a, j, hL, ?_, ?_⟩
    · rw [h1, vertex_smul_inl, baseV_smul]
    · rw [h2, vertex_smul_inl, baseV_smul, mul_assoc]

/-- The 1-skeleton is invariant under the action of `G`. -/
theorem graph_smul_adj (g : G) {v w : Vertex D} (h : (graph (D := D)).Adj v w) :
    (graph (D := D)).Adj (g • v) (g • w) := by
  obtain ⟨hne, hstep⟩ := (graph_adj_iff (D := D) (v := v) (w := w)).1 h
  refine (graph_adj_iff (D := D) (v := g • v) (w := g • w)).2 ⟨?_, ?_⟩
  · intro hc
    exact hne (by
      have := congrArg (fun z : Vertex D => g⁻¹ • z) hc
      simpa using this)
  · rcases hstep with hstep | hstep
    · exact Or.inl (StepRel_smul (D := D) g hstep)
    · exact Or.inr (StepRel_smul (D := D) g hstep)

end Work.ORDunwoody.Dunwoody
