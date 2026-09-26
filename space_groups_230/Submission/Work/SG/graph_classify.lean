import Mathlib
import Submission.Work.SG.SellingDefs

namespace Work.SG

/-! ### Supporting material for `Work.SG.graph_classify`

The finite classification of connected graphs on four vertices is handled as follows.

* `gcEdgeOf : Fin 6 → Fin 4 × Fin 4` enumerates the six pairs `p` of `Fin 4` with `p.1 < p.2`.
* `gcEdgeSetOf b` decodes a boolean vector `b : Fin 6 → Bool` into the corresponding edge set.
* `gcEnc S` re-encodes a finite edge set all of whose elements are in normal form.
* `gcConn S` is a decidable (finitistic) formulation of connectivity: no nonempty proper
  subset of the vertex set is crossed by no edge.
* `gcIsConnGraph_iff` identifies `gcConn` with `IsConnGraph`.
* `gcDecide` checks the 64 possible edge sets by `decide`: every connected one is a relabelling
  of one of the six `sellingGraph i`. -/

namespace GraphClassify

/-- The six pairs `(a,b)` of vertices of `Fin 4` with `a < b`, in a fixed order. -/
abbrev gcEdgeOf : Fin 6 → Fin 4 × Fin 4 := ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

/-- Decoding of a boolean vector `b : Fin 6 → Bool` into an edge set: the pairs `gcEdgeOf i`
with `b i = true`. -/
abbrev gcEdgeSetOf (b : Fin 6 → Bool) : Finset (Fin 4 × Fin 4) :=
  (Finset.univ.filter (fun i => b i = true)).image gcEdgeOf

/-- Encoding of an edge set: `i` is kept iff `gcEdgeOf i` belongs to the set. -/
abbrev gcEnc (S : Finset (Fin 4 × Fin 4)) : Fin 6 → Bool := fun i => decide (gcEdgeOf i ∈ S)

/-- Decidable connectivity: every nonempty proper subset of vertices is crossed by an edge. -/
abbrev gcConn (S : Finset (Fin 4 × Fin 4)) : Prop :=
  ∀ T : Finset (Fin 4), T.Nonempty → T ≠ Finset.univ →
    ∃ p ∈ S, (p.1 ∈ T ∧ p.2 ∉ T) ∨ (p.1 ∉ T ∧ p.2 ∈ T)

/-- A pair of vertices lies in the range of `gcEdgeOf` exactly when it is in normal form. -/
theorem mem_range_gcEdgeOf (p : Fin 4 × Fin 4) : p ∈ Set.range gcEdgeOf ↔ p.1 < p.2 := by
  obtain ⟨a, b⟩ := p
  fin_cases a <;> fin_cases b <;> decide

/-- Encoding followed by decoding is the identity on edge sets in normal form. -/
theorem gcEdgeSetOf_gcEnc (S : Finset (Fin 4 × Fin 4)) (hS : ∀ p ∈ S, p.1 < p.2) :
    gcEdgeSetOf (gcEnc S) = S := by
  ext x
  simp only [gcEdgeSetOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, hix⟩
    rw [← hix]
    exact of_decide_eq_true hi
  · intro hx
    obtain ⟨i, hi⟩ := (mem_range_gcEdgeOf x).mpr (hS x hx)
    exact ⟨i, decide_eq_true (hi ▸ hx), hi⟩

/-- `toFinset` of a relabelled edge list is the image of the edge set under the relabelling
`p ↦ nrmEdge (σ p.1) (σ p.2)`. -/
theorem toFinset_permE (σ : Equiv.Perm (Fin 4)) (L : List (Fin 4 × Fin 4)) :
    (permE σ L).toFinset = L.toFinset.image (fun p => nrmEdge (σ p.1) (σ p.2)) := by
  ext x
  simp [permE, List.mem_toFinset, Finset.mem_image]

/-- `gcConn` is `IsConnGraph`, transported to the underlying finite set of edges. -/
theorem isConnGraph_iff_gcConn (E : List (Fin 4 × Fin 4)) :
    IsConnGraph E ↔ gcConn E.toFinset := by
  constructor
  · intro hc
    rw [gcConn]
    intro T hne hnu
    by_contra hex
    simp only [not_exists, not_and] at hex
    obtain ⟨a, ha⟩ := hne
    have hb : ∃ b, b ∉ T := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hnu (Finset.eq_univ_of_forall h)
    obtain ⟨b, hbT⟩ := hb
    have hcl : ∀ x ∈ T, ∀ y, ((x, y) ∈ E ∨ (y, x) ∈ E) → y ∈ T := by
      intro x hx y hxy
      by_contra hy
      rcases hxy with h | h
      · exact hex (x, y) (List.mem_toFinset.mpr h) (Or.inl ⟨hx, hy⟩)
      · exact hex (y, x) (List.mem_toFinset.mpr h) (Or.inr ⟨hy, hx⟩)
    have key : ∀ y, Relation.ReflTransGen (fun x y => (x, y) ∈ E ∨ (y, x) ∈ E) a y → y ∈ T := by
      intro y hy
      induction hy with
      | refl => exact ha
      | tail hab hbc ih => exact hcl _ ih _ hbc
    exact hbT (key b (hc a b))
  · intro hS a b
    classical
    set T : Finset (Fin 4) :=
      Finset.univ.filter (fun x => Relation.ReflTransGen (fun x y => (x, y) ∈ E ∨ (y, x) ∈ E) a x)
      with hT
    have haT : a ∈ T := by
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Relation.ReflTransGen.refl
    have hclosed : ∀ x ∈ T, ∀ y, (x, y) ∈ E ∨ (y, x) ∈ E → y ∈ T := by
      intro x hx y hxy
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx.tail hxy
    have hTuniv : T = Finset.univ := by
      by_contra hne
      obtain ⟨p, hpS, hcr⟩ := hS T ⟨a, haT⟩ hne
      rcases hcr with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
      · exact hp2 (hclosed p.1 hp1 p.2 (Or.inl (List.mem_toFinset.mp hpS)))
      · exact hp1 (hclosed p.2 hp2 p.1 (Or.inr (List.mem_toFinset.mp hpS)))
    have : b ∈ T := by rw [hTuniv]; exact Finset.mem_univ b
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this

/-- The finite check: every connected edge set on `Fin 4` (in normal form) is a relabelling of
one of the six Selling support graphs.  The finite types `Fin 6 → Bool` (64 edge sets),
`Equiv.Perm (Fin 4)` (24 relabellings) and `Fin 6` (6 graphs) are enumerated by the kernel. -/
theorem gcDecide (b : Fin 6 → Bool) (hb : gcConn (gcEdgeSetOf b)) :
    ∃ τ : Equiv.Perm (Fin 4), ∃ i : Fin 6,
      (sellingGraph i).toFinset.image (fun p => nrmEdge (τ p.1) (τ p.2)) = gcEdgeSetOf b :=
  (by decide : ∀ b : Fin 6 → Bool, gcConn (gcEdgeSetOf b) →
    ∃ τ : Equiv.Perm (Fin 4), ∃ i : Fin 6,
      (sellingGraph i).toFinset.image (fun p => nrmEdge (τ p.1) (τ p.2)) = gcEdgeSetOf b) b hb

end GraphClassify

/-- Every connected graph on the four superbase vertices whose edges are listed in normal form
(`p.1 < p.2`) is a relabelling of one of the six Selling support graphs.

Route: the six `sellingGraph i` are K₄, K₄ − 01, the 4-cycle, the paw, the path and the star,
which are exactly the six isomorphism classes of connected graphs on 4 vertices.  So it suffices
to check the 38 connected labelled graphs on `Fin 4` (edges from the 6 pairs, all in normal form):
for each of them exhibit `τ` and `i`.  A `decide`-free way is a case analysis on the number of
edges (3 edges: only `P₄` and `K₁,₃` are connected; 4 edges: `C₄`, paw; 5 edges: `K₄ − e`; 6 edges:
`K₄`), each producing an explicit `τ`.  Since `E` is an arbitrary list, you may prefer to first
replace `E` by its `toFinset` (deduplicate) and argue on the finite set of possible edge sets.
`(permE τ (sellingGraph i)).toFinset = E.toFinset` is an equality of finite sets of normal-form
pairs, so it is decidable and `decide` on the 64 possible edge sets is acceptable. -/
theorem graph_classify (E : List (Fin 4 × Fin 4)) (hd : ∀ p ∈ E, p.1 < p.2) (hc : IsConnGraph E) :
    ∃ τ : Equiv.Perm (Fin 4), ∃ i : Fin 6, (permE τ (sellingGraph i)).toFinset = E.toFinset := by
  have hSrange : ∀ p ∈ E.toFinset, p.1 < p.2 := fun p hp => hd p (List.mem_toFinset.mp hp)
  have hdec : GraphClassify.gcEdgeSetOf (GraphClassify.gcEnc E.toFinset) = E.toFinset :=
    GraphClassify.gcEdgeSetOf_gcEnc _ hSrange
  have hconn : GraphClassify.gcConn (GraphClassify.gcEdgeSetOf (GraphClassify.gcEnc E.toFinset)) := by
    rw [hdec]
    exact (GraphClassify.isConnGraph_iff_gcConn E).mp hc
  obtain ⟨τ, i, hi⟩ := GraphClassify.gcDecide (GraphClassify.gcEnc E.toFinset) hconn
  exact ⟨τ, i, by rw [GraphClassify.toFinset_permE, hi, hdec]⟩

end Work.SG
