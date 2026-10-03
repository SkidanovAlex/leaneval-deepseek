import Mathlib
import Submission.Work.ORHughesFree.Tree

/-!
# The number of edges of a finite rooted tree

`Tree` is the quotient of raw trees `MTree` by `Iso` (equality of the multisets of children,
recursively).  We define the number of edges `edge t` of a raw tree by structural recursion
(`edge (.node l) = l.length + ∑_{a ∈ l} edge a`), prove it is invariant under `Iso`, and descend
it to `Tree`.  The number of edges is the measure used to set up the recursive definition of the
well-order of [DHS04, Lemma 3.3], since the children of a node have strictly fewer edges.
-/

namespace Work.ORHughesFree

namespace MTree

/-- The number of edges of a raw tree. -/
def edge : MTree → ℕ
  | .node l => l.length + (l.map edge).sum

/-- The number of edges of a node is positive as soon as the node has a child. -/
theorem edge_pos_of_mem {c : MTree} {l : List MTree} (hc : c ∈ l) :
    MTree.edge c < MTree.edge (.node l) := by
  rw [MTree.edge]
  have hle : MTree.edge c ≤ (l.map MTree.edge).sum := by
    induction l with
    | nil => exact absurd hc (by simp)
    | cons d l ih =>
      rcases List.mem_cons.mp hc with rfl | hc
      · simp
      · have := ih hc
        simp only [List.map_cons, List.sum_cons]
        omega
  have hlen : 0 < l.length := List.length_pos_of_mem hc
  omega

/-- `edge` is invariant under `Iso`. -/
theorem edge_iso : ∀ {a b : MTree}, Iso a b → MTree.edge a = MTree.edge b := by
  intro a b h
  refine Iso.rec (motive_1 := fun a b _ => MTree.edge a = MTree.edge b)
    (motive_2 := fun l l' _ => (l.map MTree.edge).sum = (l'.map MTree.edge).sum ∧
      l.length = l'.length) ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro l l' hp ih
    obtain ⟨ih1, ih2⟩ := ih
    rw [MTree.edge, MTree.edge, ih1, ih2]
  · simp
  · intro x y l l' hx hp ihx ihp
    obtain ⟨ihp1, ihp2⟩ := ihp
    refine ⟨?_, by simp [ihp2]⟩
    simp only [List.map_cons, List.sum_cons, ihx, ihp1]
  · intro x y l
    refine ⟨?_, by simp⟩
    simp only [List.map_cons, List.sum_cons]
    ring
  · intro l; exact ⟨rfl, rfl⟩
  · intro l l' hp ih; exact ⟨ih.1.symm, ih.2.symm⟩
  · intro l l' l'' hp hp' ih ih'
    exact ⟨ih.1.trans ih'.1, ih.2.trans ih'.2⟩

/-- A raw tree with no edges is the one-vertex tree. -/
theorem edge_eq_zero {t : MTree} (h : MTree.edge t = 0) : t = MTree.node [] := by
  cases t with
  | node l =>
    rw [MTree.edge] at h
    have hl : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hl]

end MTree

namespace Tree

/-- The number of edges of a finite rooted tree. -/
noncomputable def edge : Tree → ℕ := Quotient.lift MTree.edge (fun _ _ h => MTree.edge_iso h)

theorem edge_mk (t : MTree) : edge (Quotient.mk'' t : Tree) = MTree.edge t := rfl

theorem edge_out (x : Tree) : MTree.edge (Quotient.out x) = edge x :=
  (edge_mk (Quotient.out x)).symm.trans (congrArg edge (Quotient.out_eq x))

/-- `edge` of the one-vertex tree `0` is `0`. -/
theorem edge_zero : edge (0 : Tree) = 0 := by
  have h : (0 : Tree) = (Quotient.mk'' (MTree.node []) : Tree) := rfl
  rw [h, edge_mk]
  simp [MTree.edge]

/-- A child of a tree has strictly fewer edges than the tree. -/
theorem edge_lt_of_mem_fam {a x : Tree} (ha : a ∈ fam x) : edge a < edge x := by
  -- `a ∈ fam x` means `a = mk c` for a raw child `c` of the representative of `x`
  unfold fam at ha
  rw [Multiset.mem_coe] at ha
  obtain ⟨c, hc, hca⟩ :=
    (List.mem_map (f := fun c : MTree => (Quotient.mk'' c : Tree))).mp ha
  rw [← hca, edge_mk, ← edge_out]
  obtain ⟨l, hl⟩ : ∃ l : List MTree, Quotient.out x = MTree.node l := by
    cases Quotient.out x with
    | node l => exact ⟨l, rfl⟩
  rw [hl] at hc ⊢
  simp only [MTree.children] at hc
  exact MTree.edge_pos_of_mem hc

/-- A tree with no edges is the one-vertex tree. -/
theorem edge_eq_zero {x : Tree} (h : edge x = 0) : x = 0 := by
  have h' : MTree.edge (Quotient.out x) = 0 := (edge_out x).trans h
  have h2 : Quotient.out x = MTree.node [] := MTree.edge_eq_zero h'
  have h3 : (Quotient.mk'' (Quotient.out x) : Tree) = Tree.zero := by rw [h2]; rfl
  exact (Quotient.out_eq x).symm.trans h3

end Tree

end Work.ORHughesFree
