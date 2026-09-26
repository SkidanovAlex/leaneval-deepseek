import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.SellingDefs

/-! ### The underlying undirected edge set of a list of ordered pairs

`edgeSet E` is the set of *unordered* pairs `{a,b}` spanned by the ordered pairs of the list `E`.
This is the right invariant to discuss `sellingVecs`, because the defining condition
`|x a − x b| ≤ 1` is symmetric in `a` and `b`.

This module is shared vocabulary; it contains no `sorry` and imports only `Mathlib` and
`Submission.Work.SG.SellingDefs`. -/

namespace Work.SG

/-- The underlying undirected edge set of a list of ordered pairs of superbase indices, as a
finite set of unordered pairs (`Sym2`). -/
def edgeSet (E : List (Fin 4 × Fin 4)) : Finset (Sym2 (Fin 4)) :=
  E.toFinset.image fun p => s(p.1, p.2)

theorem edgeSet_eq_image (E : List (Fin 4 × Fin 4)) :
    edgeSet E = E.toFinset.image (fun p => s(p.1, p.2)) := rfl

theorem mem_edgeSet {E : List (Fin 4 × Fin 4)} {z : Sym2 (Fin 4)} :
    z ∈ edgeSet E ↔ ∃ p, p ∈ E ∧ s(p.1, p.2) = z := by
  simp [edgeSet, List.mem_toFinset]

/-- The `Sym2`-class of an edge in normal form is the class of the edge itself. -/
theorem nrmEdge_sym2 (a b : Fin 4) : s((nrmEdge a b).1, (nrmEdge a b).2) = s(a, b) := by
  rcases nrmEdge_eq a b with h | h <;> rw [h] <;> simp [Sym2.eq_swap]

/-- Putting an edge in normal form is idempotent. -/
theorem nrmEdge_idem (a b : Fin 4) :
    nrmEdge (nrmEdge a b).1 (nrmEdge a b).2 = nrmEdge a b := by
  rcases nrmEdge_eq a b with h | h
  · rw [h]; exact h
  · rw [h, ← nrmEdge_comm a b]; exact h

/-- An unordered pair of vertices of an edge in normal form is the same as the unordered pair
of the original edge, with the normal-form ordering. -/
theorem nrmEdge_mem_sym2 (a b : Fin 4) (h : a ≠ b) :
    s((nrmEdge a b).1, (nrmEdge a b).2) = s(a, b) ∧ (nrmEdge a b).1 < (nrmEdge a b).2 :=
  ⟨nrmEdge_sym2 a b, nrmEdge_fst_lt a b h⟩

end Work.SG
