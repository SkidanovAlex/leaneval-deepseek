import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFact.N5.StepTools

/-!
# The mate map of a matching, and the preimage of a finite set

`nmate N x` is the unique `N`-neighbour of `x` when `N` is a matching, and `x` itself when `x` is
uncovered by `N`.  For a matching `N` this map is an **involution**: if `x` is matched then
`nmate N x` is its partner (and is matched back to `x`), and if `x` is uncovered then
`nmate N x = x` is a fixed point.  Consequently `x ↦ nmate N x` is injective, and hence the set of
vertices whose mate lies in a prescribed finite set `F` — that is, the preimage of `F` under an
injective map — has at most `|F|` elements.

This is the counting step used in the N5b construction (`completeInsideMatching`): the vertices
`x` with `nmate N x` in the "forbidden" set are the vertices whose `N`-partner is forbidden, and
there are no more of them than there are forbidden vertices.
-/

namespace Work.Deep.GKO.OneFact.N5

variable {n : ℕ} {N : SimpleGraph (Fin n)}

/-- The mate map of a matching is an involution.  (If `x` is covered this is `nmate_invol`; if `x`
is uncovered then `nmate N x = x` and the claim is immediate.) -/
theorem nmate_invol_all (hN : Work.Deep.GKO.IsMatching' N) (x : Fin n) :
    nmate N (nmate N x) = x := by
  by_cases h : ∃ w, N.Adj x w
  · exact nmate_invol hN h
  · have hx : nmate N x = x := nmate_eq_self fun w hw => h ⟨w, hw⟩
    simp [hx]

/-- The mate map of a matching is injective: it is an involution. -/
theorem nmate_injective (hN : Work.Deep.GKO.IsMatching' N) :
    Function.Injective (nmate N) := by
  intro x y h
  have h' := congrArg (nmate N) h
  rwa [nmate_invol_all hN x, nmate_invol_all hN y] at h'

/-- **The preimage of a finite set under the mate map of a matching has at most its cardinality.**
The vertices `x` whose mate lies in `F` inject into `F` via `x ↦ nmate N x`. -/
theorem card_filter_nmate_mem_le {n : ℕ} {N : SimpleGraph (Fin n)} (hN : Work.Deep.GKO.IsMatching' N) (F : Finset (Fin n)) : (Finset.univ.filter fun x => Work.Deep.GKO.OneFact.N5.nmate N x ∈ F).card ≤ F.card := by
  refine Finset.card_le_card_of_injOn (nmate N) ?_ ?_
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x _ y _ h
    exact nmate_injective hN h

end Work.Deep.GKO.OneFact.N5
