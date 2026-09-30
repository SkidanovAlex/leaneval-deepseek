import Submission.Work.N8.closed_walk_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Matrix

namespace Work.N8

/-- **Lower bound for the number of closed walks of even length.**

The number of cyclic `(2m)`-tuples of vertices with adjacent consecutive entries
dominates the `(2m)`-th power of the average (ordered) degree
`(#ordered adjacent pairs) / #vertices`.

Assembly: the cyclic count is `trace ((AdjMat Adj)^(2m))` (`cycle_count` plus the
walk-counting identity `walk_count`), the ordered-pair count is the total mass
`∑ i, ∑ j, AdjMat Adj i j` (`edges_eq_sum`), and the operator inequality
`trace_lower_bound` (Rayleigh quotient for the symmetric adjacency matrix together
with log-convexity of the iterates `k ↦ ‖A^k x‖`) supplies the estimate. -/
theorem closed_walk_lower_v2 {V : Type} [Fintype V] [DecidableEq V]
    (Adj : V → V → Prop) [DecidableRel Adj] (hsym : ∀ a b, Adj a b ↔ Adj b a)
    (m : ℕ) (hm : 1 ≤ m) :
    (((Finset.univ.filter (fun p : V × V ↦ Adj p.1 p.2)).card : ℝ) / (Fintype.card V : ℝ)) ^ (2 * m)
      ≤ ((Finset.univ.filter (fun v : Fin (2 * m) → V ↦ ∀ j : Fin (2 * m),
            Adj (v j) (v ⟨((j : ℕ) + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩))).card : ℝ)
:= by
  have hcount :
      ((Finset.univ.filter (fun v : Fin (2 * m) → V => ∀ j : Fin (2 * m),
          Adj (v j) (v ⟨((j : ℕ) + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩))).card : ℝ)
        = (AdjMat Adj ^ (2 * m)).trace := by
    rw [cycle_count Adj (2 * m) (by omega)]
    simp only [Nat.cast_sum, Matrix.trace, Matrix.diag]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [walk_count Adj (2 * m) i i]
  rw [hcount, ← edges_eq_sum]
  exact trace_lower_bound (AdjMat Adj) (AdjMat_isSymm Adj hsym) m hm

end Work.N8
