import Mathlib
import Submission.Work.LT.lr_local_defs

namespace Work.LT

/-- **Far-edge count.** At a fixed vertex `v`, the pairs `(i,j)` on which the A-neighbour and the
B-neighbour disagree on the square `(v,i,j)` are at most the disputed B-edges through the
A-neighbours plus the disputed A-edges through the B-neighbours. Pointwise: if
`view W (nA A v i) (i,j) ≠ view W (nB B v j) (i,j)` then the diagonal value
`d = view W (nA A (nB B v j) i) (i,j) = view W (nB B (nA A v i) j) (i,j)` (by `nA_nB`) must differ
from one of them (`ne_or_ne_of_ne`), which is exactly a pointwise dispute of the B-edge through
`nA A v i` at row `i` or of the A-edge through `nB B v j` at column `j`. -/
theorem lr_far_edge_count {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) :
    ((Finset.univ.filter (fun p : Fin Δ × Fin Δ =>
        view W (nA A v p.1) p ≠ view W (nB B v p.2) p)).card : ℝ)
      ≤ (∑ i, (rB B W (nA A v i) : ℝ)) + (∑ j, (rA A W (nB B v j) : ℝ)) := by
  classical
  -- Rewrite the left-hand cardinality as a double sum of indicators over the square index `(i,j)`.
  have hL : ((Finset.univ.filter (fun p : Fin Δ × Fin Δ =>
        view W (nA A v p.1) p ≠ view W (nB B v p.2) p)).card : ℝ)
      = ∑ i : Fin Δ, ∑ j : Fin Δ,
          (if view W (nA A v i) (i,j) ≠ view W (nB B v j) (i,j) then (1:ℝ) else 0) := by
    rw [Finset.card_filter]
    push_cast
    rw [Fintype.sum_prod_type]
  rw [hL]
  -- Pointwise: a disagreement on the square `(v,i,j)` disputes one of the two far edges.
  have hpt : ∀ i j : Fin Δ,
      (if view W (nA A v i) (i,j) ≠ view W (nB B v j) (i,j) then (1:ℝ) else 0)
        ≤ (if pdispB B W (nA A v i) i j then (1:ℝ) else 0)
          + (if pdispA A W (nB B v j) i j then (1:ℝ) else 0) := by
    intro i j
    by_cases h : view W (nA A v i) (i,j) ≠ view W (nB B v j) (i,j)
    · rw [ite_eq_left h]
      rcases pdispB_far A B W v i j h with h2 | h1
      · rw [ite_eq_left h2]; split <;> norm_num
      · rw [ite_eq_left h1]; split <;> norm_num
    · rw [ite_eq_right h]; positivity
  calc ∑ i, ∑ j, (if view W (nA A v i) (i,j) ≠ view W (nB B v j) (i,j) then (1:ℝ) else 0)
      ≤ ∑ i, ∑ j, ((if pdispB B W (nA A v i) i j then (1:ℝ) else 0)
                    + (if pdispA A W (nB B v j) i j then (1:ℝ) else 0)) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact hpt i j
    _ = (∑ i, ∑ j, (if pdispB B W (nA A v i) i j then (1:ℝ) else 0))
        + (∑ i, ∑ j, (if pdispA A W (nB B v j) i j then (1:ℝ) else 0)) := by
        simp only [Finset.sum_add_distrib]
    -- Bound each sum by the number of disputed edges through the corresponding neighbour.
    _ ≤ (∑ i, (rB B W (nA A v i) : ℝ)) + (∑ j, (rA A W (nB B v j) : ℝ)) := by
        apply add_le_add
        · calc ∑ i, ∑ j, (if pdispB B W (nA A v i) i j then (1:ℝ) else 0)
              ≤ ∑ i, ∑ j, (if dispBE B W (nA A v i) j then (1:ℝ) else 0) := by
                apply Finset.sum_le_sum; intro i _
                apply Finset.sum_le_sum; intro j _
                by_cases hh : pdispB B W (nA A v i) i j
                · rw [ite_eq_left hh, ite_eq_left ⟨i, hh⟩]
                · rw [ite_eq_right hh]; split <;> norm_num
            _ = ∑ i, (rB B W (nA A v i) : ℝ) := by
                apply Finset.sum_congr rfl; intro i _
                rw [rB, Finset.card_filter]; push_cast; simp
        · calc ∑ i, ∑ j, (if pdispA A W (nB B v j) i j then (1:ℝ) else 0)
              = ∑ j, ∑ i, (if pdispA A W (nB B v j) i j then (1:ℝ) else 0) := by
                rw [Finset.sum_comm]
            _ ≤ ∑ j, ∑ i, (if dispAE A W (nB B v j) i then (1:ℝ) else 0) := by
                apply Finset.sum_le_sum; intro j _
                apply Finset.sum_le_sum; intro i _
                by_cases hh : pdispA A W (nB B v j) i j
                · rw [ite_eq_left hh, ite_eq_left ⟨j, hh⟩]
                · rw [ite_eq_right hh]; split <;> norm_num
            _ = ∑ j, (rA A W (nB B v j) : ℝ) := by
                apply Finset.sum_congr rfl; intro j _
                rw [rA, Finset.card_filter]; push_cast; simp

end Work.LT
