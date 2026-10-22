import Mathlib
import Submission.Work.ANALYTIC.CechPt.LevelAux
import Submission.Work.ANALYTIC.CechPt.midH_telescope
import Submission.Work.ANALYTIC.CechPt.sum_match_lt
import Submission.Work.ANALYTIC.CechPt.sum_match_gt
import Submission.Work.ANALYTIC.CechPt.sum_mid_eq

/-!
# The prism identity for the level-`n` dyadic nerve

This file proves the homotopy identity `d H + H d = rhoS^* - id` for the simplicial "prism"
operator `H` of `Submission/Work/ANALYTIC/CechPt/LevelAux.lean`:

`diff (H q G) y + H (q+1) (diff G) y = G (rhoS y) - G y`.

It is the combinatorial heart of the acyclicity of the level-`n` dyadic nerve of the interval
(`Submission/Work/ANALYTIC/CechPt/level_acyclic.lean`, assembled in
`Submission/Work/ANALYTIC/CechPt/Assembly.lean`).

The proof is a direct computation with the prism insertions `W j` and the cut maps `midH t`.
Writing `G` for a cochain on `lev M (q+1)`:

* the first sum `diff (H q G) y = ∑_{i,j} (-1)^{i+j} G (W_j (∂_i y))` is the `A`-side,
* the second sum `H (q+1) (diff G) y = ∑_{j,i} (-1)^{i+j} G (∂_i (W_j y))` is the `B`-side.

The face identities `∂_i W_j = W_{j-1} ∂_i` (`i < j`) and `∂_i W_j = W_j ∂_{i-1}` (`i > j+1`)
match the off-diagonal terms of the `B`-side against the `A`-side with opposite signs
(`sum_match_lt`, `sum_match_gt`); the diagonal terms `i = j, j+1` are the cut maps
`midH j`, `midH (j+1)` (`sum_mid_eq`), which telescope to `G (rhoS y) - G y`
(`midH_telescope`).
-/

namespace Work.ANALYTIC.CechPt

open Work.ANALYTIC.CechPt.Level
open scoped BigOperators

theorem prism_identity {M : ℕ} (q : ℕ) (G : Work.ANALYTIC.CechPt.Level.lev M (q + 1) → ℤ)
    (y : Work.ANALYTIC.CechPt.Level.lev M (q + 1)) :
    Work.ANALYTIC.CechPt.Level.diff (Work.ANALYTIC.CechPt.Level.H q G) y
      + Work.ANALYTIC.CechPt.Level.H (q + 1) (Work.ANALYTIC.CechPt.Level.diff G) y
      = G (Work.ANALYTIC.CechPt.Level.rhoS y) - G y := by
  -- unfold the two operators
  have hgoal :
      diff (H q G) y + H (q+1) (diff G) y
        = (∑ i : Fin (q+2), (-1:ℤ)^(i:ℕ) * ∑ j : Fin (q+1), (-1:ℤ)^(j:ℕ) * G (W j (face i y)))
          + (∑ j : Fin (q+2), (-1:ℤ)^(j:ℕ) * ∑ i : Fin (q+3), (-1:ℤ)^(i:ℕ) * G (face i (W j y))) := rfl
  rw [hgoal]
  -- `A`-side: rewrite the double sum as a sum over the product index type
  have h1 : (∑ i : Fin (q+2), (-1:ℤ)^(i:ℕ) * ∑ j : Fin (q+1), (-1:ℤ)^(j:ℕ) * G (W j (face i y)))
      = ∑ p : Fin (q+2) × Fin (q+1), (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (W p.2 (face p.1 y)) := by
    simp only [Finset.mul_sum]
    have hh : (∑ x : Fin (q+2), ∑ i : Fin (q+1),
          (-1:ℤ)^(x:ℕ) * ((-1:ℤ)^(i:ℕ) * G (W i (face x y))))
        = ∑ x : Fin (q+2), ∑ i : Fin (q+1),
          (-1:ℤ)^((x:ℕ)+(i:ℕ)) * G (W i (face x y)) := by
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun i _ => ?_))
      rw [← mul_assoc, ← pow_add]
    rw [hh]
    rw [← Finset.sum_product' (Finset.univ : Finset (Fin (q+2))) (Finset.univ : Finset (Fin (q+1)))
          (fun x i => (-1:ℤ)^((x:ℕ)+(i:ℕ)) * G (W i (face x y)))]
    rw [Finset.univ_product_univ]
  -- `B`-side: same rewriting
  have h2 : (∑ j : Fin (q+2), (-1:ℤ)^(j:ℕ) * ∑ i : Fin (q+3), (-1:ℤ)^(i:ℕ) * G (face i (W j y)))
      = ∑ p : Fin (q+2) × Fin (q+3), (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (face p.2 (W p.1 y)) := by
    simp only [Finset.mul_sum]
    have hh : (∑ x : Fin (q+2), ∑ i : Fin (q+3),
          (-1:ℤ)^(x:ℕ) * ((-1:ℤ)^(i:ℕ) * G (face i (W x y))))
        = ∑ x : Fin (q+2), ∑ i : Fin (q+3),
          (-1:ℤ)^((x:ℕ)+(i:ℕ)) * G (face i (W x y)) := by
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun i _ => ?_))
      rw [← mul_assoc, ← pow_add]
    rw [hh]
    rw [← Finset.sum_product' (Finset.univ : Finset (Fin (q+2))) (Finset.univ : Finset (Fin (q+3)))
          (fun x i => (-1:ℤ)^((x:ℕ)+(i:ℕ)) * G (face i (W x y)))]
    rw [Finset.univ_product_univ]
  rw [h1, h2]
  -- split the `A`-side into the two halves matched by the two reindexing lemmas
  have e1 : (∑ p : Fin (q+2) × Fin (q+1), (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (W p.2 (face p.1 y)))
      = (∑ p ∈ (Finset.univ : Finset (Fin (q+2) × Fin (q+1))).filter (fun p => (p.1:ℕ) ≤ (p.2:ℕ)),
            (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (W p.2 (face p.1 y)))
        + (∑ p ∈ (Finset.univ : Finset (Fin (q+2) × Fin (q+1))).filter (fun p => ¬ (p.1:ℕ) ≤ (p.2:ℕ)),
            (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (W p.2 (face p.1 y))) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin (q+2) × Fin (q+1)))
          (fun p => (p.1:ℕ) ≤ (p.2:ℕ))
          (fun p => (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (W p.2 (face p.1 y)))]
  -- split the `B`-side into the diagonal (`midH`) part and the two off-diagonal halves
  have e2 : (∑ p : Fin (q+2) × Fin (q+3), (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (face p.2 (W p.1 y)))
      = (∑ j : Fin (q+2), (G (midH ⟨(j:ℕ), by omega⟩ y) - G (midH ⟨(j:ℕ)+1, by omega⟩ y)))
        + ((∑ p ∈ (Finset.univ : Finset (Fin (q+2) × Fin (q+3))).filter (fun p => (p.2:ℕ) < (p.1:ℕ)),
              (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (face p.2 (W p.1 y)))
          + (∑ p ∈ (Finset.univ : Finset (Fin (q+2) × Fin (q+3))).filter (fun p => (p.1:ℕ)+1 < (p.2:ℕ)),
              (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (face p.2 (W p.1 y)))) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin (q+2) × Fin (q+3)))
          (fun p => (p.2:ℕ) = (p.1:ℕ) ∨ (p.2:ℕ) = (p.1:ℕ)+1)
          (fun p => (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (face p.2 (W p.1 y)))]
    rw [sum_mid_eq y G]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not
          ((Finset.univ : Finset (Fin (q+2) × Fin (q+3))).filter
            (fun p => ¬ ((p.2:ℕ) = (p.1:ℕ) ∨ (p.2:ℕ) = (p.1:ℕ)+1)))
          (fun p => (p.2:ℕ) < (p.1:ℕ))
          (fun p => (-1:ℤ)^((p.1:ℕ)+(p.2:ℕ)) * G (face p.2 (W p.1 y)))]
    congr 1
    · congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  rw [e1, e2]
  -- the two off-diagonal halves cancel against the two halves of the `A`-side
  rw [sum_match_lt y G, sum_match_gt y G]
  -- the diagonal part is the telescoping sum of the cut maps
  rw [midH_telescope y G]
  ring

end Work.ANALYTIC.CechPt
