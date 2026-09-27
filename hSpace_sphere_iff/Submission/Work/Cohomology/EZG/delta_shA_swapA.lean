/-
# The `a`-shuffle map is unchanged by swapping two adjacent positions, after a face

The mixed (neither `a`-side nor `b`-side) terms of the expanded boundary of the shuffle chain are
paired by exchanging the membership of two adjacent positions `q.castSucc`, `q.succ` of the
shuffle (`swapA`), keeping the face index `k` fixed.  For the pairing to be a cancellation of
equal summands one has to know that the two `shA`-maps involved have the *same* `k`-th face.

That is what this file records: if `k` is the face index whose value is `q.val + 1` — so that the
deleted position `delIdx k = q.succ` is exactly the upper of the two swapped positions — then
`δ k ≫ shA A = δ k ≫ shA (swapA N A q)`.

The point is purely combinatorial.  The `k`-th face of `shA A` at a vertex `j` is computed from
`cnt A m` where `m = (Fin.succAbove k j).val`; since `Fin.succAbove k ·` never hits `k`, the value
`m` is different from `q.val + 1`, and for such an `m` the swap changes the membership only at the
two positions `q.castSucc`, `q.succ`, which lie strictly on the same side of the threshold `m`.
Hence `cnt A m = cnt (swapA N A q) m` (`cnt_swapA_of_ne`), and the two order homs agree.
-/
import Mathlib
import Submission.Work.Cohomology.EZG.dAux
import Submission.Work.Cohomology.EZG.cnt_swapA_of_ne

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology.EZG

open Work.Cohomology

/-- At a vertex `j` of the source simplex, the `k`-th face of `shA A` only depends on
`cnt A m` with `m = (Fin.succAbove k j).val`, and `Fin.succAbove k ·` never takes the value `k`. -/
lemma val_succAbove_ne_castSucc_val {N : ℕ} (q : Fin N) (k : Fin (N+2))
    (hk : k.val = q.val + 1) (j : Fin (N+1)) :
    ((k.succAbove j : Fin (N+2)) : ℕ) ≠ q.val + 1 := by
  intro hh
  exact Fin.succAbove_ne k j (Fin.ext (by rw [hh, hk]))

/-- The two swapped positions lie strictly on the same side of a threshold `m` that is different
from `q.val + 1`. -/
lemma castSucc_lt_iff_succ_lt_of_ne {N : ℕ} (q : Fin N) {m : ℕ} (hm : m ≠ q.val + 1) :
    (q.castSucc : Fin (N+1)).val < m ↔ (q.succ : Fin (N+1)).val < m := by
  rw [Fin.val_castSucc, Fin.val_succ]
  omega

theorem delta_shA_swapA {N P : ℕ} (A : Finset (Fin (N+1))) (q : Fin N) (k : Fin (N+2)) (hk : k.val = q.val + 1) (h : q.castSucc ∈ A ↔ q.succ ∉ A) (hA : A.card ≤ P+1) (hA' : (Work.Cohomology.EZG.swapA N A q).card ≤ P+1) : CategoryTheory.CategoryStruct.comp (SimplexCategory.δ k) (Work.Cohomology.shA A hA) = CategoryTheory.CategoryStruct.comp (SimplexCategory.δ k) (Work.Cohomology.shA (Work.Cohomology.EZG.swapA N A q) hA') := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    Work.Cohomology.shA_apply, Work.Cohomology.delta_toOrderHom]
  exact cnt_swapA_of_ne A q h (val_succAbove_ne_castSucc_val q k hk j)

end Work.Cohomology.EZG
