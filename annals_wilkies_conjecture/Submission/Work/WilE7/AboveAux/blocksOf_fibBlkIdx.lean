import Mathlib
import Submission.Work.WilE7.AboveAux.AboveLevelDefs

namespace Work.WilE7.AboveAux

/-- The coordinate formula defining `blocksOf` against `fibBlkIdx`: gluing the `k` points
`z 0, …, z (k-1)` of `ℝ^N` into a point of `ℝ^{N*k}` and reading back the `l`-th block
returns `z l`. -/
theorem blocksOf_fibBlkIdx_apply {N k : ℕ} (z : Fin k → Fin N → ℝ) (l : Fin k) (i : Fin N) :
    blocksOf k z (fibBlkIdx N k l i) = z l i := by
  induction k with
  | zero => exact l.elim0
  | succ k ih =>
    rw [blocksOf.eq_2]
    cases l using Fin.lastCases with
    | last =>
      have hidx : fibBlkIdx N (k + 1) (Fin.last k) i = Fin.natAdd (N * k) i := by
        ext
        simp [fibBlkIdx_val, Fin.val_last, Nat.mul_comm]
      rw [hidx]
      exact Fin.append_right (blocksOf k (fun l => z l.castSucc)) (z (Fin.last k)) i
    | cast l' =>
      have hidx : fibBlkIdx N (k + 1) l'.castSucc i = Fin.castAdd N (fibBlkIdx N k l' i) := by
        ext
        simp [fibBlkIdx_val]
      rw [hidx]
      exact (Fin.append_left (blocksOf k (fun l => z l.castSucc)) (z (Fin.last k))
        (fibBlkIdx N k l' i)).trans (ih (fun l => z l.castSucc) l')

theorem blocksOf_fibBlkIdx {N k : ℕ} (z : Fin k → Fin N → ℝ) :
    (∀ (l : Fin k) (i : Fin N),
      Work.WilE7.AboveAux.blocksOf k z (Work.WilE7.AboveAux.fibBlkIdx N k l i) = z l i) ∧
    (∀ l : Fin k,
      Work.WilE7.AboveAux.fibBlk (Work.WilE7.AboveAux.blocksOf k z) l = z l) := by
  refine ⟨fun l i => blocksOf_fibBlkIdx_apply z l i, fun l => ?_⟩
  funext i
  simpa using blocksOf_fibBlkIdx_apply z l i

end Work.WilE7.AboveAux
