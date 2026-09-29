import Submission.Work.CNum.CertC.RowA
import Submission.Work.CNum.CertC.RowB
import Submission.Work.CNum.CertC.RowC
import Submission.Work.CNum.CertC.RowD
import Submission.Work.CNum.CertC.RowE
import Submission.Work.CNum.CertC.RowF
import Submission.Work.CNum.CertC.RowG
import Submission.Work.CNum.CertC.RowH

/-!
# `Work.CNum.CertC.Sum` — the rearrangement double sum of the tabulated arc bounds

`pairSumLit = (sum over k, k' < 1024 of max (Gv k) (Gv k'))` in mantissas.  The outer fold is split
into eight blocks of `128` arcs, each certified by one kernel computation in
`Work.CNum.CertC.Row{A..H}`, and the blocks are glued with `List.map_append`/`List.sum_append`.
-/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The `x`-th row of the double sum: `sum over y of max x y`. -/
def T (x : ℤ) : ℤ := List.foldl (fun a y => a + max x y) 0 gvLitL0

/-- Shifting the initial value of a fold by `x ↦ acc + S x`. -/
theorem foldl_add_shift (l : List ℤ) (S : ℤ → ℤ) (acc : ℤ) :
    l.foldl (fun a x => a + S x) acc = acc + l.foldl (fun a x => a + S x) 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons x t ih =>
      simp only [List.foldl_cons, zero_add]
      rw [ih (acc + S x), ih (S x)]
      ring

/-- A fold by `x ↦ acc + S x` is the sum of the mapped list. -/
theorem foldl_add_eq_sum (l : List ℤ) (S : ℤ → ℤ) :
    l.foldl (fun a x => a + S x) 0 = (l.map S).sum := by
  induction l with
  | nil => simp
  | cons x t ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, zero_add]
      rw [foldl_add_shift (l := t) (S := S) (acc := S x), ih]

/-- The fold function of the outer fold, in shifted form. -/
theorem G_eq :
    (fun acc x => List.foldl (fun a y => a + max x y) acc gvLitL0) = (fun acc x => acc + T x) := by
  funext acc x
  exact foldl_add_shift gvLitL0 (fun y => max x y) acc

/-- The tabulated arc bounds, as eight blocks of `128`. -/
theorem hchunks : gvLitL0 = gvA ++ gvB ++ gvC ++ gvD ++ gvE ++ gvF ++ gvG ++ gvH := rfl

/-- The rearrangement double sum of the tabulated arc bounds. -/
def pairSumLit : ℤ := (((((((915495902627090 + 1096567200134222) + 1754939517108852) + 1875698803711276) + 1875696341914272) + 1754937634495296) + 1096570699737996) + 915497570432628)

/-- Row `A` of the double sum. -/
theorem rowA_sum : (gvA.map T).sum = 915495902627090 := by
  rw [← foldl_add_eq_sum gvA T, ← G_eq]
  exact rowA_ok

/-- Row `B` of the double sum. -/
theorem rowB_sum : (gvB.map T).sum = 1096567200134222 := by
  rw [← foldl_add_eq_sum gvB T, ← G_eq]
  exact rowB_ok

/-- Row `C` of the double sum. -/
theorem rowC_sum : (gvC.map T).sum = 1754939517108852 := by
  rw [← foldl_add_eq_sum gvC T, ← G_eq]
  exact rowC_ok

/-- Row `D` of the double sum. -/
theorem rowD_sum : (gvD.map T).sum = 1875698803711276 := by
  rw [← foldl_add_eq_sum gvD T, ← G_eq]
  exact rowD_ok

/-- Row `E` of the double sum. -/
theorem rowE_sum : (gvE.map T).sum = 1875696341914272 := by
  rw [← foldl_add_eq_sum gvE T, ← G_eq]
  exact rowE_ok

/-- Row `F` of the double sum. -/
theorem rowF_sum : (gvF.map T).sum = 1754937634495296 := by
  rw [← foldl_add_eq_sum gvF T, ← G_eq]
  exact rowF_ok

/-- Row `G` of the double sum. -/
theorem rowG_sum : (gvG.map T).sum = 1096570699737996 := by
  rw [← foldl_add_eq_sum gvG T, ← G_eq]
  exact rowG_ok

/-- Row `H` of the double sum. -/
theorem rowH_sum : (gvH.map T).sum = 915497570432628 := by
  rw [← foldl_add_eq_sum gvH T, ← G_eq]
  exact rowH_ok


theorem pairSumLit_eq :
    List.foldl (fun acc x => List.foldl (fun a y => a + max x y) acc gvLitL0) 0 gvLitL0
      = pairSumLit := by
  rw [G_eq, foldl_add_eq_sum, hchunks]
  simp only [List.map_append, List.sum_append]
  rw [rowA_sum, rowB_sum, rowC_sum, rowD_sum, rowE_sum, rowF_sum, rowG_sum, rowH_sum, pairSumLit]

theorem pairSumLit_ok : pairSumLit * 10 ≤ 102 * 1024 * 1024 * SC := by decide

end Work.CNum
