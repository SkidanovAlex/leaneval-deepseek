import Mathlib
import Submission.Work.SG.ApplyBDefs
import Submission.Work.SG.RepCoh_blk

namespace Work.SG.cobstepAux

open Work.SG

/-- `mvf` is `ℤ`-linear, so a coordinatewise divisibility of the difference of three vectors
descends to the difference of the three images. -/
theorem mvf_sub3_dvd (A : Work.SG.Data.M3) (n : ℤ) {u v w : Fin 3 → ℤ}
    (h : ∀ d : Fin 3, n ∣ u d - v d - w d) (c : Fin 3) :
    n ∣ Work.SG.mvf A u c - Work.SG.mvf A v c - Work.SG.mvf A w c := by
  have hsum : (∑ d : Fin 3, (A.toIMat c d * u d - A.toIMat c d * v d - A.toIMat c d * w d))
      = (∑ d : Fin 3, A.toIMat c d * u d) - (∑ d : Fin 3, A.toIMat c d * v d)
        - (∑ d : Fin 3, A.toIMat c d * w d) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [Work.SG.mvf_apply_eq, Work.SG.mvf_apply_eq, Work.SG.mvf_apply_eq, ← hsum]
  apply Finset.dvd_sum
  intro d _
  rw [show A.toIMat c d * u d - A.toIMat c d * v d - A.toIMat c d * w d
      = A.toIMat c d * (u d - v d - w d) from by ring]
  exact dvd_mul_of_dvd_right (h d) _

theorem blk_sub3_dvd (A : Work.SG.Data.M3) (n : ℤ) {k : ℕ} {y1 y2 y3 : List ℤ}
    (h1 : y1.length = 3 * k) (h2 : y2.length = 3 * k) (h3 : y3.length = 3 * k)
    {g : ℕ} (hg : g < k)
    (hcong : ∀ q, q < 3 * k → n ∣ y1.getD q 0 - y2.getD q 0 - y3.getD q 0) (c : Fin 3) :
    n ∣ Work.SG.mvf A ((Work.SG.Data.blocks y1).getD g Work.SG.Data.V3.zero).toFun c
      - Work.SG.mvf A ((Work.SG.Data.blocks y2).getD g Work.SG.Data.V3.zero).toFun c
      - Work.SG.mvf A ((Work.SG.Data.blocks y3).getD g Work.SG.Data.V3.zero).toFun c := by
  have hlen1 : 3 * (g + 1) ≤ y1.length := by omega
  have hlen2 : 3 * (g + 1) ≤ y2.length := by omega
  have hlen3 : 3 * (g + 1) ≤ y3.length := by omega
  refine mvf_sub3_dvd A n ?_ c
  intro d
  have e1 : ((Work.SG.Data.blocks y1).getD g Work.SG.Data.V3.zero).toFun d
      = y1.getD (3 * g + d.val) 0 := RepCoh_blk y1 g d hlen1
  have e2 : ((Work.SG.Data.blocks y2).getD g Work.SG.Data.V3.zero).toFun d
      = y2.getD (3 * g + d.val) 0 := RepCoh_blk y2 g d hlen2
  have e3 : ((Work.SG.Data.blocks y3).getD g Work.SG.Data.V3.zero).toFun d
      = y3.getD (3 * g + d.val) 0 := RepCoh_blk y3 g d hlen3
  rw [e1, e2, e3]
  exact hcong (3 * g + d.val) (by omega)

end Work.SG.cobstepAux
