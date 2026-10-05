import Mathlib
import Submission.Work.RPCore.Chain.C4Defs

namespace Work.RPCore.Chain

theorem BvForm_diag (n N : ℕ) (δ : ℝ) (z : ChainSp n) :
    BvForm n N δ z z
      = 2 * (∑ j : Fin n, ((z.2 j).1 * ((z.1 j.succ).1 - (z.1 j.castSucc).1) +
            (z.2 j).2 * ((z.1 j.succ).2 - (z.1 j.castSucc).2)))
        - 2 * (1 / Real.cos δ - 1) *
            (∑ j : Fin n, if midBlock N (j : ℕ) then (z.1 j.castSucc).1 * (z.2 j).1 else 0)
        + Real.tan δ *
            (∑ j : Fin n, if midBlock N (j : ℕ) then ((z.1 j.castSucc).1 ^ 2 + (z.2 j).1 ^ 2) else 0) := by
  unfold BvForm
  have h1 : (∑ j : Fin n,
        ((z.2 j).1 * ((z.1 j.succ).1 - (z.1 j.castSucc).1) +
         (z.2 j).1 * ((z.1 j.succ).1 - (z.1 j.castSucc).1) +
         (z.2 j).2 * ((z.1 j.succ).2 - (z.1 j.castSucc).2) +
         (z.2 j).2 * ((z.1 j.succ).2 - (z.1 j.castSucc).2)))
      = 2 * (∑ j : Fin n, ((z.2 j).1 * ((z.1 j.succ).1 - (z.1 j.castSucc).1) +
              (z.2 j).2 * ((z.1 j.succ).2 - (z.1 j.castSucc).2))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h2 : (∑ j : Fin n, if midBlock N (j : ℕ) then
        ((z.1 j.castSucc).1 * (z.2 j).1 + (z.1 j.castSucc).1 * (z.2 j).1) else 0)
      = 2 * (∑ j : Fin n, if midBlock N (j : ℕ) then (z.1 j.castSucc).1 * (z.2 j).1 else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have h3 : (∑ j : Fin n, if midBlock N (j : ℕ) then
        ((z.1 j.castSucc).1 * (z.1 j.castSucc).1 + (z.2 j).1 * (z.2 j).1) else 0)
      = (∑ j : Fin n, if midBlock N (j : ℕ) then ((z.1 j.castSucc).1 ^ 2 + (z.2 j).1 ^ 2) else 0) := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [h1, h2, h3]
  ring

end Work.RPCore.Chain
