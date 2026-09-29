import Mathlib
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.pbCostArithKit

namespace Work.Resample

/-- Split a product along a position: for `j < l.length`,
`l.prod = (l.take j).prod * (l.getD j 0 * (l.drop (j+1)).prod)`. -/
theorem pa_prod_take_getD_drop {l : List ℕ} {j : ℕ} (hj : j < l.length) :
    l.prod = (l.take j).prod * (l.getD j 0 * (l.drop (j + 1)).prod) := by
  conv_lhs => rw [← List.take_append_drop j l]
  rw [List.prod_append, List.drop_eq_getElem_cons hj, List.prod_cons]
  rw [List.getD_eq_getElem l 0 hj]

/-- The `Cm`-carrying terms of the per-axis budgets, summed over the `D` axes:
`Σ_{j<D} (A_j * B_{j+1} * (t_j + 1)) ≤ 2 * D * ts.prod`, where `A_j = (ts.take j).prod` and
`B_{j+1} = (ss.drop (j+1)).prod`. -/
theorem paDSumCm {p α : ℕ} {ss ts : List ℕ} (h : HvdH.ResParams p α ss ts) :
    (∑ j ∈ Finset.range HvdH.D,
        (ts.take j).prod * (ss.drop (j + 1)).prod * (ts.getD j 0 + 1))
      ≤ 2 * HvdH.D * ts.prod := by
  have htslen : ts.length = HvdH.D := h.2.1
  have hterm : ∀ j ∈ Finset.range HvdH.D,
      (ts.take j).prod * (ss.drop (j + 1)).prod * (ts.getD j 0 + 1) ≤ 2 * ts.prod := by
    intro j hj
    have hjD : j < HvdH.D := Finset.mem_range.mp hj
    have hjl : j < ts.length := by omega
    have ht0 : 1 ≤ ts.getD j 0 := by
      have := (h.2.2.2.2.2 j hjD).1
      have := (h.2.2.2.2.2 j hjD).2.1
      omega
    have hB : (ss.drop (j + 1)).prod ≤ (ts.drop (j + 1)).prod :=
      pa_drop_prod_le h (j + 1)
    have hdec := pa_prod_take_getD_drop (l := ts) hjl
    -- `A * t_j * B' = ts.prod`
    have hAtB : (ts.take j).prod * ts.getD j 0 * (ts.drop (j + 1)).prod = ts.prod := by
      rw [hdec]
      ring
    have e1 : (ts.take j).prod * (ss.drop (j + 1)).prod * ts.getD j 0 ≤ ts.prod := by
      have h' : (ss.drop (j + 1)).prod * ts.getD j 0 ≤ ts.getD j 0 * (ts.drop (j + 1)).prod := by
        calc (ss.drop (j + 1)).prod * ts.getD j 0
            ≤ (ts.drop (j + 1)).prod * ts.getD j 0 := Nat.mul_le_mul_right _ hB
          _ = ts.getD j 0 * (ts.drop (j + 1)).prod := by ring
      calc (ts.take j).prod * (ss.drop (j + 1)).prod * ts.getD j 0
          = (ts.take j).prod * ((ss.drop (j + 1)).prod * ts.getD j 0) := Nat.mul_assoc _ _ _
        _ ≤ (ts.take j).prod * (ts.getD j 0 * (ts.drop (j + 1)).prod) := Nat.mul_le_mul_left _ h'
        _ = ts.prod := by rw [← Nat.mul_assoc]; exact hAtB
    have e2 : (ts.take j).prod * (ss.drop (j + 1)).prod ≤ ts.prod := by
      have h'' : (ts.drop (j + 1)).prod ≤ ts.getD j 0 * (ts.drop (j + 1)).prod := by
        calc (ts.drop (j + 1)).prod = 1 * (ts.drop (j + 1)).prod := (one_mul _).symm
          _ ≤ ts.getD j 0 * (ts.drop (j + 1)).prod := Nat.mul_le_mul_right _ ht0
      calc (ts.take j).prod * (ss.drop (j + 1)).prod
          ≤ (ts.take j).prod * (ts.drop (j + 1)).prod := Nat.mul_le_mul_left _ hB
        _ ≤ (ts.take j).prod * (ts.getD j 0 * (ts.drop (j + 1)).prod) := Nat.mul_le_mul_left _ h''
        _ = ts.prod := by rw [← Nat.mul_assoc]; exact hAtB
    calc (ts.take j).prod * (ss.drop (j + 1)).prod * (ts.getD j 0 + 1)
        = (ts.take j).prod * (ss.drop (j + 1)).prod * ts.getD j 0
          + (ts.take j).prod * (ss.drop (j + 1)).prod := by ring
      _ ≤ ts.prod + ts.prod := Nat.add_le_add e1 e2
      _ = 2 * ts.prod := by ring
  calc (∑ j ∈ Finset.range HvdH.D,
        (ts.take j).prod * (ss.drop (j + 1)).prod * (ts.getD j 0 + 1))
      ≤ ∑ _j ∈ Finset.range HvdH.D, 2 * ts.prod := Finset.sum_le_sum hterm
    _ = HvdH.D * (2 * ts.prod) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ = 2 * HvdH.D * ts.prod := by ring

end Work.Resample
