import Mathlib.Order.CompletePartialOrder
import Mathlib.Data.Finset.Range
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Order.Interval.Set.LinearOrder
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBox.LatticeModel

theorem tiling_Ico_monotone {a : ℕ → ℝ} (ha : Monotone a) (N : ℕ) :
    (⋃ i ∈ Finset.range N, Set.Ico (a i) (a (i + 1))) = Set.Ico (a 0) (a N) ∧
    (∀ i ∈ Finset.range N, ∀ j ∈ Finset.range N, i ≠ j →
      Disjoint (Set.Ico (a i) (a (i + 1))) (Set.Ico (a j) (a (j + 1)))) := by
  -- Splitting off the last interval of the range.
  have hstep : ∀ n, (⋃ i ∈ Finset.range (n + 1), Set.Ico (a i) (a (i + 1))) =
      (⋃ i ∈ Finset.range n, Set.Ico (a i) (a (i + 1))) ∪ Set.Ico (a n) (a (n + 1)) := by
    intro n
    ext x
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union]
    constructor
    · rintro ⟨i, hi, hx⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact Or.inl ⟨i, h, hx⟩
      · exact Or.inr (h ▸ hx)
    · rintro (⟨i, hi, hx⟩ | h)
      · exact ⟨i, Nat.lt_succ_of_lt hi, hx⟩
      · exact ⟨n, Nat.lt_succ_self n, h⟩
  constructor
  · induction N with
    | zero => simp
    | succ n ih =>
      rw [hstep n, ih]
      exact Set.Ico_union_Ico_eq_Ico (ha (Nat.zero_le n)) (ha (Nat.le_succ n))
  · intro i hi j hj hij
    rw [Finset.mem_range] at hi hj
    rcases lt_or_gt_of_ne hij with h | h
    · refine Set.disjoint_left.2 ?_
      intro x hx1 hx2
      rw [Set.mem_Ico] at hx1 hx2
      have h1 : a (i + 1) ≤ a j := ha (by omega)
      linarith [hx1.1, hx1.2, hx2.1, h1]
    · refine Set.disjoint_left.2 ?_
      intro x hx1 hx2
      rw [Set.mem_Ico] at hx1 hx2
      have h2 : a (j + 1) ≤ a i := ha (by omega)
      linarith [hx1.1, hx2.1, hx2.2, h2]

end Work.BoseBox.LatticeModel
