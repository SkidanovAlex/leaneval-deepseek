import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Real.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Algebra.BigOperators

lemma sum_double_eq_diag_add_pairs {α : Type*} [LinearOrder α] (s : Finset α) (f : α → α → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, f i j)
      = (∑ i ∈ s, f i i) + (∑ i ∈ s, ∑ j ∈ s, if i < j then f i j + f j i else 0) := by
  classical
  -- every summand splits into the diagonal part, the i < j part and the j < i part
  have hsplit : ∀ i j : α, f i j = (if i = j then f i j else 0) + (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp
    · by_cases hlt : i < j
      · simp [hij, hlt, lt_asymm hlt]
      · have hgt : j < i := (lt_or_gt_of_ne hij).resolve_left hlt
        simp [hij, hlt, hgt]
  -- the diagonal double sum collapses to the single sum
  have hdiag' : (∑ i ∈ s, ∑ j ∈ s, if i = j then f i j else 0) = (∑ i ∈ s, f i i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_ite_eq s i (fun j => f i j)]
    simp [hi]
  -- inside the i < j region the summand f i j + f j i splits
  have hsplit_pair : ∀ i j : α,
      (if i < j then f i j + f j i else 0)
        = (if i < j then f i j else 0) + (if i < j then f j i else 0) := by
    intro i j
    by_cases h : i < j <;> simp [h]
  -- swapping the summation indices turns the {i < j, f j i} part into the {j < i, f i j} part
  have hmh : (∑ i ∈ s, ∑ j ∈ s, if i < j then f j i else 0)
      = (∑ i ∈ s, ∑ j ∈ s, if j < i then f i j else 0) := by
    rw [Finset.sum_comm]
  -- so the off-diagonal double sum collects exactly the i < j and the j < i summands of the left
  have hpairs' : (∑ i ∈ s, ∑ j ∈ s, if i < j then f i j + f j i else 0)
      = (∑ i ∈ s, ∑ j ∈ s, if i < j then f i j else 0)
        + (∑ i ∈ s, ∑ j ∈ s, if j < i then f i j else 0) := by
    calc
      (∑ i ∈ s, ∑ j ∈ s, if i < j then f i j + f j i else 0)
          = ∑ i ∈ s, ∑ j ∈ s,
              ((if i < j then f i j else 0) + (if i < j then f j i else 0)) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              exact hsplit_pair i j
      _ = (∑ i ∈ s, ∑ j ∈ s, if i < j then f i j else 0)
            + (∑ i ∈ s, ∑ j ∈ s, if i < j then f j i else 0) := by
            simp_rw [Finset.sum_add_distrib]
      _ = (∑ i ∈ s, ∑ j ∈ s, if i < j then f i j else 0)
            + (∑ i ∈ s, ∑ j ∈ s, if j < i then f i j else 0) := by
            rw [hmh]
  calc
    (∑ i ∈ s, ∑ j ∈ s, f i j)
        = ∑ i ∈ s, ∑ j ∈ s,
            ((if i = j then f i j else 0) + (if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            exact hsplit i j
    _ = (∑ i ∈ s, ∑ j ∈ s, if i = j then f i j else 0)
          + (∑ i ∈ s, ∑ j ∈ s, if i < j then f i j else 0)
          + (∑ i ∈ s, ∑ j ∈ s, if j < i then f i j else 0) := by
            simp_rw [Finset.sum_add_distrib]
    _ = (∑ i ∈ s, f i i)
          + (∑ i ∈ s, ∑ j ∈ s, if i < j then f i j else 0)
          + (∑ i ∈ s, ∑ j ∈ s, if j < i then f i j else 0) := by
            rw [hdiag']
    _ = (∑ i ∈ s, f i i)
          + (∑ i ∈ s, ∑ j ∈ s, if i < j then f i j + f j i else 0) := by
            rw [hpairs']
            rw [← add_assoc]

end Commons.Algebra.BigOperators