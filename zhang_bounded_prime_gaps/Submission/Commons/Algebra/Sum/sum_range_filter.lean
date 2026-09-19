import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Submission.Commons.Algebra.Multinomial.mulBin_comm

namespace Commons.Algebra.Sum

theorem sum_range_filter {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → ℕ) (n : ℕ) (F : α → M)
    (h : ∀ x ∈ l, f x < n) :
    (∑ i ∈ Finset.range n, ((l.filter (fun x => decide (f x = i))).map F).sum) = (l.map F).sum := by
  induction l with
  | nil => simp
  | cons y t ih =>
    have ht : ∀ x ∈ t, f x < n := fun x hx => h x (List.mem_cons_of_mem y hx)
    have ih' := ih ht
    have ha : f y < n := h y (by simp)
    -- For each `i`, the contribution of `y :: t` to the fibre `i` splits into the
    -- contribution of `y` (present only when `i = f y`) plus that of `t`.
    have key : ∀ i, (((y :: t).filter (fun x => decide (f x = i))).map F).sum
        = (if i = f y then F y else 0) + (((t.filter (fun x => decide (f x = i))).map F).sum) := by
      intro i
      rw [List.filter_cons]
      by_cases hi : i = f y
      · subst hi; simp
      · have hfy : ¬ (f y = i) := fun hh => hi hh.symm
        simp [hfy, hi]
    rw [Finset.sum_congr rfl (fun i _ => key i)]
    rw [Finset.sum_add_distrib, ih']
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_range, ha, ↓reduceIte]
    rw [List.map_cons, List.sum_cons]

end Commons.Algebra.Sum