import Mathlib
import Submission.Work.Cert.CJ2.Gen

namespace Work.Cert.CJ2Sum

open Work.Cert.CJ2

/-!
# `Dsum` is invariant under permutation of the list

`Dsum` is the weighted double sum `Σ_{x,y} w_x w_y · max v_x v_y` over a list of `(value, weight)`
pairs, written in cons-recursive form
`Dsum (x :: l) = w_x² v_x + 2 w_x Σ_{y ∈ l} w_y max v_x v_y + Dsum l`.
Since `max` is symmetric and multiplication in `ℤ` is commutative, the displayed value does not
depend on the order in which the pairs are listed.  We prove this by induction on `List.Perm`,
the only nontrivial step being the exchange of two adjacent entries.
-/

/-- Swapping the two leading entries of a list does not change `Dsum`. -/
theorem Dsum_swap_adjacent (x y : ℤ × ℤ) (l : List (ℤ × ℤ)) :
    Dsum (y :: x :: l) = Dsum (x :: y :: l) := by
  simp only [Dsum_cons, List.map_cons, List.sum_cons]
  rw [max_comm y.1 x.1]
  ring

theorem Dsum_perm (l₁ l₂ : List (ℤ × ℤ)) (h : l₁.Perm l₂) :
    Work.Cert.CJ2.Dsum l₁ = Work.Cert.CJ2.Dsum l₂ := by
  induction h with
  | nil => rfl
  | cons x hl ih =>
      rw [Dsum_cons, Dsum_cons, ih,
        List.Perm.sum_eq (hl.map (fun z => z.2 * max x.1 z.1))]
  | swap x y l => exact Dsum_swap_adjacent x y l
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

end Work.Cert.CJ2Sum
