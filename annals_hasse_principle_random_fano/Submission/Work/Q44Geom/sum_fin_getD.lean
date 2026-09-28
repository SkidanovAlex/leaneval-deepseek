import Mathlib

namespace Work.Q44Geom

/-- For a list `l` with `l.length ≤ d`, the sum of `f` over the `Fin d`-indices, where an index `i ≥ l.length` is replaced by a default value `a` with `f a = 0`, equals the sum of `f` over the entries of `l`. -/
theorem sum_fin_getD {α : Type*} (l : List α) (d : ℕ) (a : α) (f : α → ℕ) (hf : f a = 0)
    (hd : l.length ≤ d) :
    ∑ i : Fin d, f (l.getD (i : ℕ) a) = (l.map f).sum := by
  induction l generalizing d with
  | nil => simp [hf]
  | cons b t ih =>
    cases d with
    | zero => exact absurd hd (by simp)
    | succ e =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ]
      rw [ih e (by simpa using hd)]
      rfl

end Work.Q44Geom
