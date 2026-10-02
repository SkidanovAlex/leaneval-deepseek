import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Data.List

theorem length_mul_le_sum {α : Type*} (L : List α) (f : α → ℝ) (v : ℝ)
    (h : ∀ x ∈ L, v ≤ f x) : (L.length : ℝ) * v ≤ (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have ht : ∀ x ∈ t, v ≤ f x := fun x hx => h x (by simp [hx])
    have ha : v ≤ f a := h a (by simp)
    have := ih ht
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
    linarith

end Commons.Data.List