import Mathlib

namespace Work.WilE7

/-- The sum of a constant list is the length times the constant. -/
lemma sum_map_const_nat {α : Type*} (l : List α) (c : ℕ) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- Unfolding `List.product` at the empty list, phrased for `List.product` itself. -/
@[simp] lemma product_nil_left {α β : Type*} (l : List β) : ([] : List α).product l = [] := rfl

/-- Unfolding `List.product` at a cons, phrased for `List.product` itself. -/
@[simp] lemma product_cons_left {α β : Type*} (a : α) (l : List α) (l' : List β) :
    (a :: l).product l' = l'.map (fun b => (a, b)) ++ l.product l' := rfl

theorem sumProduct {α β : Type*} (l : List α) (l' : List β) (f : α → ℕ) (g : β → ℕ) :
    ((l.product l').map (fun p => f p.1 + g p.2)).sum
      = l'.length * (l.map f).sum + l.length * (l'.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 : (List.map ((fun p => f p.1 + g p.2) ∘ fun b => (a, b)) l').sum
        = l'.length * f a + (List.map g l').sum := by
      have hcomp : List.map ((fun p => f p.1 + g p.2) ∘ fun b => (a, b)) l'
          = List.map (fun b => f a + g b) l' := rfl
      rw [hcomp, List.sum_map_add, sum_map_const_nat]
    simp only [product_cons_left, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons,
      List.length_cons, List.map_map, h1]
    ring

end Work.WilE7
