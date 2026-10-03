import Mathlib
import Submission.Work.ORHughesFree.Rat.FreeProduct.NUMonoid

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree

theorem listProd_Xgen_eq_mk {U : Type} [Group U] (l : List (Work.ORHughesFree.RatU U)) (hl : l ≠ []) :
    (l.map Work.ORHughesFree.Rat.FreeProduct.NU.Xgen).prod =
      (Sum.inr (Quotient.mk (Work.ORHughesFree.Rat.FreeProduct.relNESetoid U) ⟨l, hl⟩) :
        Work.ORHughesFree.Rat.FreeProduct.NU U) := by
  have key : ∀ (m : List (RatU U)) (hm : m ≠ []),
      (m.map FreeProduct.NU.Xgen).prod
        = (Sum.inr (Quotient.mk (FreeProduct.relNESetoid U) ⟨m, hm⟩) : FreeProduct.NU U) := by
    intro m
    induction m with
    | nil => intro hm; exact absurd rfl hm
    | cons x xs ih =>
      intro hm
      cases xs with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      | cons y ys =>
        have hxs : (y :: ys) ≠ [] := by simp
        rw [List.map_cons, List.prod_cons, ih hxs, FreeProduct.NU.Xgen_mul_mk]
  exact key l hl

end Work.ORHughesFree.Rat
