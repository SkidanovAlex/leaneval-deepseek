import Mathlib
import Submission.Work.ORHughesFree.Rat.FreeProduct.NU

namespace Work.ORHughesFree.Rat.FreeProduct

/-- `mulLast` peels off the head as soon as the tail is nonempty (the definition's second
clause, `[x]`, and third clause agree). -/
private theorem mulLast_cons_of_ne_nil {U : Type} [Group U] (u : U) (a : Work.ORHughesFree.RatU U)
    (ys : List (Work.ORHughesFree.RatU U)) (h : ys ≠ []) :
    Work.ORHughesFree.Rat.FreeProduct.mulLast (a :: ys) u
      = a :: Work.ORHughesFree.Rat.FreeProduct.mulLast ys u := by
  cases ys with
  | nil => exact absurd rfl h
  | cons y yss =>
    cases yss with
    | nil => rfl
    | cons z zs => rfl

theorem shiftPad_mulLast {U : Type} [Group U] (u : U) (b : List U) (l : List (Work.ORHughesFree.RatU U))
    (h : b.length = l.length + 1) (hlast : b.getLast? = some 1) :
    Work.ORHughesFree.Rat.FreeProduct.mulLast (Work.ORHughesFree.Rat.FreeProduct.shiftPad b l) u
      = Work.ORHughesFree.Rat.FreeProduct.shiftPad b (Work.ORHughesFree.Rat.FreeProduct.mulLast l u) := by
  induction l generalizing b with
  | nil => simp
  | cons x xs ih =>
    match xs with
    | [] =>
      cases b with
      | nil => simp at h
      | cons b₀ bs =>
        cases bs with
        | nil => simp at h
        | cons b₁ bs =>
          match bs with
          | [] =>
            simp at hlast
            subst hlast
            simp [Work.ORHughesFree.Rat.FreeProduct.mulLast,
              Work.ORHughesFree.Rat.FreeProduct.actR, mul_assoc]
          | w :: ws => simp only [List.length_cons, List.length_nil] at h; omega
    | y :: ys =>
      cases b with
      | nil => simp at h
      | cons b₀ bs =>
        cases bs with
        | nil => simp at h
        | cons b₁ bs =>
          have h' : (b₁ :: bs).length = (y :: ys).length + 1 := by
            simp only [List.length_cons] at h ⊢; omega
          have hlast' : (b₁ :: bs).getLast? = some 1 := by
            rw [List.getLast?_cons_cons] at hlast; exact hlast
          have hne : Work.ORHughesFree.Rat.FreeProduct.shiftPad (b₁ :: bs) (y :: ys) ≠ [] := by
            intro hnil
            have hlen := Work.ORHughesFree.Rat.FreeProduct.shiftPad_length (b₁ :: bs) (y :: ys) h'
            rw [hnil] at hlen
            simp at hlen
          have hlhs : Work.ORHughesFree.Rat.FreeProduct.mulLast
                (Work.ORHughesFree.Rat.FreeProduct.shiftPad (b₀ :: b₁ :: bs) (x :: y :: ys)) u
              = (Work.ORHughesFree.RatU.ofGroup b₁⁻¹ * x * Work.ORHughesFree.RatU.ofGroup b₀)
                :: Work.ORHughesFree.Rat.FreeProduct.shiftPad (b₁ :: bs)
                    (Work.ORHughesFree.Rat.FreeProduct.mulLast (y :: ys) u) := by
            rw [Work.ORHughesFree.Rat.FreeProduct.shiftPad_cons,
              mulLast_cons_of_ne_nil u _ _ hne, ih (b₁ :: bs) h' hlast']
          have hrhs : Work.ORHughesFree.Rat.FreeProduct.shiftPad (b₀ :: b₁ :: bs)
                (Work.ORHughesFree.Rat.FreeProduct.mulLast (x :: y :: ys) u)
              = (Work.ORHughesFree.RatU.ofGroup b₁⁻¹ * x * Work.ORHughesFree.RatU.ofGroup b₀)
                :: Work.ORHughesFree.Rat.FreeProduct.shiftPad (b₁ :: bs)
                    (Work.ORHughesFree.Rat.FreeProduct.mulLast (y :: ys) u) := by
            rw [mulLast_cons_of_ne_nil u x (y :: ys) (by simp),
              Work.ORHughesFree.Rat.FreeProduct.shiftPad_cons]
          exact hlhs.trans hrhs.symm

end Work.ORHughesFree.Rat.FreeProduct
