import Mathlib
import Submission.Work.ORHughesFree.Rat.FreeProduct.NU

namespace Work.ORHughesFree.Rat.FreeProduct

open Work.ORHughesFree

theorem shiftPad_mulFirst {U : Type} [Group U] (u : U) (b : List U) (l : List (Work.ORHughesFree.RatU U))
    (h : b.length = l.length + 1) (hhead : b.head? = some 1) :
    Work.ORHughesFree.Rat.FreeProduct.mulFirst u (Work.ORHughesFree.Rat.FreeProduct.shiftPad b l)
      = Work.ORHughesFree.Rat.FreeProduct.shiftPad b (Work.ORHughesFree.Rat.FreeProduct.mulFirst u l) := by
  cases l with
  | nil =>
    cases b with
    | nil => simp at h
    | cons b₀ bs =>
      cases bs with
      | nil => rfl
      | cons b₁ bs => simp at h
  | cons x xs =>
    cases b with
    | nil => simp at h
    | cons b₀ bs =>
      cases bs with
      | nil => simp at h
      | cons b₁ bs =>
        have hb₀ : b₀ = 1 := by simpa using hhead
        rw [hb₀]
        simp only [shiftPad_cons, mulFirst_cons]
        congr 1
        simp only [actL, RatU.ofGroup_one, mul_one, mul_assoc]

end Work.ORHughesFree.Rat.FreeProduct
