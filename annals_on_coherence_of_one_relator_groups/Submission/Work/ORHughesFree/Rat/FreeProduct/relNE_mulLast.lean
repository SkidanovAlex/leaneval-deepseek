import Mathlib
import Submission.Work.ORHughesFree.Rat.FreeProduct.NU
import Submission.Work.ORHughesFree.Rat.FreeProduct.shiftPad_mulLast

namespace Work.ORHughesFree.Rat.FreeProduct

theorem relNE_mulLast {U : Type} [Group U] (u : U) {l l' : Work.ORHughesFree.Rat.FreeProduct.NEL (U := U)}
    (h : Work.ORHughesFree.Rat.FreeProduct.relNE l l') :
    Work.ORHughesFree.Rat.FreeProduct.relNE
      ⟨Work.ORHughesFree.Rat.FreeProduct.mulLast l.1 u,
        Work.ORHughesFree.Rat.FreeProduct.mulLast_ne_nil u l.2⟩
      ⟨Work.ORHughesFree.Rat.FreeProduct.mulLast l'.1 u,
        Work.ORHughesFree.Rat.FreeProduct.mulLast_ne_nil u l'.2⟩ := by
  obtain ⟨b, hlen, hb⟩ := h
  refine ⟨b, ?_, ?_⟩
  · rw [mulLast_length]; omega
  · change mulLast l'.1 u = shiftPad (1 :: (b ++ [1])) (mulLast l.1 u)
    rw [hb]
    exact shiftPad_mulLast u (1 :: (b ++ [1])) l.1
      (by simp only [List.length_cons, List.length_append, List.length_nil]; omega)
      (by rw [List.getLast?_cons_of_ne_nil (by simp : b ++ [1] ≠ []), List.getLast?_concat])

end Work.ORHughesFree.Rat.FreeProduct
