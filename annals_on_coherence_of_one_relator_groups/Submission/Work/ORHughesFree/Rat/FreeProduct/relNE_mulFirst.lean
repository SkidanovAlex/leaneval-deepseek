import Mathlib
import Submission.Work.ORHughesFree.Rat.FreeProduct.NU
import Submission.Work.ORHughesFree.Rat.FreeProduct.shiftPad_mulFirst

namespace Work.ORHughesFree.Rat.FreeProduct

theorem relNE_mulFirst {U : Type} [Group U] (u : U) {l l' : Work.ORHughesFree.Rat.FreeProduct.NEL (U := U)}
    (h : Work.ORHughesFree.Rat.FreeProduct.relNE l l') :
    Work.ORHughesFree.Rat.FreeProduct.relNE
      ⟨Work.ORHughesFree.Rat.FreeProduct.mulFirst u l.1,
        Work.ORHughesFree.Rat.FreeProduct.mulFirst_ne_nil u l.2⟩
      ⟨Work.ORHughesFree.Rat.FreeProduct.mulFirst u l'.1,
        Work.ORHughesFree.Rat.FreeProduct.mulFirst_ne_nil u l'.2⟩ := by
  obtain ⟨b, hlen, hb⟩ := h
  have hbnd : (1 :: (b ++ [1])).length = l.1.length + 1 := by
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega
  refine ⟨b, ?_, ?_⟩
  · rw [mulFirst_length]; exact hlen
  · show mulFirst u l'.1 = shiftPad (1 :: (b ++ [1])) (mulFirst u l.1)
    rw [hb, shiftPad_mulFirst u (1 :: (b ++ [1])) l.1 hbnd (by simp)]

end Work.ORHughesFree.Rat.FreeProduct
