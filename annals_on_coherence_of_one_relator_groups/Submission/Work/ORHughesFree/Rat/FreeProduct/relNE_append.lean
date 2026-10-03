import Mathlib
import Submission.Work.ORHughesFree.Rat.FreeProduct.NU
import Submission.Work.ORHughesFree.Rat.FreeProduct.shiftPad_append_right

namespace Work.ORHughesFree.Rat.FreeProduct

theorem relNE_append {U : Type} [Group U] {l₁ l₁' l₂ l₂' : Work.ORHughesFree.Rat.FreeProduct.NEL (U := U)}
    (h₁ : Work.ORHughesFree.Rat.FreeProduct.relNE l₁ l₁')
    (h₂ : Work.ORHughesFree.Rat.FreeProduct.relNE l₂ l₂') :
    Work.ORHughesFree.Rat.FreeProduct.relNE
      ⟨l₁.1 ++ l₂.1, by simp [l₁.2]⟩ ⟨l₁'.1 ++ l₂'.1, by simp [l₁'.2]⟩ := by
  obtain ⟨b₁, hlen₁, hb₁⟩ := h₁
  obtain ⟨b₂, hlen₂, hb₂⟩ := h₂
  refine ⟨b₁ ++ [1] ++ b₂, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · show l₁'.1 ++ l₂'.1
        = shiftPad (1 :: ((b₁ ++ [1] ++ b₂) ++ [1])) (l₁.1 ++ l₂.1)
    have hparam : (1 : U) :: ((b₁ ++ [1] ++ b₂) ++ [1])
        = (1 :: (b₁ ++ [1])) ++ (b₂ ++ [1]) := by simp [List.append_assoc]
    have hgl : ((1 :: (b₁ ++ [1])) : List U).getLastD 1 = 1 := by
      rw [List.getLastD_cons, List.getLastD_concat]
    have hlen₁' : (1 :: (b₁ ++ [1])).length = l₁.1.length + 1 := by
      simp only [List.length_cons, List.length_append, List.length_nil]
      omega
    rw [hb₁, hb₂]
    rw [hparam, shiftPad_append_split (1 :: (b₁ ++ [1])) (b₂ ++ [1]) l₁.1 l₂.1 hlen₁', hgl]

end Work.ORHughesFree.Rat.FreeProduct
