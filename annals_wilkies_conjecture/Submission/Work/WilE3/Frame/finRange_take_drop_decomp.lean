import Mathlib

namespace Work.WilE3.Frame

theorem finRange_take_drop_decomp {k : ℕ} (l : Fin k) :
    List.finRange k = (List.finRange k).take l.val ++ l :: (List.finRange k).drop (l.val + 1) ∧
      l ∉ (List.finRange k).drop (l.val + 1) := by
  have hlen : l.val < (List.finRange k).length := by simp
  have hget : (List.finRange k)[l.val] = l := by
    rw [List.getElem_finRange hlen]; exact Fin.ext (by simp)
  constructor
  · -- The element `l` sits at position `l.val` of `finRange k`.
    have E1 : List.take l.val (List.finRange k) ++ l :: List.drop (l.val + 1) (List.finRange k)
        = List.take l.val (List.finRange k) ++ List.drop l.val (List.finRange k) := by
      congr 1
      nth_rewrite 1 [← hget]
      exact List.getElem_cons_drop hlen
    exact (E1.trans (List.take_append_drop l.val (List.finRange k))).symm
  · -- Every element of `drop (l.val + 1)` has value at least `l.val + 1`.
    intro hmem
    obtain ⟨i, hi, hii⟩ := List.mem_iff_getElem.mp hmem
    have hlen2 : l.val + 1 + i < (List.finRange k).length := by
      rw [List.length_drop] at hi; omega
    have h1 : (List.finRange k)[l.val + 1 + i] = l := by
      rw [← List.getElem_drop (xs := List.finRange k) (i := l.val + 1) (j := i)]; exact hii
    have h2 : ((List.finRange k)[l.val + 1 + i]).val = l.val + 1 + i := by
      rw [List.getElem_finRange hlen2]; simp
    rw [h1] at h2
    omega

end Work.WilE3.Frame
