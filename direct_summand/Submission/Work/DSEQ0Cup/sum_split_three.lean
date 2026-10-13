import Mathlib
import Submission.Work.DSEQ0.CupBasic

namespace Work.DSEQ0Cup

theorem sum_split_three (p q : ℕ) {M : Type*} [AddCommMonoid M] (f : Fin (p+q+2) → M) :
    ∑ k : Fin (p+q+2), f k =
      (∑ i : Fin (p+1), f ⟨i.val, by omega⟩) + ∑ j : Fin (q+1), f ⟨p+1+j.val, by omega⟩ := by
  have h : (p + 1) + (q + 1) = p + q + 2 := by omega
  rw [← Equiv.sum_comp (Fin.castOrderIso h).toEquiv f]
  exact Fin.sum_univ_add
    (fun a : Fin ((p + 1) + (q + 1)) => f ((Fin.castOrderIso h).toEquiv a))

end Work.DSEQ0Cup
