import Mathlib
import Submission.Work.DSCOH.Norm.FirstHomDefs
import Submission.Work.DSCOH.Norm.ReadFib.readAFiber

namespace Work.DSCOH.Norm.TelIdx2

open Work.DSCOH.Norm

/-- The head of size `a+1` is the head of size `a` together with the `a`-th sorted value. -/
lemma headVal_succ_eq_insert {ι : Type*} [LinearOrder ι] {m : ℕ}
    (x : Fin (m+1) → ι) (a : Fin m) :
    headVal x (Fin.succ a)
      = insert (Tuple.sort x (Fin.castSucc a)) (headVal x (Fin.castSucc a)) := by
  have hfilter : (Finset.univ.filter (fun j : Fin (m+1) => (j:ℕ) < (Fin.succ a : ℕ)))
      = insert (Fin.castSucc a)
          (Finset.univ.filter (fun j : Fin (m+1) => (j:ℕ) < (Fin.castSucc a : ℕ))) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    rw [Fin.val_succ, Fin.val_castSucc]
    constructor
    · intro h
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with h' | h'
      · exact Or.inr h'
      · exact Or.inl (Fin.ext (by rw [Fin.val_castSucc]; exact h'))
    · rintro (rfl | h)
      · rw [Fin.val_castSucc]; omega
      · omega
  rw [headVal, headVal, hfilter, Finset.image_insert]

theorem compl_headVal_succ_eq_erase {ι : Type*} [LinearOrder ι] [Fintype ι] {m : ℕ}
    (x : Fin (m+1) → ι) (a : Fin m) :
    (headVal x (Fin.succ a))ᶜ
      = (headVal x (Fin.castSucc a))ᶜ.erase (Tuple.sort x (Fin.castSucc a)) := by
  rw [headVal_succ_eq_insert x a, Finset.compl_insert]

end Work.DSCOH.Norm.TelIdx2
