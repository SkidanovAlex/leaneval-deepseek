import Mathlib
import Submission.Work.DSCOH.Norm.FirstHomDefs
import Submission.Work.DSCOH.Norm.ReadFib.readAFiber

namespace Work.DSCOH.Norm.TelIdx2

theorem tailEmb_succ_eq_lt {ι : Type*} [LinearOrder ι] [Fintype ι] {k : ℕ}
    (x : Fin (k+2) → ι) (a : Fin (k+1)) (i : Fin ((k+2) - (a:ℕ) - 1))
    (hi : (i:ℕ) < rankA x (Fin.castSucc a)) :
    tailEmb x (Fin.succ a) i =
      tailEmb x (Fin.castSucc a) ⟨(i:ℕ), by
        have h1 := rankA_lt x (Fin.castSucc a)
        rw [compl_card] at h1
        omega⟩ := by
  -- `c` is the value read at index `i` by the tail embedding of the slot `a` (shifted into the
  -- larger index set of `a+1`, which is the same value by proof irrelevance).
  set c : Fin ((k+2) - (↑(Fin.castSucc a))) := ⟨(i:ℕ), by
        have h1 := rankA_lt x (Fin.castSucc a)
        rw [compl_card] at h1
        omega⟩
  -- The head of the slot `a+1` is the head of the slot `a` together with the value `Tuple.sort x a`.
  have hcard : (headVal x (Fin.succ a))ᶜ
      = (headVal x (Fin.castSucc a))ᶜ.erase (Tuple.sort x (Fin.castSucc a)) := by
    have hint : headVal x (Fin.succ a)
        = insert (Tuple.sort x (Fin.castSucc a)) (headVal x (Fin.castSucc a)) := by
      ext v; rw [headVal, headVal]
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert]
      constructor
      · rintro ⟨j, hj, rfl⟩
        rw [Fin.val_succ] at hj
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with h | h
        · exact Or.inr ⟨j, h, rfl⟩
        · have hje : j = Fin.castSucc a := by ext; simpa using h
          exact Or.inl (congrArg (Tuple.sort x) hje)
      · rintro (h | ⟨j, hj, rfl⟩)
        · exact ⟨Fin.castSucc a, by rw [Fin.val_succ, Fin.val_castSucc]; omega, h.symm⟩
        · exact ⟨j, by simp only [Fin.val_succ, Fin.val_castSucc] at hj ⊢; omega, rfl⟩
    rw [hint]
    ext v
    rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_erase, Finset.mem_compl]
    tauto
  -- Below the rank of `Tuple.sort x a` the tails of the slots `a` and `a+1` agree.
  have hlt : tailEmb x (Fin.castSucc a) c < Tuple.sort x (Fin.castSucc a) := by
    rw [← Work.DSCOH.Norm.ReadFib.tailEmb_rankA x (Fin.castSucc a)]
    exact (tailEmb x (Fin.castSucc a)).lt_iff_lt.mpr (by rw [Fin.lt_def]; exact hi)
  refine (Work.DSCOH.Norm.ReadFib.tailEmb_eq_iff x (Fin.succ a) i
    (tailEmb x (Fin.castSucc a) c)).mpr ⟨?_, ?_⟩
  · rw [hcard, Finset.mem_erase]
    exact ⟨ne_of_lt hlt, Finset.mem_compl.mpr (tailEmb_mem x (Fin.castSucc a) c)⟩
  · rw [hcard, Finset.filter_erase]
    rw [Finset.erase_eq_self.mpr (by
      simp only [Finset.mem_filter]
      exact fun h => absurd h.2 (not_lt.mpr (le_of_lt hlt)))]
    exact ((Work.DSCOH.Norm.ReadFib.tailEmb_eq_iff x (Fin.castSucc a) c
      (tailEmb x (Fin.castSucc a) c)).mp rfl).2

end Work.DSCOH.Norm.TelIdx2
