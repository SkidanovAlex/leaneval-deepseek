import Mathlib
import Submission.Work.DSCOH.Norm.FirstHomDefs
import Submission.Work.DSCOH.Norm.ReadFib.readAFiber
import Submission.Work.DSCOH.Norm.TelIdx2.compl_headVal_succ_eq_erase

namespace Work.DSCOH.Norm.TelIdx2

open Work.DSCOH.Norm

/-- **The upward index shift of the tail embedding, `≥` case.**  The two tail embeddings
`tailEmb x (Fin.castSucc a)` and `tailEmb x (Fin.succ a)` enumerate respectively the complement
`(headVal x (Fin.castSucc a))ᶜ` of the head values and that same complement with the value
`Tuple.sort x (Fin.castSucc a)` deleted (the latter sits at position
`rankA x (Fin.castSucc a)`).  Hence for indices `i` at or above `rankA x (Fin.castSucc a)` the
`i`-th entry of the smaller enumeration is the `(i+1)`-st entry of the larger one. -/
theorem tailEmb_succ_eq_ge {ι : Type*} [LinearOrder ι] [Fintype ι] {k : ℕ}
    (x : Fin (k+2) → ι) (a : Fin (k+1)) (i : Fin ((k+2) - (a:ℕ) - 1))
    (hi : rankA x (Fin.castSucc a) ≤ (i:ℕ)) :
    tailEmb x (Fin.succ a) i =
      tailEmb x (Fin.castSucc a) ⟨(i:ℕ)+1, by
        have h : (i:ℕ) + 1 < (k+2) - (a:ℕ) := by
          have := i.isLt; have := a.isLt; omega
        exact h⟩ := by
  have hbound : (i:ℕ) + 1 < (k+2) - (a:ℕ) := by
    have := i.isLt; have := a.isLt; omega
  show tailEmb x (Fin.succ a) i
      = tailEmb x (Fin.castSucc a) (⟨(i:ℕ)+1, hbound⟩ : Fin ((k+2) - (a:ℕ)))
  set j : Fin ((k+2) - (a:ℕ)) := ⟨(i:ℕ)+1, hbound⟩ with hj
  have hjv : (j:ℕ) = (i:ℕ)+1 := by rw [hj]
  -- `Tuple.sort x (Fin.castSucc a)` is the `rankA x (Fin.castSucc a)`-th entry of the larger
  -- enumeration.
  have hrank : Tuple.sort x (Fin.castSucc a)
      = tailEmb x (Fin.castSucc a) ⟨rankA x (Fin.castSucc a), by
          have h1 := rankA_lt x (Fin.castSucc a); rw [compl_card] at h1; exact h1⟩ :=
    (ReadFib.tailEmb_rankA x (Fin.castSucc a)).symm
  refine (ReadFib.tailEmb_eq_iff x (Fin.succ a) i (tailEmb x (Fin.castSucc a) j)).mpr
    ⟨?_, ?_⟩
  · -- the value `tailEmb x (Fin.castSucc a) j` survives the deletion, i.e. it is not
    -- `Tuple.sort x (Fin.castSucc a)`
    rw [compl_headVal_succ_eq_erase]
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_compl.mpr (tailEmb_mem x (Fin.castSucc a) j)⟩
    intro hc
    rw [hrank] at hc
    have h2 := (tailEmb x (Fin.castSucc a)).injective hc
    have h3 : (j:ℕ) = rankA x (Fin.castSucc a) := by simpa using congrArg Fin.val h2
    omega
  · -- the count of entries below `tailEmb x (Fin.castSucc a) j` increases by one on deleting
    -- the (strictly smaller) value `Tuple.sort x (Fin.castSucc a)`
    rw [compl_headVal_succ_eq_erase, Finset.filter_erase]
    have hcard : (((headVal x (Fin.castSucc a))ᶜ).filter
        (fun v => v < tailEmb x (Fin.castSucc a) j)).card = (j:ℕ) :=
      ReadFib.card_filter_lt_of_orderEmbOfFin_eq (compl_card x (Fin.castSucc a)) rfl
    have hmem : Tuple.sort x (Fin.castSucc a) ∈ ((headVal x (Fin.castSucc a))ᶜ).filter
        (fun v => v < tailEmb x (Fin.castSucc a) j) := by
      simp only [Finset.mem_filter]
      refine ⟨sortA_mem_compl x (Fin.castSucc a), ?_⟩
      rw [hrank]
      refine (tailEmb x (Fin.castSucc a)).lt_iff_lt.mpr ?_
      have h3 : rankA x (Fin.castSucc a) < (j:ℕ) := by omega
      exact h3
    rw [Finset.card_erase_of_mem hmem, hcard, hjv]
    omega

end Work.DSCOH.Norm.TelIdx2
