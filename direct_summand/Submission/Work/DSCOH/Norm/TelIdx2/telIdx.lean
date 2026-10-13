import Mathlib
import Submission.Work.DSCOH.Norm.FirstHomDefs
import Submission.Work.DSCOH.Norm.ReadFib.readAFiber
import Submission.Work.DSCOH.Norm.TelIdx2.tailEmb_succ_eq_lt
import Submission.Work.DSCOH.Norm.TelIdx2.tailEmb_succ_eq_ge

namespace Work.DSCOH.Norm.TelIdx2

open Work.DSCOH.Norm

set_option maxHeartbeats 1000000

/-- `tailEmb x a` only depends on the value of its index: two indices of `Fin ((k+1) - a)` with the
same underlying natural number give the same entry of the increasing enumeration of the complement
of the head values.  (Helper for `telIdx`.) -/
lemma tailEmb_congr_val {ι : Type*} [LinearOrder ι] [Fintype ι] {k : ℕ}
    (x : Fin (k+1) → ι) (a : Fin (k+1)) {i j : Fin ((k+1) - (a:ℕ))}
    (h : (i:ℕ) = (j:ℕ)) : tailEmb x a i = tailEmb x a j :=
  congrArg _ (Fin.ext h)

/-- **The index identity of the "telescoping" of the leftover terms** of the first (sorting)
homotopy of Stacks 20.23.6.  For `x : Fin (k+2) → ι` and a slot `a : Fin (k+1)` (so that the
next slot `a+1 : Fin (k+2)` makes sense), deleting the position `pos2A x a` of the `a`-th read
of `x` gives the same index map as deleting the position `a+1` of the `(a+1)`-st read of `x`. -/
theorem telIdx {ι : Type*} [LinearOrder ι] [Fintype ι] {k : ℕ} (x : Fin (k+2) → ι)
    (a : Fin (k+1)) :
    Work.DSCOH.Norm.readA x (Fin.castSucc a) ∘
        (Fin.succAbove (Work.DSCOH.Norm.pos2A x (Fin.castSucc a))) =
      Work.DSCOH.Norm.readA x (Fin.succ a) ∘ (Fin.succAbove ((Fin.succ a).castSucc)) := by

  funext p
  show readA x (Fin.castSucc a) (Fin.succAbove (pos2A x (Fin.castSucc a)) p)
      = readA x (Fin.succ a) (Fin.succAbove ((Fin.succ a).castSucc) p)
  have hPv : ((pos2A x (Fin.castSucc a) : Fin (k+3)) : ℕ)
      = (a:ℕ) + 1 + rankA x (Fin.castSucc a) := rfl
  by_cases hp1 : (p:ℕ) ≤ (a:ℕ)
  · have hP : (Fin.castSucc p : Fin (k+3)) < pos2A x (Fin.castSucc a) := by
      show (p:ℕ) < ((pos2A x (Fin.castSucc a) : Fin (k+3)) : ℕ)
      rw [hPv]; omega
    have hQ : (Fin.castSucc p : Fin (k+3)) < (Fin.succ a).castSucc := by
      show (p:ℕ) < (((Fin.succ a).castSucc : Fin (k+3)) : ℕ)
      simp only [Fin.val_castSucc, Fin.val_succ]; omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hP, Fin.succAbove_of_castSucc_lt _ _ hQ]
    rw [readA_head x (Fin.castSucc a) (by simpa only [Fin.val_castSucc] using hp1),
        readA_head x (Fin.succ a) (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)]
  · push_neg at hp1
    by_cases hp2 : (p:ℕ) < ((pos2A x (Fin.castSucc a) : Fin (k+3)) : ℕ)
    · have hP : (Fin.castSucc p : Fin (k+3)) < pos2A x (Fin.castSucc a) := by
        show (p:ℕ) < ((pos2A x (Fin.castSucc a) : Fin (k+3)) : ℕ)
        exact hp2
      have hQ : (Fin.succ a).castSucc ≤ (Fin.castSucc p : Fin (k+3)) := by
        show (((Fin.succ a).castSucc : Fin (k+3)) : ℕ) ≤ (p:ℕ)
        simp only [Fin.val_castSucc, Fin.val_succ]; omega
      rw [Fin.succAbove_of_castSucc_lt _ _ hP, Fin.succAbove_of_le_castSucc _ _ hQ]
      have hp2' : (p:ℕ) < (a:ℕ) + 1 + rankA x (Fin.castSucc a) := by rw [← hPv]; exact hp2
      have hb1 : (p:ℕ) - 1 - (a:ℕ) < (k+2) - (a:ℕ) := by
        have := p.isLt; have := a.isLt; omega
      have hb2 : (p:ℕ) - 1 - (a:ℕ) < (k+2) - (a:ℕ) - 1 := by
        have h1 := rankA_lt x (Fin.castSucc a); rw [compl_card] at h1
        have := p.isLt; omega
      have hL : readA x (Fin.castSucc a) (Fin.castSucc p)
          = tailEmb x (Fin.castSucc a) (⟨(p:ℕ) - 1 - (a:ℕ), hb1⟩ : Fin ((k+2) - (a:ℕ))) := by
        rw [readA_tail x (Fin.castSucc a) (by
          show ¬ ((↑(Fin.castSucc p) : ℕ) ≤ (↑(Fin.castSucc a) : ℕ))
          simp only [Fin.val_castSucc]; omega)]
        refine tailEmb_congr_val x (Fin.castSucc a) ?_
        show (↑(Fin.castSucc p) : ℕ) - 1 - (↑(Fin.castSucc a) : ℕ) = (p:ℕ) - 1 - (a:ℕ)
        simp only [Fin.val_castSucc]
      have hR : readA x (Fin.succ a) (Fin.succ p)
          = tailEmb x (Fin.succ a)
              (⟨(p:ℕ) - 1 - (a:ℕ), hb2⟩ : Fin ((k+2) - (a:ℕ) - 1)) := by
        rw [readA_tail x (Fin.succ a) (by
          show ¬ ((↑(Fin.succ p) : ℕ) ≤ (↑(Fin.succ a) : ℕ))
          simp only [Fin.val_succ]; omega)]
        refine tailEmb_congr_val x (Fin.succ a) ?_
        show (↑(Fin.succ p) : ℕ) - 1 - (↑(Fin.succ a) : ℕ) = (p:ℕ) - 1 - (a:ℕ)
        simp only [Fin.val_succ]; omega
      rw [hL, hR, tailEmb_succ_eq_lt x a ⟨(p:ℕ) - 1 - (a:ℕ), hb2⟩
        (by show (p:ℕ) - 1 - (a:ℕ) < rankA x (Fin.castSucc a); omega)]
    · push_neg at hp2
      have hp2' : (a:ℕ) + 1 + rankA x (Fin.castSucc a) ≤ (p:ℕ) := by rw [← hPv]; exact hp2
      have hP : pos2A x (Fin.castSucc a) ≤ (Fin.castSucc p : Fin (k+3)) := by
        show ((pos2A x (Fin.castSucc a) : Fin (k+3)) : ℕ) ≤ (p:ℕ)
        rw [hPv]; exact hp2
      have hQ : (Fin.succ a).castSucc ≤ (Fin.castSucc p : Fin (k+3)) := by
        show (((Fin.succ a).castSucc : Fin (k+3)) : ℕ) ≤ (p:ℕ)
        simp only [Fin.val_castSucc, Fin.val_succ]; omega
      rw [Fin.succAbove_of_le_castSucc _ _ hP, Fin.succAbove_of_le_castSucc _ _ hQ]
      have hd1 : (p:ℕ) - (a:ℕ) < (k+2) - (a:ℕ) := by
        have := p.isLt; have := a.isLt; omega
      have hd2 : (p:ℕ) - (a:ℕ) - 1 < (k+2) - (a:ℕ) - 1 := by
        have := p.isLt; have := a.isLt; omega
      have hL : readA x (Fin.castSucc a) (Fin.succ p)
          = tailEmb x (Fin.castSucc a) (⟨(p:ℕ) - (a:ℕ), hd1⟩ : Fin ((k+2) - (a:ℕ))) := by
        rw [readA_tail x (Fin.castSucc a) (by
          show ¬ ((↑(Fin.succ p) : ℕ) ≤ (↑(Fin.castSucc a) : ℕ))
          simp only [Fin.val_succ, Fin.val_castSucc]; omega)]
        refine tailEmb_congr_val x (Fin.castSucc a) ?_
        show (↑(Fin.succ p) : ℕ) - 1 - (↑(Fin.castSucc a) : ℕ) = (p:ℕ) - (a:ℕ)
        simp only [Fin.val_succ, Fin.val_castSucc]; omega
      have hR : readA x (Fin.succ a) (Fin.succ p)
          = tailEmb x (Fin.succ a)
              (⟨(p:ℕ) - (a:ℕ) - 1, hd2⟩ : Fin ((k+2) - (a:ℕ) - 1)) := by
        rw [readA_tail x (Fin.succ a) (by
          show ¬ ((↑(Fin.succ p) : ℕ) ≤ (↑(Fin.succ a) : ℕ))
          simp only [Fin.val_succ]; omega)]
        refine tailEmb_congr_val x (Fin.succ a) ?_
        show (↑(Fin.succ p) : ℕ) - 1 - (↑(Fin.succ a) : ℕ) = (p:ℕ) - (a:ℕ) - 1
        simp only [Fin.val_succ]; omega
      rw [hL, hR, tailEmb_succ_eq_ge x a ⟨(p:ℕ) - (a:ℕ) - 1, hd2⟩
        (by show rankA x (Fin.castSucc a) ≤ (p:ℕ) - (a:ℕ) - 1; omega)]
      refine tailEmb_congr_val x (Fin.castSucc a) ?_
      show (p:ℕ) - (a:ℕ) = (↑(⟨(p:ℕ) - (a:ℕ) - 1, hd2⟩ : Fin ((k+2) - (a:ℕ) - 1)) : ℕ) + 1
      have hpa : (a:ℕ) + 1 ≤ (p:ℕ) := by omega
      simp only [Fin.val_mk]
      omega

end Work.DSCOH.Norm.TelIdx2
