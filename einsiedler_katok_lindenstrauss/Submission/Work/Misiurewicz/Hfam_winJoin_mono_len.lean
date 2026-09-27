import Mathlib
import Submission.Work.Misiurewicz.Hfam_winJoin_grid

/-!
# Monotonicity of `Hfam` of a window join in the window length

`winJoin T P k N w = ⋂_{j < N} T^{-(j+k)} (P.parts (w j))` observes the orbit of a point over
the time window `[k, k+N)`.  Writing `ρ : (Fin L' → Fin P.n) → (Fin L → Fin P.n)` for the
restriction `w' ↦ w' ∘ Fin.castLE h` (defined when `h : L ≤ L'`), every atom of the shorter
window join contains the corresponding atom of the longer one:

`winJoin T P k L' w' ⊆ winJoin T P k L (ρ w')`.

Shannon entropy is monotone under refinement of a finite measurable partition
(`Work.EKLComp.Core.Hfam_mono`), so `Hfam μ (winJoin T P k L) ≤ Hfam μ (winJoin T P k L')`.
-/

namespace Work.Misiurewicz

open Work.EKLContract Work.EKLComp

/-- Entropy of the window join is monotone in the window length: a longer window `L'` observes
more time steps than a shorter window `L ≤ L'`, so its partition is finer and has larger
Shannon entropy. -/
theorem Hfam_winJoin_mono_len (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ]
    (T : Work.EKLContract.X3 → Work.EKLContract.X3) (hT : Measurable T)
    (P : Work.EKLContract.FinPart Work.EKLContract.X3) (k : ℕ) {L L' : ℕ} (h : L ≤ L') :
    Work.EKLContract.Hfam μ (Work.EKLComp.winJoin T P k L) ≤
      Work.EKLContract.Hfam μ (Work.EKLComp.winJoin T P k L') := by
  classical
  -- restrict a word `w' : Fin L' → Fin P.n` to `Fin L ≃ Fin.castLE h`
  refine Work.EKLComp.Core.Hfam_mono μ (winJoin_isMPart hT P k L) (winJoin_isMPart hT P k L')
    (fun w' : Fin L' → Fin P.n => fun j : Fin L => w' (Fin.castLE h j)) ?_
  intro w' x hx
  simp only [Work.EKLComp.winJoin, Set.mem_iInter, Set.mem_preimage] at hx ⊢
  intro j
  exact hx (Fin.castLE h j)

end Work.Misiurewicz
