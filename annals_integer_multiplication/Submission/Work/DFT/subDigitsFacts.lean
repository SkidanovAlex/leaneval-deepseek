import Mathlib
import Submission.Work.DFT.dftDefs

namespace Work.DFT

theorem subDigitsFacts (ts X Y : List ℕ) (hpos : ∀ t ∈ ts, 0 < t)
    (hX : X.length = ts.length) (hY : Y.length = ts.length) :
    (HvdH.subDigits ts X Y).length = ts.length ∧
    (∀ i < ts.length, (HvdH.subDigits ts X Y).getD i 0 < ts.getD i 0) ∧
    (∀ i < ts.length, (HvdH.subDigits ts X Y).getD i 0 =
      (X.getD i 0 + ts.getD i 0 - Y.getD i 0) % ts.getD i 0) := by
  induction ts generalizing X Y with
  | nil => simp [HvdH.subDigits]
  | cons t ts ih =>
      obtain ⟨x, X', rfl⟩ : ∃ x X', X = x :: X' := by
        cases X with
        | nil => simp at hX
        | cons x X' => exact ⟨x, X', rfl⟩
      obtain ⟨y, Y', rfl⟩ : ∃ y Y', Y = y :: Y' := by
        cases Y with
        | nil => simp at hY
        | cons y Y' => exact ⟨y, Y', rfl⟩
      simp only [List.length_cons, Nat.succ.injEq] at hX hY
      have ht : 0 < t := hpos t (by simp)
      have hpos' : ∀ u ∈ ts, 0 < u := fun u hu => hpos u (by simp [hu])
      obtain ⟨ihl, ihl2, ihl3⟩ := ih X' Y' hpos' hX hY
      refine ⟨by simp [HvdH.subDigits, ihl], ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => simpa [HvdH.subDigits, List.getD_cons_zero] using Nat.mod_lt (x + t - y) ht
        | succ i => simpa [HvdH.subDigits, List.getD_cons_succ] using ihl2 i (by simpa using hi)
      · intro i hi
        cases i with
        | zero => simp [HvdH.subDigits, List.getD_cons_zero]
        | succ i => simpa [HvdH.subDigits, List.getD_cons_succ] using ihl3 i (by simpa using hi)

end Work.DFT
