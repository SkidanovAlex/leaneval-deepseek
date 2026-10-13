import Submission.Work.WilCrux.GR.Helpers

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

/-! ## 7. The base case -/

theorem selBand_word_zero (m : ℕ) (w : Fin 0 → CellType) (i : Fin (m + nBand 0 w)) :
    selBand m w i = i := by
  refine Fin.addCases (m := m) (n := nBand 0 w) (motive := fun i => selBand m w i = i) ?_ ?_ i
  · intro i'
    rw [selBand_castAdd]
    exact Fin.ext rfl
  · intro k
    exact Fin.elim0 k

theorem sheetPtM_word_zero (m : ℕ) (w : Fin 0 → CellType) (v : Fin (m + nBand 0 w) → ℝ)
    (u : Fin (nGraph 0 w) → ℝ) : sheetPtM (wordEquiv w) v u = v := by
  funext i
  have hi : i = (Fin.castAdd 0 (⟨i.val, by simpa using i.isLt⟩ : Fin m) : Fin (m + 0)) :=
    Fin.ext rfl
  rw [hi, sheetPtM]
  simp only [Fin.append_left]
  rfl

theorem sheetData_zero (m : ℕ) (C₀ : Set (Fin m → ℝ)) (κ : Set (Fin (m + 0) → ℝ))
    (hC₀ : IsOpen C₀) (hκ : IsCellOver m 0 C₀ κ) :
    SheetData m 0 (word m 0 κ) κ := by
  obtain ⟨hκeq, hne⟩ := hκ
  have hsel : ∀ (z : Fin (m + 0) → ℝ), (fun i => z (selBand m (word m 0 κ) i)) = z :=
    fun z => funext fun i => by rw [selBand_word_zero m (word m 0 κ) i]
  refine ⟨κ, fun _ => 0, hne, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hκeq]; exact hC₀
  · exact continuousOn_const
  · intro v hv
    rfl
  · intro z hz
    exact Eq.mp (congrArg (fun w => w ∈ κ) (hsel z).symm) hz
  · intro z hz
    exact (sheetPtM_word_zero m (word m 0 κ) (fun i => z (selBand m (word m 0 κ) i))
      (fun k => z (Fin.natAdd m (graphIdx (word m 0 κ) k)))).trans (hsel z)
  · intro v hv
    show sheetPtM (wordEquiv (word m 0 κ)) v 0 ∈ κ
    rw [sheetPtM_word_zero m (word m 0 κ) v 0]
    exact hv
  · intro z hz
    refine funext fun k => ?_
    exact Fin.elim0 (graphIdx (word m 0 κ) k)


end Work.WilCrux
