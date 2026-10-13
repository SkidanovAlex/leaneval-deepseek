import Mathlib
import Submission.Work.WilCrux.isCell_level_data
import Submission.Work.WilCrux.GR.StepZero
import Submission.Work.WilCrux.GR.StepGraph
import Submission.Work.WilCrux.GR.StepBand

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

/-! ## 10. The induction -/

theorem sheetData_word (m : ℕ) :
    ∀ (N : ℕ) (C₀ : Set (Fin m → ℝ)) (κ : Set (Fin (m + N) → ℝ)),
    IsOpen C₀ → IsCellOver m N C₀ κ → SheetData m N (word m N κ) κ := by
  intro N
  induction N with
  | zero =>
      intro C₀ κ hC₀ hκ
      exact sheetData_zero m C₀ κ hC₀ hκ
  | succ N ih =>
      intro C₀ κ hC₀ hκ
      obtain ⟨hne, hcell, hrec⟩ := hκ
      obtain ⟨-, -, hGB⟩ := isCell_level_data hcell hne
      have hdata' := ih C₀ (base κ) hC₀ hrec
      by_cases hg : IsGraphCellAt κ (base κ)
      · have hlev : levelType κ = CellType.graph := by
          unfold levelType
          exact ite_eq_left hg
        obtain ⟨f, hf, hκeq⟩ := hg
        have hword : word m (N + 1) κ = Fin.snoc (word m N (base κ)) CellType.graph := by
          rw [word_succ, hlev]
        rw [hword]
        exact sheetData_snoc_graph m N (word m N (base κ)) (base κ) hdata' f hf κ hκeq
      · have hlev : levelType κ = CellType.band := by
          unfold levelType
          exact ite_eq_right hg
        have hword : word m (N + 1) κ = Fin.snoc (word m N (base κ)) CellType.band := by
          rw [word_succ, hlev]
        rcases hGB with hg' | hb
        · exact absurd hg' hg
        · obtain ⟨a, b, ha, hbcont, hab, hκeq⟩ := hb
          rw [hword]
          exact sheetData_snoc_band m N (word m N (base κ)) (base κ) hdata' a b ha hbcont hab κ
            hκeq

/-! ## 11. The target -/

theorem graph_representation (m : ℕ) :
    ∀ (N : ℕ) (C₀ : Set (Fin m → ℝ)) (κ : Set (Fin (m + N) → ℝ)),
    IsOpen C₀ → Work.WilCrux.IsCellOver m N C₀ κ →
    ∃ (T : Set (Fin (m + Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) → ℝ))
      (φ : (Fin (m + Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) → ℝ) →
        (Fin (Work.WilCrux.nGraph N (Work.WilCrux.word m N κ)) → ℝ)),
      IsOpen T ∧ T.Nonempty ∧ ContinuousOn φ T ∧ (∀ v ∉ T, φ v = 0) ∧
      (∀ v u, Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ)) v u ∈ κ →
        v ∈ T) ∧
      (∀ v ∈ T, Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ)) v
        (φ v) ∈ κ) ∧
      (∀ z ∈ κ, ∃ v ∈ T, z = Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ)) v
        (φ v)) := by
  intro N C₀ κ hC₀ hκ
  obtain ⟨T, φ, hTne, hTopen, hφcont, hφ0, hproj, hrec, hsheet, hagree⟩ :=
    sheetData_word m N C₀ κ hC₀ hκ
  refine ⟨T, φ, hTopen, hTne, hφcont, hφ0, ?_, hsheet, ?_⟩
  · intro v u hvu
    have h := hproj _ hvu
    rwa [proj_sheetPtM (word m N κ) v u] at h
  · intro z hz
    exact ⟨fun i => z (selBand m (word m N κ) i), hproj z hz,
      by rw [hagree z hz, hrec z hz]⟩

end Work.WilCrux
