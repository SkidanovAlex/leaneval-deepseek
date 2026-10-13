import Mathlib
import Submission.Work.WilE7.BandAux.bandCompTwo_defs

namespace Work.WilE7.BandAux

theorem bandSheetPartTwo_closed {p m k₁ k₂ : ℕ} {C : Set (Fin p → ℝ)}
    {s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    {s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    (hcont₁ : ∀ i, ContinuousOn (s₁ i) C) (hcont₂ : ∀ i, ContinuousOn (s₂ i) C)
    {G : Set (Fin (Work.WilE7.bandDim p m) → ℝ)}
    (hG : ∀ w ∈ G, Work.WilE7.BandAux.bandBase w ∈ C) (ij : Fin k₁ × Fin k₂) :
    IsClosed (Work.WilE7.BandAux.bandSheetPartTwo s₁ s₂ G ij) := by
  have hbase : Continuous (fun w : G => Work.WilE7.BandAux.bandBase w.1) :=
    continuous_bandBase.comp continuous_subtype_val
  have h2 : Continuous (fun w : G => Work.WilE7.bandZ2 w.1) :=
    continuous_bandZ2.comp continuous_subtype_val
  have h2' : Continuous (fun w : G => Work.WilE7.bandZ2' w.1) :=
    continuous_bandZ2'.comp continuous_subtype_val
  have hs1 : Continuous (fun w : G => s₁ ij.1 (Work.WilE7.BandAux.bandBase w.1)) :=
    (hcont₁ ij.1).comp_continuous hbase (fun w => hG w.1 w.2)
  have hs2 : Continuous (fun w : G => s₂ ij.2 (Work.WilE7.BandAux.bandBase w.1)) :=
    (hcont₂ ij.2).comp_continuous hbase (fun w => hG w.1 w.2)
  have hA1 : Continuous (fun w : G =>
      Fin.append (Work.WilE7.BandAux.bandBase w.1) (s₁ ij.1 (Work.WilE7.BandAux.bandBase w.1))) :=
    (Fin.continuous_append (X := ℝ) p (m + 1)).comp (hbase.prodMk hs1)
  have hA2 : Continuous (fun w : G =>
      Fin.append (Work.WilE7.BandAux.bandBase w.1) (s₂ ij.2 (Work.WilE7.BandAux.bandBase w.1))) :=
    (Fin.continuous_append (X := ℝ) p (m + 1)).comp (hbase.prodMk hs2)
  rw [show Work.WilE7.BandAux.bandSheetPartTwo s₁ s₂ G ij =
      {w : G | Work.WilE7.bandZ2 w.1 =
          Fin.append (Work.WilE7.BandAux.bandBase w.1) (s₁ ij.1 (Work.WilE7.BandAux.bandBase w.1))} ∩
      {w : G | Work.WilE7.bandZ2' w.1 =
          Fin.append (Work.WilE7.BandAux.bandBase w.1) (s₂ ij.2 (Work.WilE7.BandAux.bandBase w.1))}
      from by
    ext w
    simp only [Work.WilE7.BandAux.bandSheetPartTwo, Set.mem_ofPred_eq, Set.mem_inter_iff]]
  exact (isClosed_eq h2 hA1).inter (isClosed_eq h2' hA2)

end Work.WilE7.BandAux
