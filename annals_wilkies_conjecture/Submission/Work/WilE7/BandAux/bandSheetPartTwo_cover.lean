import Mathlib
import Submission.Work.WilE7.BandAux.bandCompTwo_defs

namespace Work.WilE7.BandAux
open Work.WilE7 WilkiesDesign WilkiesDesign.E

theorem bandSheetPartTwo_cover {p m k₁ k₂ : ℕ} (S₁ S₂ : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) {C : Set (Fin p → ℝ)}
    {s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    {s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    (hcov₁ : ∀ z ∈ S₁.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ i : Fin k₁, s₁ i (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hcov₂ : ∀ z ∈ S₂.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ i : Fin k₂, s₂ i (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    {G : Set (Fin (Work.WilE7.bandDim p m) → ℝ)}
    (hG : ∀ w ∈ G, w ∈ (Work.WilE7.bandS3two Z S₁ S₂).set ∧
      Work.WilE7.BandAux.bandBase w ∈ C) :
    ∀ x : G, ∃ ij : Fin k₁ × Fin k₂, x ∈ Work.WilE7.BandAux.bandSheetPartTwo s₁ s₂ G ij := by
  intro x
  have hxS3 : x.1 ∈ (bandS3two Z S₁ S₂).set := (hG x.1 x.2).1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -, -⟩ := (bandS3two_mem_iff Z S₁ S₂ x.1).mp hxS3
  have hxb : bandBase x.1 ∈ C := (hG x.1 x.2).2
  have hb2 : projFirst p (m + 1) (bandZ2 x.1) ∈ C := by rw [← h5]; exact hxb
  have hb4 : projFirst p (m + 1) (bandZ2' x.1) ∈ C := by
    rw [← (congrArg (projFirst p (m + 1)) h7).trans h6]
    exact hxb
  obtain ⟨a, ha⟩ := hcov₁ (bandZ2 x.1) h2 hb2
  obtain ⟨b, hb⟩ := hcov₂ (bandZ2' x.1) h4 hb4
  refine ⟨(a, b), ?_⟩
  rw [mem_bandSheetPartTwo]
  constructor
  · show bandZ2 x.1 = Fin.append (bandBase x.1) (s₁ a (bandBase x.1))
    show bandZ2 x.1 = Fin.append (projFirst p (m + 1) (bandZ1 x.1))
      (s₁ a (projFirst p (m + 1) (bandZ1 x.1)))
    rw [h5, ha]
    exact (append_projFirst_projSnd (bandZ2 x.1)).symm
  · show bandZ2' x.1 = Fin.append (bandBase x.1) (s₂ b (bandBase x.1))
    show bandZ2' x.1 = Fin.append (projFirst p (m + 1) (bandZ1 x.1))
      (s₂ b (projFirst p (m + 1) (bandZ1 x.1)))
    rw [show projFirst p (m + 1) (bandZ1 x.1) = projFirst p (m + 1) (bandZ2' x.1) from
      (congrArg (projFirst p (m + 1)) h7).trans h6, hb]
    exact (append_projFirst_projSnd (bandZ2' x.1)).symm

end Work.WilE7.BandAux
