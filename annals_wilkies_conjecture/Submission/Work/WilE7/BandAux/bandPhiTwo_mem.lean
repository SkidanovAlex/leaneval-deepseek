import Mathlib
import Submission.Work.WilE7.BandAux.bandCoverTwo_defs

namespace Work.WilE7.BandAux

open Work.WilE7 WilkiesDesign WilkiesDesign.E

theorem bandPhiTwo_mem {p m : ℕ} (S₁ S₂ : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (u₀ : Fin (p + (m + 1)) → ℝ) (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k₁ : ℕ) (s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hsub₁ : ∀ i : Fin k₁, ∀ x ∈ C, Fin.append x (s₁ i x) ∈ S₁.X.set)
    (k₂ : ℕ) (s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hsub₂ : ∀ i : Fin k₂, ∀ x ∈ C, Fin.append x (s₂ i x) ∈ S₂.X.set)
    (i : Fin k₁) (j : Fin k₂) :
    ∀ q ∈ Work.WilE7.BandAux.bandHtwo Z s₁ s₂ i j u₀,
      Work.WilE7.BandAux.bandPhiTwo s₁ s₂ i j q ∈ (Work.WilE7.bandS3two Z S₁ S₂).set := by
  intro q hq
  rw [bandHtwo_mem_iff] at hq
  obtain ⟨hqc, hqa, hqb⟩ := hq
  have hx : projFirst p (m + 1) q.1 ∈ C := by
    rw [hC]; exact ⟨q.1, hqc, rfl⟩
  have hsub_i := hsub₁ i _ hx
  have hsub_j := hsub₂ j _ hx
  have hbi : |(s₁ i (projFirst p (m + 1) q.1)) (Fin.last m)| ≤ 1 := by
    have h := hsub_i.1 (Fin.natAdd p (Fin.last m))
    rwa [Fin.append_right] at h
  have hbj : |(s₂ j (projFirst p (m + 1) q.1)) (Fin.last m)| ≤ 1 := by
    have h := hsub_j.1 (Fin.natAdd p (Fin.last m))
    rwa [Fin.append_right] at h
  have hqa' : (s₁ i (projFirst p (m + 1) q.1)) (Fin.last m) < q.2 := by
    have h := hqa
    simp only [bandLevel] at h
    exact EReal.coe_lt_coe_iff.mp h
  have hqb' : q.2 < (s₂ j (projFirst p (m + 1) q.1)) (Fin.last m) := by
    have h := hqb
    simp only [bandLevel] at h
    exact EReal.coe_lt_coe_iff.mp h
  have hcube : |q.2| ≤ 1 := by
    have h1' : -1 ≤ (s₁ i (projFirst p (m + 1) q.1)) (Fin.last m) := (abs_le.mp hbi).1
    have h2' : (s₂ j (projFirst p (m + 1) q.1)) (Fin.last m) ≤ 1 := (abs_le.mp hbj).2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [bandPhiTwo_apply]
  exact bandPt_mem_two Z S₁ S₂ q.1 (connectedComponentIn_subset Z.set u₀ hqc)
    (s₁ i (projFirst p (m + 1) q.1)) (s₂ j (projFirst p (m + 1) q.1)) q.2
    hsub_i hsub_j hcube hqa' hqb'

end Work.WilE7.BandAux
