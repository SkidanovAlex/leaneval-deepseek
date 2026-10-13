import Mathlib
import Submission.Work.WilE7.BandAux.bandCompTwo_defs

namespace Work.WilE7.BandAux

/-- Projection of `Fin.append` onto its right summand: if two `Fin.append`s agree, so do the
appended tuples. -/
theorem fin_append_right_inj {m n : ℕ} {α : Type*} (a : Fin m → α) {b c : Fin n → α}
    (h : Fin.append a b = Fin.append a c) : b = c := by
  funext i
  have h' := congrFun h (Fin.natAdd m i)
  rwa [Fin.append_right, Fin.append_right] at h'

theorem bandSheetPartTwo_disjoint {p m k₁ k₂ : ℕ} {C : Set (Fin p → ℝ)}
    {s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    {s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    (hinj₁ : ∀ x ∈ C, Function.Injective fun i : Fin k₁ => s₁ i x)
    (hinj₂ : ∀ x ∈ C, Function.Injective fun i : Fin k₂ => s₂ i x)
    {G : Set (Fin (Work.WilE7.bandDim p m) → ℝ)}
    (hG : ∀ w ∈ G, Work.WilE7.BandAux.bandBase w ∈ C)
    {ij ij' : Fin k₁ × Fin k₂} (hij : ij ≠ ij') :
    Disjoint (Work.WilE7.BandAux.bandSheetPartTwo s₁ s₂ G ij)
      (Work.WilE7.BandAux.bandSheetPartTwo s₁ s₂ G ij') := by
  rw [Set.disjoint_left]
  intro w h1 h2
  rw [mem_bandSheetPartTwo] at h1 h2
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  have hbC : bandBase w.1 ∈ C := hG w.1 w.2
  have e₁ : s₁ ij.1 (bandBase w.1) = s₁ ij'.1 (bandBase w.1) := by
    apply fin_append_right_inj (bandBase w.1)
    rw [← h1a, h2a]
  have e₂ : s₂ ij.2 (bandBase w.1) = s₂ ij'.2 (bandBase w.1) := by
    apply fin_append_right_inj (bandBase w.1)
    rw [← h1b, h2b]
  have hi : ij.1 = ij'.1 := (hinj₁ (bandBase w.1) hbC) e₁
  have hj : ij.2 = ij'.2 := (hinj₂ (bandBase w.1) hbC) e₂
  exact hij (Prod.ext hi hj)

end Work.WilE7.BandAux
