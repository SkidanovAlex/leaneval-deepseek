import Mathlib

namespace Work.WilE7.SheetData

theorem lt_level_of_levelsAbove {k : ℕ} {L : Fin k → ℝ} (hL : Monotone L) (i : Fin k)
    (σ : Fin (k - i.val) → Fin k) (hσ : Function.Injective σ) {t : ℝ}
    (hσt : ∀ l, t < L (σ l)) : t < L i := by
  have hex : ∃ l, σ l ≤ i := by
    by_contra h
    simp only [not_exists, not_le] at h
    have hlt : ∀ l, i.val < (σ l).val := fun l => h l
    let f : Fin (k - i.val) → Fin (k - i.val - 1) := fun l =>
      ⟨(σ l).val - (i.val + 1), by
        have h1 : (σ l).val < k := (σ l).isLt
        have h2 : i.val < (σ l).val := hlt l
        omega⟩
    have hf : Function.Injective f := by
      intro l1 l2 heq
      have hv : (σ l1).val - (i.val + 1) = (σ l2).val - (i.val + 1) := congrArg Fin.val heq
      have h1 : i.val < (σ l1).val := hlt l1
      have h2 : i.val < (σ l2).val := hlt l2
      have hvv : (σ l1).val = (σ l2).val := by omega
      exact hσ (Fin.ext hvv)
    have hcard := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨l, hl⟩ := hex
  exact lt_of_lt_of_le (hσt l) (hL hl)

end Work.WilE7.SheetData
