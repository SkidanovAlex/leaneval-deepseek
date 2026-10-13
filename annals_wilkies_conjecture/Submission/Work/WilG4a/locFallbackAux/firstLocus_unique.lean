import Mathlib

namespace Work.WilG4a.locFallbackAux

def firstLocus {m : ℕ} {α : Type*} (P : Fin m → Set α) : Fin m → Set α :=
  fun σ => P σ ∩ (⋃ τ : {τ : Fin m // τ < σ}, P τ.val)ᶜ

/-- Every nonempty family `P : Fin m → Set α` admits a minimal index `σ` with `l ∈ P σ`,
and `firstLocus P` selects exactly that index: `l ∈ firstLocus P σ'` forces `σ' = σ`. -/
theorem firstLocus_unique {m : ℕ} {α : Type*} (P : Fin m → Set α) {l : α}
    (h : ∃ σ, l ∈ P σ) :
    ∃ σ : Fin m, l ∈ P σ ∧ (∀ τ : Fin m, l ∈ P τ → σ ≤ τ) ∧
      ∀ σ' : Fin m, l ∈ firstLocus P σ' → σ' = σ := by
  classical
  obtain ⟨s0, hs0⟩ := h
  -- the set of values `n` attained by some index `σ` with `l ∈ P σ`
  have hex : ∃ n, ∃ σ : Fin m, σ.val = n ∧ l ∈ P σ := ⟨s0.val, s0, rfl, hs0⟩
  obtain ⟨σ0, hval, hmem⟩ := Nat.find_spec hex
  have hmin : ∀ τ : Fin m, l ∈ P τ → σ0 ≤ τ := by
    intro τ hτ
    rw [Fin.le_def, hval]
    exact Nat.find_min' hex ⟨τ, rfl, hτ⟩
  refine ⟨σ0, hmem, hmin, ?_⟩
  intro σ' hσ'
  have hmem' : l ∈ P σ' := hσ'.1
  have hnot : l ∉ (⋃ τ : {τ : Fin m // τ < σ'}, P τ.val) := hσ'.2
  -- `σ'` is below every index appearing in `P` and also below `σ0`
  have hle1 : σ' ≤ σ0 := by
    by_contra hc
    have hlt : σ0 < σ' := not_le.mp hc
    exact hnot (Set.mem_iUnion.mpr ⟨⟨σ0, hlt⟩, hmem⟩)
  exact le_antisymm hle1 (hmin σ' hmem')

end Work.WilG4a.locFallbackAux
