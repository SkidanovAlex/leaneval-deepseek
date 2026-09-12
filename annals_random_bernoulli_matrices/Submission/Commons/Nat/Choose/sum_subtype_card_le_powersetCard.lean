import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic

namespace Commons.Nat.Choose

open Finset
open scoped BigOperators

/-- Reindexing identity (real version): the sum over all subsets `B` of `Fin m` with `B.card ≤ r`
of `α^(m − B.card)` equals the sum over `ℓ ≤ r` of the sum over the `ℓ`-element subsets
(`powersetCard ℓ univ`), of `α^(m − B.card)`. -/
theorem sum_subtype_card_le_powersetCard {m r : ℕ} (α : ℝ) :
    (∑ B : {B : Finset (Fin m) // B.card ≤ r}, α ^ (m - (B : Finset (Fin m)).card)) =
      ∑ ℓ ∈ Finset.range (r + 1),
        ∑ B ∈ (Finset.univ : Finset (Fin m)).powersetCard ℓ, α ^ (m - B.card) := by
  let A : Finset (Finset (Fin m)) :=
    (Finset.range (r + 1)).biUnion fun ℓ => (Finset.univ : Finset (Fin m)).powersetCard ℓ
  have hA : ∀ B : Finset (Fin m), B ∈ A ↔ B.card ≤ r := by
    intro B
    dsimp [A]
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨ℓ, hℓ, hB⟩
      have hℓ_le : ℓ ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hℓ)
      have hBcard : B.card = ℓ := (Finset.mem_powersetCard.mp hB).2
      rw [hBcard]
      exact hℓ_le
    · intro hBr
      refine ⟨B.card, ?_, ?_⟩
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hBr)
      · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ B, rfl⟩
  have hdisj : (↑(Finset.range (r + 1)) : Set ℕ).PairwiseDisjoint
      (fun ℓ => (Finset.univ : Finset (Fin m)).powersetCard ℓ) := by
    intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ hne
    change Disjoint ((Finset.univ : Finset (Fin m)).powersetCard ℓ₁)
      ((Finset.univ : Finset (Fin m)).powersetCard ℓ₂)
    rw [Finset.disjoint_left]
    intro B hB₁ hB₂
    have h₁ : B.card = ℓ₁ := (Finset.mem_powersetCard.mp hB₁).2
    have h₂ : B.card = ℓ₂ := (Finset.mem_powersetCard.mp hB₂).2
    exact hne (h₁.symm.trans h₂)
  calc
    (∑ B : {B : Finset (Fin m) // B.card ≤ r}, α ^ (m - (B : Finset (Fin m)).card))
        = ∑ B ∈ A, α ^ (m - B.card) := by
          rw [← Finset.sum_subtype (s := A) (p := fun B : Finset (Fin m) => B.card ≤ r)
            (f := fun B => α ^ (m - B.card)) (h := hA)]
    _ = ∑ ℓ ∈ Finset.range (r + 1),
          ∑ B ∈ (Finset.univ : Finset (Fin m)).powersetCard ℓ, α ^ (m - B.card) := by
          dsimp [A]
          rw [Finset.sum_biUnion (s := Finset.range (r + 1))
            (t := fun ℓ => (Finset.univ : Finset (Fin m)).powersetCard ℓ)
            (f := fun B => α ^ (m - B.card)) hdisj]

end Commons.Nat.Choose