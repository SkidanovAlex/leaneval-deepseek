/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.Peluse.ExpA.Defs

/-!
# Reindexing the slot product

The product over all **nonzero** sign patterns `ω : Fin s → Bool` of a function `G` equals the
product over `i : Fin (2 ^ s - 1)` of `G (slotIdx s i.succ)`.

This is the reindexing used when the `a`-average of the expansion is written as the multilinear
average over the `2 ^ s - 1` phase-carrying slots of Lemma 4.10: the slot index `i.succ`
(`i : Fin (2 ^ s - 1)`) runs through the patterns of positive binary value, i.e. the nonzero
patterns under `slotIdx s = slotEnum s ∘ Fin.cast`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.ExpA

noncomputable section

/-- The slot index `i.succ` (`i : Fin (2 ^ s - 1)`) always carries a **nonzero** sign pattern. -/
lemma slotIdx_succ_ne_zero (s : ℕ) (i : Fin (2 ^ s - 1)) :
    slotIdx s i.succ ≠ (0 : Fin s → Bool) := by
  intro h
  have h' : slotIdx s i.succ = slotIdx s (0 : Fin (2 ^ s - 1 + 1)) := by rw [h, slotIdx_zero]
  exact Fin.succ_ne_zero i (slotIdx_injective s h')

/-- The slots `i.succ`, `i : Fin (2 ^ s - 1)`, enumerate exactly the nonzero sign patterns. -/
lemma image_slotIdx_succ_eq (s : ℕ) :
    (Finset.univ : Finset (Fin (2 ^ s - 1))).image (fun i => slotIdx s i.succ)
      = Finset.univ.erase (0 : Fin s → Bool) := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro ω hω
    rw [Finset.mem_image] at hω
    obtain ⟨i, -, rfl⟩ := hω
    exact Finset.mem_erase.mpr ⟨slotIdx_succ_ne_zero s i, Finset.mem_univ _⟩
  · rw [Finset.card_image_of_injective _
          (fun i j h => Fin.succ_injective _ (slotIdx_injective s h)),
        Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin s → Bool))]
    simp only [Finset.card_univ, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool]
    omega

/-- The product over the nonzero sign patterns reindexed by the slots `i.succ`. -/
theorem slotProdReindex (s : ℕ) (G : (Fin s → Bool) → ℂ) :
    (∏ ω ∈ (Finset.univ.erase (0 : Fin s → Bool)), G ω)
      = ∏ i : Fin (2 ^ s - 1), G (Work.Peluse.ExpA.slotIdx s i.succ) := by
  rw [← image_slotIdx_succ_eq s, Finset.prod_image]
  intro x _ y _ h
  exact Fin.succ_injective (2 ^ s - 1) (slotIdx_injective s h)

end

end Work.Peluse.ExpA
