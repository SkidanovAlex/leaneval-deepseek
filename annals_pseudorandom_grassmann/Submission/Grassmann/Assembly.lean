import Mathlib
import Submission.Grassmann.Transfer

/-!
# Reducing `theorem_1_12` to the case `2ℓ ≤ k`

The target statement of the challenge is, for `α ∈ (0,1)`,

`∃ ε > 0, ∃ r, ∀ᶠ (ℓ) (k) in atTop, ∀ S ⊆ Gr k ℓ, S ≠ ∅ → 2#S ≤ N → Φ(S) ≤ α →
    ∃ A ≤ B, dim A + codim B ≤ r ∧ density(S ∩ Gr[A,B]) ≥ ε`.

Since `∀ᶠ (ℓ) (k) in atTop` is the *nested* filter `∀ᶠ ℓ, ∀ᶠ k`, and for fixed `ℓ` the
condition `2ℓ ≤ k` holds for all sufficiently large `k`, this is *equivalent* to the version
with the extra hypothesis `2ℓ ≤ k`.  That is the form in which the Grassmann expansion
theorem (`ExpStmt`) is naturally proved, and the complement `ℓ > k/2` follows from it by the
duality `Gr k ℓ ≃ Gr k (k-ℓ)` (`ExpStmt_dual`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open PseudorandomGrassmann
open Module Finset Filter
open Classical

local notation "𝔽₂" => ZMod 2

namespace Submission.Grassmann
namespace F2

/-- **The reduction.**  The challenge statement follows from its `2ℓ ≤ k` instance. -/
theorem theorem_1_12_of_main (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (main : ∃ ε > 0, ∃ r, ∀ᶠ (ℓ : ℕ) (k : ℕ) in atTop, 2 * ℓ ≤ k → ExpStmt α ε r k ℓ) :
    ∃ ε > 0, ∃ r, ∀ᶠ (ℓ : ℕ) (k : ℕ) in atTop, ∀ S : Finset (GrVertex k ℓ),
      (hS : S.Nonempty) → 2 * #S ≤ Fintype.card (GrVertex k ℓ) →
        Φ (Gr k ℓ) S hS ≤ α → ∃ (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)), A ≤ B ∧
          letI a := finrank 𝔽₂ A; letI b := k - finrank 𝔽₂ B
          a + b ≤ r ∧ #(S ∩ SubGr k ℓ A B) / #(SubGr k ℓ A B) ≥ (ε : ℝ) := by
  obtain ⟨ε, hε, r, hmain⟩ := main
  refine ⟨ε, hε, r, ?_⟩
  refine hmain.mono (fun ℓ hℓ => ?_)
  refine (hℓ.and (eventually_atTop.mpr ⟨2 * ℓ, fun k hk => hk⟩)).mono ?_
  rintro k ⟨hk, h2ℓ⟩
  exact hk h2ℓ

/-- Conversely, the `2ℓ ≤ k` instance is a consequence of the challenge statement
(this is the trivial direction: restrict the `∀ᶠ ℓ` / `∀ᶠ k` to a cofinal set). -/
theorem main_of_theorem_1_12 (α : ℝ)
    (h : ∃ ε > 0, ∃ r, ∀ᶠ (ℓ : ℕ) (k : ℕ) in atTop, ∀ S : Finset (GrVertex k ℓ),
      (hS : S.Nonempty) → 2 * #S ≤ Fintype.card (GrVertex k ℓ) →
        Φ (Gr k ℓ) S hS ≤ α → ∃ (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)), A ≤ B ∧
          letI a := finrank 𝔽₂ A; letI b := k - finrank 𝔽₂ B
          a + b ≤ r ∧ #(S ∩ SubGr k ℓ A B) / #(SubGr k ℓ A B) ≥ (ε : ℝ)) :
    ∃ ε > 0, ∃ r, ∀ᶠ (ℓ : ℕ) (k : ℕ) in atTop, 2 * ℓ ≤ k → ExpStmt α ε r k ℓ := by
  obtain ⟨ε, hε, r, hmain⟩ := h
  exact ⟨ε, hε, r, hmain.mono (fun ℓ hℓ => hℓ.mono (fun k hk _ => hk))⟩

end F2
end Submission.Grassmann
