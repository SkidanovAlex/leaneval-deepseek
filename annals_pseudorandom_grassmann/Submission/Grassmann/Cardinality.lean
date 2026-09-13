import Submission.Grassmann.Structure
import Submission.Commons.LinearAlgebra.Submodule.exists_submodule_span_finrank
import Submission.Commons.LinearAlgebra.Submodule.exists_submodule_between_finrank

/-!
# Cardinality facts for the Grassmann vertex sets

`GrVertex k ℓ` (the type of `ℓ`-dimensional subspaces of `𝔽₂ᵏ`) is a finite type
whose cardinality is positive precisely when `ℓ ≤ k`.  Combined with
`card_GrVertex_eq_zero_of_lt` (in `Submission.Grassmann.Structure`) this gives
a clean if-and-only-if.

Also here: when is the reference set `SubGr k ℓ A B` nonempty?  Answer (for
`A ≤ B`): exactly when `finrank A ≤ ℓ ≤ finrank B`, i.e. the sandwich
dimension interval contains `ℓ`.  This is the point where the theorem's
conclusion can possibly be non-vacuous.
-/

open PseudorandomGrassmann
open Module Finset Filter

set_option autoImplicit false

local notation "𝔽₂" => ZMod 2

namespace Submission.Grassmann

variable {k ℓ : ℕ}

/-- If `ℓ ≤ k`, there exists an `ℓ`-dimensional subspace of `𝔽₂ᵏ`, i.e.
`GrVertex k ℓ` is inhabited. -/
lemma nonempty_GrVertex_of_le (h : ℓ ≤ k) : Nonempty (GrVertex k ℓ) := by
  classical
  have hfin : ℓ ≤ Module.finrank 𝔽₂ (Fin k → 𝔽₂) := by
    rwa [Module.finrank_pi, Fintype.card_fin]
  rcases Commons.LinearAlgebra.Submodule.exists_submodule_span_finrank (K := 𝔽₂)
      (V := Fin k → 𝔽₂) hfin with ⟨W, hW⟩
  exact ⟨⟨W, hW⟩⟩

/-- Vertex count is non-zero exactly when `ℓ ≤ k`. -/
lemma card_GrVertex_ne_zero_iff_le : Fintype.card (GrVertex k ℓ) ≠ 0 ↔ ℓ ≤ k := by
  constructor
  · intro hne
    by_contra hlt
    exact hne (card_GrVertex_eq_zero_of_lt (Nat.lt_of_not_ge hlt))
  · intro hle
    haveI : Nonempty (GrVertex k ℓ) := nonempty_GrVertex_of_le hle
    exact Fintype.card_ne_zero (α := GrVertex k ℓ)

/-- Vertex count is positive exactly when `ℓ ≤ k`. -/
lemma card_GrVertex_pos_iff_le : 0 < Fintype.card (GrVertex k ℓ) ↔ ℓ ≤ k := by
  rw [← card_GrVertex_ne_zero_iff_le]
  exact Nat.pos_iff_ne_zero

/-- `GrVertex k ℓ` is a nonempty finite type exactly when `ℓ ≤ k`. -/
lemma nonempty_GrVertex_iff_le : Nonempty (GrVertex k ℓ) ↔ ℓ ≤ k := by
  constructor
  · intro h
    by_contra hlt
    have hlt' : k < ℓ := Nat.lt_of_not_ge hlt
    haveI : IsEmpty (GrVertex k ℓ) := isEmpty_GrVertex_of_lt hlt'
    rcases h with ⟨v⟩
    exact (inferInstance : IsEmpty (GrVertex k ℓ)).false v
  · exact nonempty_GrVertex_of_le

/-- The reference set `SubGr k ℓ A B` is nonempty exactly when `A ≤ B` and the
dimension interval `[finrank A, finrank B]` contains `ℓ`. -/
lemma SubGr_nonempty_iff (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    (SubGr k ℓ A B).Nonempty ↔ A ≤ B ∧ finrank 𝔽₂ A ≤ ℓ ∧ ℓ ≤ finrank 𝔽₂ B := by
  classical
  constructor
  · intro h
    rcases h with ⟨L, hL⟩
    have hdim := finrank_le_of_mem_SubGr (A := A) (B := B) (L := L) hL
    rw [mem_SubGr] at hL
    exact ⟨le_trans hL.1 hL.2, hdim⟩
  · intro h
    rcases h with ⟨hAB, hA, hB⟩
    rcases Commons.LinearAlgebra.Submodule.exists_submodule_between_finrank (K := 𝔽₂)
        (V := Fin k → 𝔽₂) A B hAB hA hB with ⟨W, hWA, hWB, hWdim⟩
    refine ⟨⟨W, hWdim⟩, ?_⟩
    rw [mem_SubGr]
    exact ⟨hWA, hWB⟩


open Classical in
open Classical in
/-- A positive density conclusion `ε ≤ #(S ∩ SubGr) / #(SubGr)` (as real
division, `ε > 0`) forces the reference set to be nonempty. -/
lemma SubGr_nonempty_of_density_pos (S : Finset (GrVertex k ℓ))
    (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) {ε : ℝ} (hε : 0 < ε)
    (hd : (ε : ℝ) ≤ ((#(S ∩ SubGr k ℓ A B) : ℝ) / (#(SubGr k ℓ A B) : ℝ))) :
    (SubGr k ℓ A B).Nonempty := by
  by_contra hne
  have hcard0 : #(SubGr k ℓ A B) = 0 := by
    by_contra hc
    have hpos : 0 < #(SubGr k ℓ A B) := Nat.pos_of_ne_zero hc
    exact hne (Finset.card_pos.mp hpos)
  rw [hcard0] at hd
  have : (ε : ℝ) ≤ 0 := by
    simpa using hd
  linarith

end Submission.Grassmann
