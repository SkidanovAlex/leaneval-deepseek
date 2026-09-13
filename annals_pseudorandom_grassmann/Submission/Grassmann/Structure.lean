import ChallengeDeps
import Mathlib

/-!
# Basic structure of the Grassmann objects in Theorem 1.12

Foundational, fully-verified facts about the exact objects appearing in the
statement of Khot--Minzer--Safra, *Pseudorandom sets in Grassmann graph have
near-perfect expansion* (Ann. of Math. 198 (2023), Theorem 1.12 as formalised
here): the vertex type `GrVertex k ℓ` of `ℓ`-dimensional subspaces of `𝔽₂ᵏ`
(`𝔽₂ = ZMod 2`), the reference sets `SubGr k ℓ A B = {L : GrVertex k ℓ | A ≤ L ≤ B}`
and the expansion functional `Φ`.

This file establishes the elementary *denotational layer*: which vertex types
are inhabited, when reference sets are nonempty, and elementary
membership / monotonicity facts, so that all later analytic work can be
phrased against verified definitions.
-/

open PseudorandomGrassmann
open Module Finset Filter
set_option linter.style.haveILetI false

set_option autoImplicit false

local notation "𝔽₂" => ZMod 2

namespace Submission.Grassmann

variable {k ℓ : ℕ}

/-- Every vertex is an `ℓ`-dimensional subspace of `𝔽₂ᵏ`; in particular its
dimension is at most `k`. -/
lemma finrank_vertex_le (k ℓ : ℕ) (L : GrVertex k ℓ) : finrank 𝔽₂ L.1 ≤ k := by
  have h := Submodule.finrank_le L.1
  rwa [Module.finrank_pi, Fintype.card_fin] at h

/-- For `ℓ > k` the vertex type is empty: there is no `ℓ`-dimensional subspace
of the `k`-dimensional space `𝔽₂ᵏ`. -/
lemma isEmpty_GrVertex_of_lt (h : k < ℓ) : IsEmpty (GrVertex k ℓ) := by
  rw [isEmpty_subtype]
  intro L hL
  have hle : finrank 𝔽₂ L ≤ k := by
    have hh := Submodule.finrank_le L
    rwa [Module.finrank_pi, Fintype.card_fin] at hh
  exact (not_le_of_gt h) (by simpa [hL] using hle)

/-- The vertex count of `Gr_{k,ℓ}` is zero once `ℓ > k`. -/
lemma card_GrVertex_eq_zero_of_lt {k ℓ : ℕ} (h : k < ℓ) : Fintype.card (GrVertex k ℓ) = 0 := by
  haveI : IsEmpty (GrVertex k ℓ) := isEmpty_GrVertex_of_lt h
  exact Fintype.card_eq_zero (α := GrVertex k ℓ)

/-- The zero subspace has dimension `0` (over `𝔽₂`, in ambient dimension `k`). -/
lemma finrank_bot_eq_zero (k : ℕ) : finrank 𝔽₂ (⊥ : Submodule 𝔽₂ (Fin k → 𝔽₂)) = 0 := by
  simp [finrank_bot]

/-- The ambient space `𝔽₂ᵏ` has dimension `k` (over `𝔽₂`). -/
lemma finrank_top_eq_k (k : ℕ) : finrank 𝔽₂ (⊤ : Submodule 𝔽₂ (Fin k → 𝔽₂)) = k := by
  rw [finrank_top, Module.finrank_pi]
  simp

/-- Membership in `SubGr k ℓ A B` is exactly the sandwich condition `A ≤ L ≤ B`. -/
lemma mem_SubGr (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) (L : GrVertex k ℓ) :
    L ∈ SubGr k ℓ A B ↔ A ≤ (L : Submodule 𝔽₂ (Fin k → 𝔽₂)) ∧
      (L : Submodule 𝔽₂ (Fin k → 𝔽₂)) ≤ B := by
  simp [SubGr]

/-- `SubGr k ℓ ⊥ ⊤` collects every vertex. -/
lemma SubGr_bot_top (k ℓ : ℕ) : SubGr k ℓ ⊥ ⊤ = Finset.univ := by
  ext L
  simp [SubGr]

/-- Reference sets are monotone: enlarging the floor `A` (raising it) and
shrinking the ceiling `B` (lowering it) shrinks the sandwich. -/
lemma SubGr_mono {A A' B B' : Submodule 𝔽₂ (Fin k → 𝔽₂)} (hA : A' ≤ A) (hB : B ≤ B') :
    SubGr k ℓ A B ⊆ SubGr k ℓ A' B' := by
  intro L hL
  rw [mem_SubGr] at hL ⊢
  exact ⟨le_trans hA hL.1, le_trans hL.2 hB⟩

/-- If `A` is not below `B` then no vertex lies between them. -/
lemma SubGr_empty_of_not_le {A B : Submodule 𝔽₂ (Fin k → 𝔽₂)} (h : ¬ A ≤ B) :
    SubGr k ℓ A B = ∅ := by
  ext L
  constructor
  · intro hmem
    rw [mem_SubGr] at hmem
    exact False.elim (h (le_trans hmem.1 hmem.2))
  · intro hmem
    simp at hmem

/-- When `A ≤ B`, every vertex of `SubGr` is a subspace of `B` containing `A`,
so the dimensions are sandwiched between `finrank A` and `finrank B`. -/
lemma finrank_le_of_mem_SubGr {A B : Submodule 𝔽₂ (Fin k → 𝔽₂)} {L : GrVertex k ℓ}
    (h : L ∈ SubGr k ℓ A B) :
    finrank 𝔽₂ A ≤ ℓ ∧ ℓ ≤ finrank 𝔽₂ B := by
  rw [mem_SubGr] at h
  have hA := Submodule.finrank_mono (s := A) (t := (L : Submodule 𝔽₂ (Fin k → 𝔽₂))) h.1
  have hB := Submodule.finrank_mono (s := (L : Submodule 𝔽₂ (Fin k → 𝔽₂))) (t := B) h.2
  simpa [L.2] using And.intro hA hB

/-- The intersection of a set with a reference set is no larger than the
reference set itself. -/
lemma card_inter_le_card_SubGr (S : Finset (GrVertex k ℓ)) (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    #(S ∩ SubGr k ℓ A B) ≤ #(SubGr k ℓ A B) := by
  exact Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := SubGr k ℓ A B))

end Submission.Grassmann
