import Mathlib
import Submission.Grassmann.Duality
import Submission.Commons.Data.Finset.map_toEmbedding_compl
import Submission.Commons.Combinatorics.SimpleGraph.card_interedges_map_iso

/-!
# Transferring the Grassmann expansion statement across the duality

`Submission/Grassmann/Duality.lean` constructs the graph isomorphism
`orthoIso : Gr k ℓ ≃g Gr k (k-ℓ)`.  Here we record how the *data* of the main theorem
(`SubGr`, `Φ`, the density and the defect `dim A + codim B`) behave under it.  The point is
that the Grassmann Expansion Hypothesis is **self-dual**:

* `SubGr k ℓ A B` is carried to `SubGr k (k-ℓ) (ortho B) (ortho A)`, with **the same
  cardinality** (`card_SubGr_ortho`);
* the **defect is preserved**: `dim (ortho B) + codim (ortho A) = dim A + codim B`
  (`defect_ortho`);
* the expansion `Φ` is preserved (`Phi_ortho`).

Consequently, in the endgame it suffices to prove `theorem_1_12` for `2ℓ ≤ k`.

NOTE: no `attribute [local instance] Classical.propDecidable` in this file --- the
statements below must be elaborated with the *same* typeclass resolution as `ChallengeDeps`
so that the terms are syntactically comparable with the body of `Φ`.
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

noncomputable section

variable {k ℓ : ℕ}

/-! ## 1. Sub-Grassmannians under orthocomplementation -/

/-- Orthocomplementation carries the sub-Grassmannian `Gr[A,B]` to `Gr[B^⊥, A^⊥]`. -/
lemma mem_SubGr_ortho (hℓ : ℓ ≤ k) (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) (L : GrVertex k ℓ) :
    orthoEquiv k ℓ hℓ L ∈ SubGr k (k - ℓ) (ortho B) (ortho A) ↔ L ∈ SubGr k ℓ A B := by
  rw [mem_SubGr, mem_SubGr, orthoEquiv_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(le_ortho_iff (k := k) (L := A) (L' := L.1)).mp h2,
      (le_ortho_iff (k := k) (L := L.1) (L' := B)).mp h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(le_ortho_iff (k := k) (L := L.1) (L' := B)).mpr h2,
      (le_ortho_iff (k := k) (L := A) (L' := L.1)).mpr h1⟩

/-- The image of a sub-Grassmannian under orthocomplementation. -/
lemma SubGr_map_ortho (hℓ : ℓ ≤ k) (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    (SubGr k ℓ A B).map (orthoEquiv k ℓ hℓ).toEmbedding
      = SubGr k (k - ℓ) (ortho B) (ortho A) := by
  ext x
  rw [Finset.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_SubGr_ortho hℓ A B y).mpr hy
  · intro hx
    refine ⟨(orthoEquiv k ℓ hℓ).symm x, ?_, by simp⟩
    exact (mem_SubGr_ortho hℓ A B _).mp (by simpa using hx)

lemma card_SubGr_ortho (hℓ : ℓ ≤ k) (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    #(SubGr k (k - ℓ) (ortho B) (ortho A)) = #(SubGr k ℓ A B) := by
  rw [← SubGr_map_ortho hℓ A B, Finset.card_map]

/-- **The defect is preserved by orthocomplementation.** -/
lemma defect_ortho (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    Module.finrank 𝔽₂ (ortho B) + (k - Module.finrank 𝔽₂ (ortho A))
      = Module.finrank 𝔽₂ A + (k - Module.finrank 𝔽₂ B) := by
  rw [finrank_ortho, finrank_ortho]
  have h1 : Module.finrank 𝔽₂ A ≤ k := by
    have := Submodule.finrank_le A; rwa [finrank_fin_fun] at this
  have h2 : Module.finrank 𝔽₂ B ≤ k := by
    have := Submodule.finrank_le B; rwa [finrank_fin_fun] at this
  omega

/-! ## 2. Sets and densities under orthocomplementation -/

/-- The image of the intersection of `S` with a sub-Grassmannian is the intersection of the
image with the image. -/
lemma card_inter_SubGr_map (hℓ : ℓ ≤ k) (S : Finset (GrVertex k ℓ))
    (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    #(S.map (orthoEquiv k ℓ hℓ).toEmbedding ∩ SubGr k (k - ℓ) (ortho B) (ortho A))
      = #(S ∩ SubGr k ℓ A B) := by
  rw [← SubGr_map_ortho hℓ A B, ← Finset.map_inter, Finset.card_map]

/-- Densities are preserved by the duality. -/
lemma density_ortho (hℓ : ℓ ≤ k) (S : Finset (GrVertex k ℓ))
    (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    (#(S.map (orthoEquiv k ℓ hℓ).toEmbedding
        ∩ SubGr k (k - ℓ) (ortho B) (ortho A)) : ℝ)
        / #(SubGr k (k - ℓ) (ortho B) (ortho A))
      = (#(S ∩ SubGr k ℓ A B) : ℝ) / #(SubGr k ℓ A B) := by
  rw [card_inter_SubGr_map hℓ S A B, card_SubGr_ortho hℓ A B]

/-- The two vertex sets have the same cardinality. -/
lemma card_GrVertex_ortho (hℓ : ℓ ≤ k) :
    Fintype.card (GrVertex k (k - ℓ)) = Fintype.card (GrVertex k ℓ) :=
  (Fintype.card_congr (orthoEquiv k ℓ hℓ)).symm

/-! ## 3. The expansion `Φ` under the duality -/

/-- The common degree of `Gr k ℓ` is invariant under `ℓ ↦ k - ℓ`. -/
lemma degree_ortho (hℓ : ℓ ≤ k) :
    (2 ^ (k - ℓ) - 1) * (2 ^ (ℓ + 1) - 2) = (2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2) := by
  have e1 : 1 ≤ 2 ^ (k - ℓ) := Nat.one_le_two_pow
  have e2 : 2 ≤ 2 ^ (ℓ + 1) := by
    have h : 2 ^ 1 ≤ 2 ^ (ℓ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using h
  have e3 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have e4 : 2 ≤ 2 ^ (k - ℓ + 1) := by
    have h : 2 ^ 1 ≤ 2 ^ (k - ℓ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using h
  have key : (((2 ^ (k - ℓ) - 1) * (2 ^ (ℓ + 1) - 2) : ℕ) : ℤ)
      = (((2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub e1, Nat.cast_sub e2, Nat.cast_sub e3, Nat.cast_sub e4]
    have hp : (2 : ℤ) ^ (k - ℓ) * 2 ^ ℓ = 2 ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hℓ]
    have p1 : (2 : ℤ) ^ (ℓ + 1) = 2 ^ ℓ * 2 := by rw [pow_succ]
    have p2 : (2 : ℤ) ^ (k - ℓ + 1) = 2 ^ (k - ℓ) * 2 := by rw [pow_succ]
    rw [p1, p2]
    nlinarith [hp]
  exact_mod_cast key

/-- The common degree in `ℚ`. -/
lemma degree_ortho' (hℓ : ℓ ≤ k) :
    (((2 ^ (k - ℓ) - 1) * (2 ^ (ℓ + 1) - 2) : ℕ) : ℚ)
      = (((2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2) : ℕ) : ℚ) := by
  rw [degree_ortho hℓ]

/-- **A graph isomorphism preserves `Φ`** whenever the two graphs are regular with the same
degree: the interedges correspond and the densities are equal. -/
theorem Phi_iso_aux {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {G' : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (e : G ≃g G') (d : ℕ) (hd : ∀ v, G.degree v = d) (hd' : ∀ w, G'.degree w = d)
    (S : Finset V) (hS : S.Nonempty) :
    Φ G' (S.map e.toEquiv.toEmbedding) (Finset.map_nonempty.mpr hS) = Φ G S hS := by
  have hcount : #(G'.interedges (S.map e.toEquiv.toEmbedding)
      ((S.map e.toEquiv.toEmbedding)ᶜ)) = #(G.interedges S Sᶜ) := by
    rw [Commons.Data.Finset.map_toEmbedding_compl]
    exact Commons.Combinatorics.SimpleGraph.card_interedges_map_iso e S
  rw [Φ, Φ, hcount, Finset.card_map, hd' (Finset.map_nonempty.mpr hS).choose, hd hS.choose]

/-- **`Φ` is preserved by the duality `Gr k ℓ ≃ Gr k (k-ℓ)`.** -/
theorem Phi_ortho (hℓ : 1 ≤ ℓ) (hk : ℓ ≤ k) (hk' : 1 ≤ k - ℓ) (S : Finset (GrVertex k ℓ))
    (hS : S.Nonempty) :
    Φ (Gr k (k - ℓ)) (S.map (orthoEquiv k ℓ hk).toEmbedding)
        (Finset.map_nonempty.mpr hS)
      = Φ (Gr k ℓ) S hS :=
  Phi_iso_aux (G := Gr k ℓ) (G' := Gr k (k - ℓ)) (orthoIso k ℓ hk hℓ)
    ((2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2))
    (fun v => Gr_degree_eq_value (k := k) (ℓ := ℓ) hℓ v)
    (fun w => by
      rw [Gr_degree_eq_value (k := k) (ℓ := k - ℓ) hk' w, show k - (k - ℓ) = ℓ by omega]
      exact degree_ortho hk)
    S hS

/-! ## 4. The statement-level transfer -/

/-- The inner (density/expansion) statement of `theorem_1_12` for a fixed pair `(k,ℓ)`. -/
def ExpStmt (α ε : ℝ) (r : ℕ) (k ℓ : ℕ) : Prop :=
  ∀ S : Finset (GrVertex k ℓ), (hS : S.Nonempty) →
    2 * #S ≤ Fintype.card (GrVertex k ℓ) → Φ (Gr k ℓ) S hS ≤ α →
      ∃ (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)), A ≤ B ∧
        Module.finrank 𝔽₂ A + (k - Module.finrank 𝔽₂ B) ≤ r ∧
        (#(S ∩ SubGr k ℓ A B) : ℝ) / (#(SubGr k ℓ A B) : ℝ) ≥ ε

/-- **The duality transfer.**  If the expansion statement holds for the complementary pair
`(k, k-ℓ)` then it holds for `(k, ℓ)`. -/
theorem ExpStmt_dual (hℓ : 1 ≤ ℓ) (hk : ℓ ≤ k) (hk' : 1 ≤ k - ℓ) {α ε : ℝ} {r : ℕ}
    (h : ExpStmt α ε r k (k - ℓ)) : ExpStmt α ε r k ℓ := by
  intro S hS hcard hΦ
  have hS' : (S.map (orthoEquiv k ℓ hk).toEmbedding).Nonempty := Finset.map_nonempty.mpr hS
  have hcard' : 2 * #(S.map (orthoEquiv k ℓ hk).toEmbedding)
      ≤ Fintype.card (GrVertex k (k - ℓ)) := by
    rw [Finset.card_map, card_GrVertex_ortho hk]
    exact hcard
  have hΦ' : Φ (Gr k (k - ℓ)) (S.map (orthoEquiv k ℓ hk).toEmbedding) hS' ≤ α := by
    rw [Phi_ortho hℓ hk hk' S hS]
    exact hΦ
  obtain ⟨A', B', hAB', hdef', hdens'⟩ := h _ hS' hcard' hΦ'
  refine ⟨ortho B', ortho A', ?_, ?_, ?_⟩
  · rw [le_ortho_iff]
    exact hAB'
  · rw [defect_ortho]
    exact hdef'
  · have hd := density_ortho hk S (ortho B') (ortho A')
    rw [ortho_ortho (k := k) B', ortho_ortho (k := k) A'] at hd
    rw [← hd]
    exact hdens'

end

end F2
end Submission.Grassmann
