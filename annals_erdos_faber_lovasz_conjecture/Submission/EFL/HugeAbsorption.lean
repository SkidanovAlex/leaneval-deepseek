import Submission.EFL.Absorption
import Submission.EFL.InternalStepB

/-!
# §7.3: difficult matchings and the huge-edge absorption setup

This module begins §7.3 of the paper.  It contains

* `IsDifficult` — Definition `defn:difficult`: a matching `M` is *difficult* if
  `|V(𝓗) ∖ U| ≥ 2` and `M` covers at least `3/4` of `V(𝓗) ∖ U`;
* the two consequences of *not* being difficult that the crossing part of
  Lemma 7.3 (`huge-edge-absorption-lemma`) uses:
  `card_inter_compl_le_of_not_difficult` (`|V(M) ∩ (V∖U)| ≤ 3n/4`) and
  `card_matchVert_le_of_not_difficult`
  (`|V(M)| ≤ (3/4 + ε)n` when `M` is in addition typical-absorbable, as
  `AB-huge` gives `|V(M) ∩ U| ≤ εn`).
-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- **Definition `defn:difficult`.**  A matching `M` is difficult if `V(𝓗) ∖ U`
has at least two vertices and `M` covers at least `3/4` of them. -/
def IsDifficult {𝓗 : Hypergraph (Fin n)} (U : Set (Fin n)) (M : Set 𝓗) : Prop :=
  2 ≤ (Uᶜ).ncard ∧ 3 * (Uᶜ).ncard ≤ 4 * (matchVert M ∩ Uᶜ).ncard

/-- A matching that is not difficult covers at most `3n/4` vertices outside
`U`. -/
theorem card_inter_compl_le_of_not_difficult {𝓗 : Hypergraph (Fin n)} {U : Set (Fin n)}
    {M : Set 𝓗} (h : ¬ IsDifficult U M) (hn : 4 ≤ n) :
    ((matchVert M ∩ Uᶜ).ncard : ℝ) ≤ 3 * (n : ℝ) / 4 := by
  classical
  rw [IsDifficult, not_and_or] at h
  rcases h with h | h
  · have hc : (Uᶜ).ncard ≤ 1 := by
      have h2 := not_le.mp h
      omega
    have hle : (matchVert M ∩ Uᶜ).ncard ≤ 1 :=
      le_trans (Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)) hc
    have h1 : ((matchVert M ∩ Uᶜ).ncard : ℝ) ≤ 1 := by exact_mod_cast hle
    have h2 : (1 : ℝ) ≤ 3 * (n : ℝ) / 4 := by
      have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    linarith
  · have hc : 4 * (matchVert M ∩ Uᶜ).ncard < 3 * (Uᶜ).ncard := not_le.mp h
    have h2 : ((matchVert M ∩ Uᶜ).ncard : ℝ) < 3 * ((Uᶜ).ncard : ℝ) / 4 := by
      have h3 : (4 : ℝ) * ((matchVert M ∩ Uᶜ).ncard : ℝ) < 3 * ((Uᶜ).ncard : ℝ) := by
        exact_mod_cast hc
      linarith
    have h3 : ((Uᶜ).ncard : ℝ) ≤ (n : ℝ) := by
      have h4 := Set.ncard_le_ncard (Set.subset_univ Uᶜ) (Set.toFinite _)
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h4
      exact_mod_cast h4
    linarith

/-- **`v(N_ℓ) ≤ (3/4 + ε)n`** (used in the crossing part of Lemma 7.3): a
matching that is absorbable by typicality and is not difficult has at most
`(3/4 + ε)n` vertices. -/
theorem card_matchVert_le_of_not_difficult {𝓗 R : Hypergraph (Fin n)}
    {U S : Set (Fin n)} {M : Set 𝓗} {ρ ε γ κ ξ : ℝ}
    (h : AbsorbableByTypical 𝓗 M R U S ρ ε γ κ ξ) (hnd : ¬ IsDifficult U M)
    (hn : 4 ≤ n) :
    ((matchVert M).ncard : ℝ) ≤ (3 / 4 + ε) * (n : ℝ) := by
  classical
  obtain ⟨𝓥, -, -, -, -, -, -, hcard⟩ := h
  have hsplit : matchVert M ⊆ (matchVert M ∩ U) ∪ (matchVert M ∩ Uᶜ) := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl ⟨hx, hxU⟩
    · exact Or.inr ⟨hx, hxU⟩
  have h1 : ((matchVert M).ncard : ℝ)
      ≤ ((matchVert M ∩ U).ncard : ℝ) + ((matchVert M ∩ Uᶜ).ncard : ℝ) := by
    have h2 := Set.ncard_le_ncard hsplit (Set.toFinite _)
    have h3 := Set.ncard_union_le (matchVert M ∩ U) (matchVert M ∩ Uᶜ)
    have h4 : ((matchVert M).ncard : ℝ)
        ≤ (((matchVert M ∩ U) ∪ (matchVert M ∩ Uᶜ)) : Set (Fin n)).ncard := by
      exact_mod_cast h2
    have h5 : (((matchVert M ∩ U) ∪ (matchVert M ∩ Uᶜ)) : Set (Fin n)).ncard
        ≤ (matchVert M ∩ U).ncard + (matchVert M ∩ Uᶜ).ncard := h3
    have h6 : ((((matchVert M ∩ U) ∪ (matchVert M ∩ Uᶜ)) : Set (Fin n)).ncard : ℝ)
        ≤ (((matchVert M ∩ U).ncard : ℝ) + ((matchVert M ∩ Uᶜ).ncard : ℝ)) := by
      exact_mod_cast h5
    linarith
  have h2 := card_inter_compl_le_of_not_difficult hnd hn
  have h3 : ((matchVert M).ncard : ℝ) ≤ ε * (n : ℝ) + 3 * (n : ℝ) / 4 := by
    linarith
  have h4 : ε * (n : ℝ) + 3 * (n : ℝ) / 4 = (3 / 4 + ε) * (n : ℝ) := by ring
  linarith

end

end ErdosFaberLovaszConjecture
