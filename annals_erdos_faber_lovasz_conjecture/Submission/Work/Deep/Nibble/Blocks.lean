import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise
import Mathlib.Order.Partition.Equipartition

/-!
# Splitting the colour set `Fin D` into `K` near-equal blocks

The §7 chunking of `lem:nibble2` splits the `D` colour classes into `K` blocks
of sizes `⌊D/K⌋` or `⌈D/K⌉` and serves one block per part of the partition of
`𝓗'`.  This module provides that decomposition, using Mathlib's equipartition
machinery (`Finpartition.exists_equipartition_card_eq`,
`Finpartition.IsEquipartition`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

/-- **Splitting `Fin D` into `K` blocks of sizes `⌊D/K⌋` or `⌊D/K⌋+1`.**

For `0 < K ≤ D` there are `I : Fin K → Finset (Fin D)` that are pairwise
disjoint, cover `Fin D`, have `⌊D/K⌋ ≤ #(I i) ≤ ⌊D/K⌋+1`, and whose sizes sum
to `D`. -/
theorem exists_colourBlocks (D K : ℕ) (hK : 0 < K) (hKD : K ≤ D) :
    ∃ I : Fin K → Finset (Fin D),
      (∀ i, D / K ≤ (I i).card ∧ (I i).card ≤ D / K + 1) ∧
      (∀ i j, i ≠ j → Disjoint (I i) (I j)) ∧
      (Finset.univ.biUnion I = Finset.univ) ∧
      (∑ i : Fin K, (I i).card) = D := by
  classical
  obtain ⟨P, hPequi, hPcard⟩ :=
    Finpartition.exists_equipartition_card_eq (s := (Finset.univ : Finset (Fin D)))
      (n := K) (Nat.pos_iff_ne_zero.mp hK) (by simpa using hKD)
  let e : P.parts ≃ Fin K := (Finset.equivFin P.parts).trans (finCongr hPcard)
  let I : Fin K → Finset (Fin D) := fun i => (e.symm i).1
  have hmem : ∀ i, I i ∈ P.parts := fun i => (e.symm i).2
  have hsizes : ∀ i, D / K ≤ (I i).card ∧ (I i).card ≤ D / K + 1 := by
    intro i
    have h1 := hPequi.average_le_card_part (hmem i)
    have h2 := hPequi.card_part_le_average_add_one (hmem i)
    have hs : (Finset.univ : Finset (Fin D)).card = D := by simp
    rw [hs, hPcard] at h1 h2
    exact ⟨h1, h2⟩
  have hdisj : ∀ i j, i ≠ j → Disjoint (I i) (I j) := by
    intro i j hij
    exact P.disjoint (hmem i) (hmem j)
      (fun hcon => hij (e.symm.injective (Subtype.ext hcon)))
  have hcover : Finset.univ.biUnion I = Finset.univ := by
    ext c
    simp only [Finset.mem_univ, iff_true]
    have hc : c ∈ P.parts.sup id := by rw [P.sup_parts]; exact Finset.mem_univ c
    rw [Finset.mem_sup] at hc
    obtain ⟨t, ht, hct⟩ := hc
    refine Finset.mem_biUnion.mpr ⟨e ⟨t, ht⟩, Finset.mem_univ _, ?_⟩
    have hfix : e.symm (e ⟨t, ht⟩) = ⟨t, ht⟩ := e.symm_apply_apply ⟨t, ht⟩
    change c ∈ (e.symm (e ⟨t, ht⟩) : ↥P.parts).1
    rw [hfix]
    exact hct
  have hsum : (∑ i : Fin K, (I i).card) = D := by
    rw [← Finset.card_biUnion
      (h := fun i _ j _ hij => hdisj i j hij), hcover]
    simp
  exact ⟨I, hsizes, hdisj, hcover, hsum⟩

end

end ErdosFaberLovaszConjecture
