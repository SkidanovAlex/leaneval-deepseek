import Submission.EFL.Reservoir
import Submission.EFL.RegReservoir

/-!
# Elementary observations of §12 (`claim:easyobs`)

This module proves the first observation `(EP1)` of the paper's Claim
`claim:easyobs`: every edge of `𝓗` that meets `U = V_+^{(1-ε)}(G)` has at most
`εn` vertices (for `2 ≤ εn`; for edges of size at least three the extra
condition is unnecessary).
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- **Claim `claim:easyobs` (EP1).**  If an edge `e ∈ 𝓗` contains a vertex `u`
of `U = V_+^{(1-ε)}(G)` then `|e| ≤ εn`.  (When `|e| ≥ 3` the argument is
linearity; when `|e| ≤ 2` one uses `2 ≤ εn`.) -/
theorem edgeSize_le_of_meets_Vplus (𝓗 : Hypergraph (Fin n)) (hlin : 𝓗.IsLinear) {ε : ℝ}
    (hεn : 2 ≤ ε * (n : ℝ)) {e : Set (Fin n)} (he : e ∈ 𝓗)
    (hmeet : ∃ u ∈ e, u ∈ Vplus 𝓗 (1 - ε)) :
    (edgeSize e : ℝ) ≤ ε * (n : ℝ) := by
  classical
  obtain ⟨u, hue, huU⟩ := hmeet
  have huU' : (1 - ε) * (n : ℝ) ≤ (degAt 𝓗.pow2 u : ℝ) := huU
  by_cases h2 : edgeSize e ≤ 2
  · have h3 : (edgeSize e : ℝ) ≤ 2 := by exact_mod_cast h2
    linarith
  · push_neg at h2
    have h3 : 3 ≤ edgeSize e := by omega
    have hsub : nbrs (𝓗.pow2) u ⊆ (Set.univ \ e : Set (Fin n)) := by
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_univ, true_and]
      intro hxe
      have hxu : ({u, x} : Set (Fin n)) ∈ 𝓗 := hx.1
      have hpair : edgeSize ({u, x} : Set (Fin n)) = 2 := hx.2
      have hxne : x ≠ u := by
        intro h
        rw [h] at hpair
        have hp : ({u, u} : Set (Fin n)) = ({u} : Set (Fin n)) := by ext y; simp
        rw [hp, edgeSize_eq_ncard, Set.ncard_singleton] at hpair
        omega
      have heq := IsLinear.eq_of_mem_pair hlin he hxu (Ne.symm hxne) hue hxe
        (by simp) (by simp)
      have : edgeSize e = 2 := by rw [heq]; exact hpair
      omega
    have h4 : degAt 𝓗.pow2 u ≤ (Set.univ \ e : Set (Fin n)).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h5 : ((Set.univ \ e : Set (Fin n)).ncard : ℝ) = (n : ℝ) - (edgeSize e : ℝ) := by
      have h6 : (Set.univ \ e : Set (Fin n)).ncard = n - e.ncard := by
        rw [Set.ncard_sdiff (Set.subset_univ e), Set.ncard_univ, Nat.card_fin]
      have h7 : e.ncard ≤ n := by
        have h8 : e.ncard ≤ (Set.univ : Set (Fin n)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ e) (Set.toFinite _)
        rwa [Set.ncard_univ, Nat.card_fin] at h8
      rw [h6, Nat.cast_sub h7, edgeSize_eq_ncard]
    have h9 : ((Set.univ \ e : Set (Fin n)).ncard : ℝ) ≤
        (n : ℝ) - (edgeSize e : ℝ) := le_of_eq h5
    have h10 : (degAt 𝓗.pow2 u : ℝ) ≤ (n : ℝ) - (edgeSize e : ℝ) := by
      have h11 : (degAt 𝓗.pow2 u : ℝ) ≤ ((Set.univ \ e : Set (Fin n)).ncard : ℝ) := by
        exact_mod_cast h4
      linarith
    linarith

end

end ErdosFaberLovaszConjecture
