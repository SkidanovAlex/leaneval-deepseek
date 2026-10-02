import Submission.EFL.DegreeLemma
import Submission.Commons.Combinatorics.Hypergraph.card_size_ge_three_mul_two_le
import Submission.Commons.Combinatorics.Hypergraph.card_size_gt_mul_le
import Submission.Commons.Combinatorics.Hypergraph.card_two_edges_eq_card_nbrs

/-!
# The Regularising Lemma (Lemma 11.3, `lem:degree-lemma`)

This module discharges the two numerical inputs of
`regularising_lemma_core` (the degree estimate for the edges of `𝓗` that are
not 2-edges, and the bound `d_𝓗(w) - d_{𝓗_small}(w) ≤ 2n/r₁`) using the
combinatorial lemmas

* `Commons.Combinatorics.Hypergraph.card_size_ge_three_mul_two_le`,
* `Commons.Combinatorics.Hypergraph.card_size_gt_mul_le`,
* `Commons.Combinatorics.Hypergraph.card_two_edges_eq_card_nbrs`,

and obtains the paper's Lemma 11.3 in full.
-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- The paper's inequality (eq. `eqn:non-graph-degree`): the number of edges
of `𝓗` of size at least three containing `w` is at most half of
`n - 1 - d_G(w)`, where `G = 𝓗^{(2)}`. -/
theorem hdeg_sdiff_pow2_le (𝓗 : Hypergraph (Fin n)) (hlin : 𝓗.IsLinear)
    (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e) (w : Fin n) :
    (MultiHypergraph.hdeg (𝓗 \ 𝓗.pow2) w : ℝ) ≤
      (((n : ℝ) - 1) - (degAt 𝓗.pow2 w : ℝ)) / 2 := by
  have hlin' : ∀ e₁ ∈ 𝓗, ∀ e₂ ∈ 𝓗, e₁ ≠ e₂ → (e₁ ∩ e₂).Subsingleton := hlin
  have hset : {e ∈ 𝓗 \ 𝓗.pow2 | w ∈ e} = {e ∈ 𝓗 | w ∈ e ∧ 3 ≤ e.ncard} := by
    ext e
    constructor
    · intro he
      have h2 : 2 ≤ e.ncard := by
        have := hbig e he.1.1
        rwa [edgeSize_eq_ncard] at this
      exact ⟨he.1.1, he.2, by
        by_contra h3
        push_neg at h3
        have h4 : e.ncard = 2 := by omega
        exact he.1.2 (mem_pow2.mpr ⟨he.1.1, by rw [edgeSize_eq_ncard, h4]⟩)⟩
    · intro he
      refine ⟨⟨he.1, ?_⟩, he.2.1⟩
      intro hp
      have h2 : e.ncard = 2 := by
        have := (mem_pow2.mp hp).2
        rwa [edgeSize_eq_ncard] at this
      have h3 : 3 ≤ e.ncard := he.2.2
      omega
  have hsetD : {e ∈ 𝓗.pow2 | w ∈ e} = {e ∈ 𝓗 | w ∈ e ∧ e.ncard = 2} := by
    ext e
    simp only [Set.mem_setOf_eq, mem_pow2, edgeSize_eq_ncard]
    tauto
  have hD : (degAt 𝓗.pow2 w : ℝ) = ({e ∈ 𝓗 | w ∈ e ∧ e.ncard = 2}.ncard : ℝ) := by
    rw [← hdeg_pow2_eq_degAt, MultiHypergraph.hdeg, hsetD]
  have hM : (MultiHypergraph.hdeg (𝓗 \ 𝓗.pow2) w : ℝ) =
      ({e ∈ 𝓗 | w ∈ e ∧ 3 ≤ e.ncard}.ncard : ℝ) := by
    rw [MultiHypergraph.hdeg, hset]
  have hbig' : ∀ e ∈ 𝓗, 2 ≤ e.ncard := fun e he => by
    have := hbig e he
    rwa [edgeSize_eq_ncard] at this
  have hmain := Commons.Combinatorics.Hypergraph.card_size_ge_three_mul_two_le 𝓗 hlin' hbig' w
  rw [hM]
  linarith [hmain, hD]

/-- The number of edges of `𝓗` of size more than `r₁` containing `w` is at
most `2n/r₁`. -/
theorem hdeg_sub_small_le (𝓗 : Hypergraph (Fin n)) (hlin : 𝓗.IsLinear) {r₁ : ℕ}
    (hr1 : 1 ≤ r₁) (w : Fin n) :
    (MultiHypergraph.hdeg 𝓗 w : ℝ) - (MultiHypergraph.hdeg (𝓗.smallEdges r₁) w : ℝ) ≤
      2 * (n : ℝ) / (r₁ : ℝ) := by
  have hlin' : ∀ e₁ ∈ 𝓗, ∀ e₂ ∈ 𝓗, e₁ ≠ e₂ → (e₁ ∩ e₂).Subsingleton := hlin
  have hsplit := hdeg_eq_small_add 𝓗 r₁ w
  have hM : (MultiHypergraph.hdeg 𝓗 w : ℝ) -
      (MultiHypergraph.hdeg (𝓗.smallEdges r₁) w : ℝ) =
      ({e ∈ 𝓗 | w ∈ e ∧ r₁ < e.ncard}.ncard : ℝ) := by
    rw [hsplit, Nat.cast_add]
    ring
  have hmain := Commons.Combinatorics.Hypergraph.card_size_gt_mul_le 𝓗 hlin' r₁ w
  rw [hM]
  have hr1pos : (0 : ℝ) < (r₁ : ℝ) := by exact_mod_cast hr1
  have h1 : ({e ∈ 𝓗 | w ∈ e ∧ r₁ < e.ncard}.ncard : ℝ) ≤ ((n : ℝ) - 1) / (r₁ : ℝ) := by
    rw [le_div_iff₀ hr1pos]
    linarith [hmain]
  have h2 : ((n : ℝ) - 1) / (r₁ : ℝ) ≤ 2 * (n : ℝ) / (r₁ : ℝ) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hr1pos)
    linarith [Nat.cast_nonneg (α := ℝ) n]
  linarith [h1, h2]

/-- **Lemma 11.3 (`lem:degree-lemma`), the Regularising Lemma.**  Let `𝓗` be a
linear `n`-vertex hypergraph without singleton edges, let `G = 𝓗^{(2)}` and let
`R_res ⊆ E(G)` be a `(ρ,ξ,ε,𝓥)`-reservoir of Type `A₁`, `A₂` or `B` (for a
family `𝓥` containing `V(𝓗)`), where in the Type `B` case the numerical
assumption `2ρ(n-1) + 1 ≤ εn` (the paper's `3ρ ≤ ε`) holds.  Then there is a
linear multi-hypergraph `𝓗'` obtained from `𝓗_small ∖ R_res` by adding
singleton edges, contained in `𝓗_reg`, such that
`d_{𝓗'}(w) = (1-ρ)(n-1 ± βn)` for every vertex `w`. -/
theorem regularising_lemma (𝓗 Rres : Hypergraph (Fin n)) (𝓥 : Set (Set (Fin n)))
    {ρ ξ ε β : ℝ} {r₁ : ℕ} (hm : DegreeMargins n ρ ξ ε β r₁)
    (hlin : 𝓗.IsLinear) (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e)
    (hV : (Set.univ : Set (Fin n)) ∈ 𝓥)
    (hres : IsReservoirTypeA1 𝓗 Rres 𝓥 ρ ξ ε ∨ IsReservoirTypeA2 𝓗 Rres 𝓥 ρ ξ ε ∨
            (IsReservoirTypeB 𝓗 Rres 𝓥 ρ ξ ε ∧ 2 * ρ * ((n : ℝ) - 1) + 1 ≤ ε * (n : ℝ))) :
    ∃ 𝓗' : MultiHypergraph n,
      𝓗'.edges = 𝓗.smallEdges r₁ \ Rres ∧
      𝓗' ≤ MultiHypergraph.regHypergraph 𝓗 ∧
      𝓗'.IsLinear ∧
      ∀ w : Fin n, |((𝓗'.deg w : ℝ)) - (1 - ρ) * ((n : ℝ) - 1)| ≤ 2 / 3 * β * (n : ℝ) :=
  regularising_lemma_core 𝓗 Rres 𝓥 hm hlin hbig hV hres
    (fun w => hdeg_sdiff_pow2_le 𝓗 hlin hbig w)
    (fun w => hdeg_sub_small_le 𝓗 hlin (le_trans (by norm_num) hm.hr1) w)

end

end ErdosFaberLovaszConjecture
