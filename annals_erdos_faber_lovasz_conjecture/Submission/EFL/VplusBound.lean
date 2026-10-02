import Submission.EFL.StabilityLoop
import Submission.EFL.DegreeBounds

/-!
# The volume bound for `U = V_+^{(1-ε)}(G)` (Claim 12.1, EP3, first part)

Let `𝓗` be a linear hypergraph on `Fin n`, let `W ⊆ 𝓗` be a family of edges of
size at least three with `∑_{e ∈ W} |e|(|e|-1) ≥ (1-δ)·n(n-1)` (the FPP-
extremal edges of the Type B case of Theorem 6.7), and let `U` consist of the
vertices whose `𝓗`-degree in the 2-shadow `G = 𝓗^{(2)}` is at least
`(1-ε)·n`.  Then `|U| ≤ 2δn`.

The proof is the paper's: the edges of `W` and the 2-edges of `𝓗` are
edge-disjoint subfamilies of the linear `𝓗`, so
`∑_{e ∈ W∪E(G)} |e|(|e|-1) ≤ n(n-1)`; hence `2·e(G) ≤ δ·n(n-1)`.  On the
other hand `|U|(1-ε)n ≤ ∑_{w∈U} d_G(w) ≤ 2·e(G)` by the handshake identity
`∑_w d_G(w) = ∑_{e ∈ G} |e| = 2·e(G)`.
-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- The canonical finset of a set of vertices. -/
def vertFinset (S : Set (Fin n)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun v => v ∈ S)

@[simp]
theorem mem_vertFinset {S : Set (Fin n)} {v : Fin n} : v ∈ vertFinset S ↔ v ∈ S := by
  simp [vertFinset]

theorem vertFinset_card (S : Set (Fin n)) : (vertFinset S).card = S.ncard := by
  rw [Set.ncard_eq_toFinset_card S (Set.toFinite S)]
  congr 1
  ext v
  simp [vertFinset, Set.Finite.mem_toFinset]

/-- The handshake identity for a family of 2-element edges:
`∑_w d_G(w) = ∑_{e ∈ G} |e|`. -/
theorem sum_degAt_eq_sum_ncard (G : Hypergraph (Fin n)) (hG2 : ∀ e ∈ G, e.ncard = 2) :
    (∑ w ∈ (Finset.univ : Finset (Fin n)), degAt G w) =
      (canonFinset G).sum (fun e => e.ncard) := by
  have hdeg (w : Fin n) : degAt G w = ((canonFinset G).filter (fun e => w ∈ e)).card := by
    rw [← hdeg_eq_degAt G hG2 w]
    rw [MultiHypergraph.hdeg, Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    congr 1
    ext e
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, canonFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
  calc (∑ w ∈ (Finset.univ : Finset (Fin n)), degAt G w)
      = ∑ w ∈ (Finset.univ : Finset (Fin n)),
          ((canonFinset G).filter (fun e => w ∈ e)).card := by
        exact Finset.sum_congr rfl (fun w _ => hdeg w)
    _ = ∑ w ∈ (Finset.univ : Finset (Fin n)),
          ∑ e ∈ canonFinset G, (if w ∈ e then (1 : ℕ) else 0) := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [Finset.card_filter]
    _ = ∑ e ∈ canonFinset G, ∑ w ∈ (Finset.univ : Finset (Fin n)),
          (if w ∈ e then (1 : ℕ) else 0) := Finset.sum_comm
    _ = ∑ e ∈ canonFinset G,
          ((Finset.univ : Finset (Fin n)).filter (fun w => w ∈ e)).card := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [Finset.card_filter]
    _ = ∑ e ∈ canonFinset G, e.ncard := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [← edgeSize_eq_ncard]
        rfl

/-- The handshake bound: for a family `G` of 2-element edges and any set `S` of
vertices, `∑_{w ∈ S} d_G(w) ≤ 2·e(G)`. -/
theorem sum_degAt_le_two_mul_card (G : Hypergraph (Fin n)) (hG2 : ∀ e ∈ G, e.ncard = 2)
    (S : Finset (Fin n)) :
    (∑ w ∈ S, degAt G w) ≤ 2 * (canonFinset G).card := by
  have h1 : (∑ w ∈ S, degAt G w) ≤
      ∑ w ∈ (Finset.univ : Finset (Fin n)), degAt G w :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun w _ _ => Nat.zero_le _)
  rw [sum_degAt_eq_sum_ncard G hG2] at h1
  have h2 : (canonFinset G).sum (fun e => e.ncard) ≤ 2 * (canonFinset G).card := by
    have h3 : (canonFinset G).sum (fun e => e.ncard) =
        (canonFinset G).sum (fun _ => 2) :=
      Finset.sum_congr rfl (fun e he => hG2 e (Finset.mem_filter.mp he).2)
    rw [h3, Finset.sum_const, smul_eq_mul, mul_comm]
  exact le_trans h1 h2

/-- **Claim 12.1 (EP3), first part.**  `|V_+^{(1-ε)}(G)| ≤ 2δn` if the
FPP-extremal family `W` has volume at least `1-δ`. -/
theorem card_Vplus_le_of_extremal (𝓗 W : Hypergraph (Fin n)) {δ ε : ℝ} (U : Set (Fin n))
    (hlin : 𝓗.IsLinear) (hW : W ⊆ 𝓗) (hWd : ∀ e ∈ W, 3 ≤ e.ncard)
    (hvol : (1 - δ) * ((n : ℝ) * ((n : ℝ) - 1)) ≤
      (canonFinset W).sum (fun e => (e.ncard : ℝ) * ((e.ncard : ℝ) - 1)))
    (hU : ∀ w ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt 𝓗.pow2 w : ℝ))
    (hδ0 : 0 ≤ δ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) :
    (U.ncard : ℝ) ≤ 2 * δ * (n : ℝ) := by
  have hG2 : ∀ e ∈ 𝓗.pow2, e.ncard = 2 :=
    fun e he => by rw [← edgeSize_eq_ncard]; exact (mem_pow2.mp he).2
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  by_cases hn : n ≤ 1
  · -- `Fin n` is tiny: `U` is empty
    have hempty : U = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr (fun w hw => ?_)
      have h1 := hU w hw
      have h3 := degAt_le_pred 𝓗.pow2 hG2 w
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos'
      · subst hn0
        exact Fin.elim0 w
      · have hn1 : n = 1 := by omega
        subst hn1
        have h6 : degAt 𝓗.pow2 w ≤ 0 := by simpa using h3
        have h5 : (degAt 𝓗.pow2 w : ℝ) ≤ 0 := by exact_mod_cast h6
        have h1' : (1 - ε) ≤ (degAt 𝓗.pow2 w : ℝ) := by simpa using h1
        linarith [hε1, h1', h5]
    rw [hempty, Set.ncard_empty, Nat.cast_zero]
    nlinarith [hδ0, hnR]
  · push_neg at hn
    -- the volume inequality
    have hnj : 2 ≤ n := hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    set M : Finset (Set (Fin n)) := canonFinset W ∪ canonFinset 𝓗.pow2 with hM
    have hMmem : ∀ e ∈ M, e ∈ 𝓗 := by
      intro e he
      rw [hM, Finset.mem_union] at he
      rcases he with he | he
      · exact hW (Finset.mem_filter.mp he).2
      · exact (mem_pow2.mp (Finset.mem_filter.mp he).2).1
    have hMlin : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ M → e₂ ∈ M → e₁ ≠ e₂ →
        (e₁ ∩ e₂ : Set (Fin n)).Subsingleton :=
      fun e₁ e₂ he₁ he₂ hne => hlin (hMmem e₁ he₁) (hMmem e₂ he₂) hne
    have hsum := sum_edgeSize_mul_sub_le_on M hMlin
    have hdisj : Disjoint (canonFinset W) (canonFinset 𝓗.pow2) := by
      rw [Finset.disjoint_left]
      intro e heW heG
      have h1 : 3 ≤ e.ncard := hWd e (Finset.mem_filter.mp heW).2
      have h2 : e.ncard = 2 := hG2 e (Finset.mem_filter.mp heG).2
      omega
    have hsumsplit : M.sum (fun e => edgeSize e * (edgeSize e - 1)) =
        (canonFinset W).sum (fun e => edgeSize e * (edgeSize e - 1)) +
        (canonFinset 𝓗.pow2).sum (fun e => edgeSize e * (edgeSize e - 1)) := by
      rw [hM, Finset.sum_union hdisj]
    have hpow2sum : (canonFinset 𝓗.pow2).sum (fun e => edgeSize e * (edgeSize e - 1)) =
        2 * (canonFinset 𝓗.pow2).card := by
      calc (canonFinset 𝓗.pow2).sum (fun e => edgeSize e * (edgeSize e - 1))
          = (canonFinset 𝓗.pow2).sum (fun _ => 2) := by
            refine Finset.sum_congr rfl (fun e he => ?_)
            have h2 : edgeSize e = 2 := by
              rw [edgeSize_eq_ncard]; exact hG2 e (Finset.mem_filter.mp he).2
            rw [h2]
        _ = 2 * (canonFinset 𝓗.pow2).card := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
    -- convert the volume inequality
    have hWsum : (canonFinset W).sum (fun e => edgeSize e * (edgeSize e - 1)) =
        (canonFinset W).sum (fun e => e.ncard * (e.ncard - 1)) := by
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [edgeSize_eq_ncard]
    have hvolR : (1 - δ) * ((n : ℝ) * ((n : ℝ) - 1)) +
        2 * ((canonFinset 𝓗.pow2).card : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
      have h1 : ((M.sum (fun e => edgeSize e * (edgeSize e - 1)) : ℕ) : ℝ) ≤
          ((n * (n - 1) : ℕ) : ℝ) := by exact_mod_cast hsum
      rw [hsumsplit, hpow2sum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h1
      have h2 : (((canonFinset W).sum (fun e => edgeSize e * (edgeSize e - 1)) : ℕ) : ℝ) =
          (canonFinset W).sum (fun e => (e.ncard : ℝ) * ((e.ncard : ℝ) - 1)) := by
        rw [hWsum]
        push_cast
        refine Finset.sum_congr rfl (fun e he => ?_)
        have h3 : 1 ≤ e.ncard := by
          have h4 := hWd e (Finset.mem_filter.mp he).2
          omega
        rw [Nat.cast_sub h3, Nat.cast_one]
      rw [h2] at h1
      have h3 : ((n * (n - 1) : ℕ) : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      linarith
    -- the handshake
    have hhand := sum_degAt_le_two_mul_card 𝓗.pow2 hG2 (vertFinset U)
    have hsumU : (U.ncard : ℝ) * ((1 - ε) * (n : ℝ)) ≤
        2 * ((canonFinset 𝓗.pow2).card : ℝ) := by
      have h1 : (∑ w ∈ vertFinset U, ((1 - ε) * (n : ℝ))) ≤
          ∑ w ∈ vertFinset U, (degAt 𝓗.pow2 w : ℝ) :=
        Finset.sum_le_sum (fun w hw => hU w (mem_vertFinset.mp hw))
      rw [Finset.sum_const, nsmul_eq_mul] at h1
      rw [vertFinset_card] at h1
      have h4 : ((∑ w ∈ vertFinset U, degAt 𝓗.pow2 w : ℕ) : ℝ) ≤
          2 * ((canonFinset 𝓗.pow2).card : ℝ) := by exact_mod_cast hhand
      push_cast at h4
      linarith
    -- combine
    have hB : 2 * ((canonFinset 𝓗.pow2).card : ℝ) ≤
        δ * ((n : ℝ) * ((n : ℝ) - 1)) := by
      have hN : (1 - δ) * ((n : ℝ) * ((n : ℝ) - 1)) =
          (n : ℝ) * ((n : ℝ) - 1) - δ * ((n : ℝ) * ((n : ℝ) - 1)) := by ring
      linarith [hvolR, hN]
    have hD : (U.ncard : ℝ) * ((1 / 2 : ℝ) * (n : ℝ)) ≤ δ * ((n : ℝ) * ((n : ℝ) - 1)) := by
      have hC : (1 / 2 : ℝ) * (n : ℝ) ≤ (1 - ε) * (n : ℝ) := by nlinarith [hε1]
      nlinarith [hsumU, hB, hC]
    have hE : (U.ncard : ℝ) * ((1 / 2 : ℝ) * (n : ℝ)) ≤
        (2 * δ * ((n : ℝ) - 1)) * ((1 / 2 : ℝ) * (n : ℝ)) := by
      have h2 : (2 * δ * ((n : ℝ) - 1)) * ((1 / 2 : ℝ) * (n : ℝ)) =
          δ * ((n : ℝ) * ((n : ℝ) - 1)) := by ring
      rw [h2]
      exact hD
    have hF : (0 : ℝ) < (1 / 2 : ℝ) * (n : ℝ) := by linarith [hnpos]
    have hG : (U.ncard : ℝ) ≤ 2 * δ * ((n : ℝ) - 1) := le_of_mul_le_mul_right hE hF
    nlinarith [hG, hδ0, hnR]

end

end ErdosFaberLovaszConjecture
