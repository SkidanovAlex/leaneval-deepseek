import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith.Frontend
import Submission.EFL.Nearfull.ExistsMaximalDisjointPairing
import Submission.Commons.Combinatorics.Hypergraph.pairing_of_useful_pairs

set_option autoImplicit false

namespace Commons.Combinatorics.Hypergraph

open Classical

/-- The two ways of saying that a hyperedge meets both `e` and `f` (as nonempty
intersection, or as intersection different from the empty set) describe subtypes
with the same cardinality. -/
private lemma useful_card_eq_clique {n : ℕ} (𝓗 : Set (Set (Fin n)))
    (e f : {e : Set (Fin n) // e ∈ 𝓗}) :
    Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ e ∧ g ≠ f ∧
        ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧
        ((g : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty}
      = Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ e ∧ g ≠ f ∧
        (g : Set (Fin n)) ∩ (e : Set (Fin n)) ≠ (∅ : Set (Fin n)) ∧
        (g : Set (Fin n)) ∩ (f : Set (Fin n)) ≠ (∅ : Set (Fin n))} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun g => ?_))
  simp only [Set.nonempty_iff_ne_empty]

/-- From a real bound `(K : ℝ) ≤ n - 2` one gets the integer bound `K ≤ n - 2`. -/
private lemma nat_le_sub_two_of_real_clique {n K : ℕ} (h : (K : ℝ) ≤ (n : ℝ) - 2) :
    K ≤ n - 2 := by
  have h2 : ((K + 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    linarith
  have h3 : K + 2 ≤ n := by exact_mod_cast h2
  omega

/-- **Pairing of a useful family (clique form).**  In the hypothesis the common-neighbour
bound is only required for pairs `e, f ∈ A` that *meet*; this suffices because the proof
only ever applies it to a pair of distinct hyperedges left uncovered by a maximal
disjoint pairing, and such edges automatically meet. -/
theorem pairing_of_useful_family_clique {n : ℕ} (𝓗 : Set (Set (Fin n))) (t : ℕ)
    (A : Finset {e : Set (Fin n) // e ∈ 𝓗})
    (hAcard : 4 * t ≤ A.card)
    (hA : ∀ e ∈ A, ∀ f ∈ A, e ≠ f → (((e : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty →
      (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ e ∧ g ≠ f ∧
        (g : Set (Fin n)) ∩ (e : Set (Fin n)) ≠ (∅ : Set (Fin n)) ∧
        (g : Set (Fin n)) ∩ (f : Set (Fin n)) ≠ (∅ : Set (Fin n))} : ℝ) ≤ (n : ℝ) - 2))
    (hcard : n + t ≤ Nat.card {e : Set (Fin n) // e ∈ 𝓗}) :
    ∃ σ : Fin t → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗},
      Function.Injective (fun p : Fin t × Fin 2 => σ p.1 p.2) ∧
      (∀ i : Fin t, Disjoint ((σ i 0).1 : Set (Fin n)) ((σ i 1).1 : Set (Fin n))) := by
  classical
  obtain ⟨s, σ₀, hinj₀, hdisj₀, hmax₀⟩ := exists_maximal_disjoint_pairing 𝓗
  by_cases hst : t ≤ s
  · -- The maximal pairing already has at least `t` pairs: keep the first `t`.
    refine ⟨fun i b => σ₀ (Fin.castLE hst i) b, ?_, ?_⟩
    · rintro ⟨i, b⟩ ⟨j, b'⟩ h
      change σ₀ (Fin.castLE hst i) b = σ₀ (Fin.castLE hst j) b' at h
      have hh : (fun p : Fin s × Fin 2 => σ₀ p.1 p.2) (Fin.castLE hst i, b)
          = (fun p : Fin s × Fin 2 => σ₀ p.1 p.2) (Fin.castLE hst j, b') := h
      obtain ⟨h1, h2⟩ := Prod.mk.inj (hinj₀ hh)
      exact Prod.ext (Fin.castLE_injective hst h1) h2
    · intro i
      exact hdisj₀ (Fin.castLE hst i)
  · -- The maximal pairing has fewer than `t` pairs: the uncovered edges pairwise meet.
    have hsl : s < t := Nat.lt_of_not_le hst
    let cover : Finset {e : Set (Fin n) // e ∈ 𝓗} :=
      (Finset.univ : Finset (Fin s × Fin 2)).image (fun p => σ₀ p.1 p.2)
    have hcover_card : cover.card = 2 * s := by
      rw [Finset.card_image_of_injective _ hinj₀, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fin, Nat.mul_comm]
    have hcover_mem : ∀ x : {e : Set (Fin n) // e ∈ 𝓗},
        x ∈ cover ↔ x ∈ Set.range (fun p : Fin s × Fin 2 => σ₀ p.1 p.2) := by
      intro x
      simp only [cover, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
    -- The part of `A` not covered by the maximal pairing still has `≥ 2t` elements.
    let B : Finset {e : Set (Fin n) // e ∈ 𝓗} := A \ cover
    have hBcard : t * 2 ≤ B.card := by
      change t * 2 ≤ (A \ cover).card
      have hle : A.card - cover.card ≤ (A \ cover).card := Finset.le_card_sdiff cover A
      omega
    -- Choose `2t` distinct such edges.
    let x : Fin (t * 2) → {e : Set (Fin n) // e ∈ 𝓗} :=
      fun i => ((Finset.equivFin B).symm (Fin.castLE hBcard i) : ↥B).1
    have hx_inj : Function.Injective x := by
      intro i j hij
      have h1 : (Finset.equivFin B).symm (Fin.castLE hBcard i)
          = (Finset.equivFin B).symm (Fin.castLE hBcard j) := Subtype.ext hij
      have h2 : Fin.castLE hBcard i = Fin.castLE hBcard j :=
        (Finset.equivFin B).symm.injective h1
      exact Fin.castLE_injective hBcard h2
    have hx_mem : ∀ i, x i ∈ B := by
      intro i
      exact ((Finset.equivFin B).symm (Fin.castLE hBcard i) : ↥B).2
    let a : Fin t → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗} :=
      fun i b => x (finProdFinEquiv (i, b))
    have ha_inj : Function.Injective (fun p : Fin t × Fin 2 => a p.1 p.2) := by
      intro p q hpq
      have h1 : finProdFinEquiv p = finProdFinEquiv q := hx_inj hpq
      exact finProdFinEquiv.injective h1
    have ha_mem : ∀ p : Fin t × Fin 2, a p.1 p.2 ∈ B := by
      intro p; exact hx_mem _
    have ha_memA : ∀ p : Fin t × Fin 2, a p.1 p.2 ∈ A := by
      intro p; exact (Finset.mem_sdiff.mp (ha_mem p)).1
    have ha_notcover : ∀ p : Fin t × Fin 2, a p.1 p.2 ∉ cover := by
      intro p; exact (Finset.mem_sdiff.mp (ha_mem p)).2
    have ha_inter : ∀ p q : Fin t × Fin 2, p ≠ q →
        (((a p.1 p.2).1 : Set (Fin n)) ∩ ((a q.1 q.2).1 : Set (Fin n))).Nonempty := by
      intro p q hpq
      have hp : a p.1 p.2 ∉ Set.range (fun r : Fin s × Fin 2 => σ₀ r.1 r.2) :=
        fun h => ha_notcover p ((hcover_mem _).mpr h)
      have hq : a q.1 q.2 ∉ Set.range (fun r : Fin s × Fin 2 => σ₀ r.1 r.2) :=
        fun h => ha_notcover q ((hcover_mem _).mpr h)
      have hne : a p.1 p.2 ≠ a q.1 q.2 := fun h => hpq (ha_inj h)
      exact hmax₀ _ hp _ hq hne
    have ha_useful : ∀ i : Fin t,
        Nat.card {g : {e : Set (Fin n) // e ∈ 𝓗} //
            g ≠ a i 0 ∧ g ≠ a i 1 ∧ (g.1 ∩ (a i 0).1).Nonempty ∧
              (g.1 ∩ (a i 1).1).Nonempty} ≤ n - 2 := by
      intro i
      have h0 : a i 0 ∈ A := ha_memA (i, 0)
      have h1 : a i 1 ∈ A := ha_memA (i, 1)
      have hne : a i 0 ≠ a i 1 := by
        intro h
        have h' : ((i, (0 : Fin 2)) : Fin t × Fin 2) = (i, 1) := ha_inj h
        exact (by decide : ¬ ((0 : Fin 2) = 1)) (congrArg Prod.snd h')
      -- The two edges are distinct elements of `A` which are left uncovered by the
      -- maximal pairing, hence they meet; so the "clique" hypothesis applies.
      have hmeet : ((((a i 0).1 : Set (Fin n)) ∩ ((a i 1).1 : Set (Fin n)))).Nonempty :=
        ha_inter (i, 0) (i, 1) (by simp)
      have hreal := hA (a i 0) h0 (a i 1) h1 hne hmeet
      rw [useful_card_eq_clique 𝓗 (a i 0) (a i 1)]
      exact nat_le_sub_two_of_real_clique hreal
    exact pairing_of_useful_pairs (n := n) 𝓗 t a ha_inj ha_inter ha_useful hcard

end Commons.Combinatorics.Hypergraph
