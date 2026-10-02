import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

/-!
# Robustness of lower regularity under deleting a bounded-degree subgraph

This file proves Proposition 3.2(ii) of Glock–Kühn–Osthus (the graph-language
form used by the GKO development): if `G` is lower `(p, ε)`-regular on `n`
vertices and `H` has maximum degree at most `ηn`, then the graph `G \ H` is
lower `(p, max (2ε) (2√η))`-regular.

The proof has three ingredients:

* `crossEdges_le_sdiff_add`: the edges of `G` between `A` and `B` split into the
  edges of `G \ H` and the edges of `H`, so
  `e_{G∖H}(A,B) ≥ e_G(A,B) - e_H(A,B)`;
* `crossEdges_le_sum_deg`: `e_H(A,B) ≤ ∑_{a ∈ A} d_H(a) ≤ |A| · ηn`, and since
  `|B| ≥ max(2ε,2√η)n ≥ 2√η n` we get `√η|A||B| ≥ ηn|A|`;
* `ε + √η ≤ max (2ε) (2√η)`, which turns
  `(p-ε)|A||B| - √η|A||B|` into `(p - max(2ε,2√η))|A||B|`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators
open Classical

namespace Work.Deep.GKO

noncomputable section

/-! ## Counting lemmas for `crossEdges` -/

/-- The edges of `G` between the vertex sets `A` and `B` split into those of
`G \ H` and those of `H`: `e_G(A,B) ≤ e_{G∖H}(A,B) + e_H(A,B)`. -/
private theorem crossEdges_le_sdiff_add {n : ℕ} (G H : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    crossEdges G A B ≤ crossEdges (G \ H) A B + crossEdges H A B := by
  simp only [crossEdges]
  refine le_trans ?_ (Finset.card_union_le _ _)
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_union, SimpleGraph.sdiff_adj] at hp ⊢
  tauto

/-- `Nat.card` of the neighbour set is the cardinality of the corresponding
`Finset` of neighbours. -/
private theorem neighborSet_natCard {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    Nat.card (G.neighborSet v) = ((Finset.univ.filter (fun b => G.Adj v b))).card := by
  have h : G.neighborSet v =
      ((Finset.univ.filter (fun b => G.Adj v b) : Finset (Fin n)) : Set (Fin n)) := by
    ext b
    simp
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset]

/-- `e_H(A,B) ≤ ∑_{a ∈ A} d_H(a)`: every edge of `H` between `A` and `B` is
counted by the degree of its endpoint in `A`. -/
private theorem crossEdges_le_sum_deg {n : ℕ} (H : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    crossEdges H A B ≤ ∑ a ∈ A, Nat.card (H.neighborSet a) := by
  have hmain : ((A.product (Finset.univ : Finset (Fin n))).filter
        (fun p : Fin n × Fin n => H.Adj p.1 p.2)).card
      = ∑ a ∈ A, (Finset.univ.filter (fun b => H.Adj a b)).card := by
    calc ((A.product (Finset.univ : Finset (Fin n))).filter
          (fun p : Fin n × Fin n => H.Adj p.1 p.2)).card
        = ∑ p ∈ A.product (Finset.univ : Finset (Fin n)),
            (if H.Adj p.1 p.2 then 1 else 0) := by
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = ∑ a ∈ A, ∑ b ∈ (Finset.univ : Finset (Fin n)),
            (if H.Adj a b then 1 else 0) :=
          Finset.sum_product A Finset.univ
            (fun p : Fin n × Fin n => if H.Adj p.1 p.2 then 1 else 0)
      _ = ∑ a ∈ A, (Finset.univ.filter (fun b => H.Adj a b)).card := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc crossEdges H A B
      = ((A.product B).filter (fun p : Fin n × Fin n => H.Adj p.1 p.2)).card := rfl
    _ ≤ ((A.product (Finset.univ : Finset (Fin n))).filter
          (fun p : Fin n × Fin n => H.Adj p.1 p.2)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.product_subset_product (le_refl A) (Finset.subset_univ B)))
    _ = ∑ a ∈ A, (Finset.univ.filter (fun b => H.Adj a b)).card := hmain
    _ = ∑ a ∈ A, Nat.card (H.neighborSet a) :=
        Finset.sum_congr rfl (fun a _ => (neighborSet_natCard H a).symm)

/-! ## The main statement -/

/-- Robustness of lower regularity under deleting a bounded-degree subgraph (Proposition 3.2(ii) of Glock–Kühn–Osthus): if `H` has maximum degree at most `ηn`, then `G \ H` is lower `(p, max(2ε, 2√η))`-regular.

Proof sketch: `e_{G∖H}(A,B) ≥ e_G(A,B) - e_H(A,B) ≥ (p-ε)|A||B| - ηn|A| ≥ (p-ε)|A||B| - √η|A||B|` because `|B| ≥ max(2ε,2√η)n ≥ 2√η n ≥ √η n`; then use `ε + √η ≤ max (2ε) (2√η)`. -/
theorem lowerReg_of_delete {n : ℕ} (G H : SimpleGraph (Fin n)) {p ε η : ℝ}
    (hlr : Work.Deep.GKO.LowerReg G p ε) (hη : 0 ≤ η)
    (hH : ∀ v : Fin n, (Nat.card (H.neighborSet v) : ℝ) ≤ η * (n : ℝ)) :
    Work.Deep.GKO.LowerReg (G \ H) p (max (2 * ε) (2 * Real.sqrt η)) := by
  intro A B hdisj hA hB
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hA0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
  have hsqrt : (0 : ℝ) ≤ Real.sqrt η := Real.sqrt_nonneg η
  have hsq : Real.sqrt η * Real.sqrt η = η := Real.mul_self_sqrt hη
  set δ : ℝ := max (2 * ε) (2 * Real.sqrt η) with hδdef
  -- `ε ≤ δ`: if `ε ≥ 0` this follows from `2ε ≤ δ`, otherwise from `ε < 0 ≤ 2√η ≤ δ`.
  have hεδ : ε ≤ δ := by
    rw [hδdef]
    by_cases h : 0 ≤ ε
    · linarith [le_max_left (2 * ε) (2 * Real.sqrt η)]
    · have h' : ε < 0 := not_le.mp h
      linarith [le_max_right (2 * ε) (2 * Real.sqrt η), Real.sqrt_nonneg η]
  -- `ε + √η ≤ δ`: `δ = 2 · max ε √η ≥ ε + √η`, and the negative-`ε` case is easier.
  have hεηδ : ε + Real.sqrt η ≤ δ := by
    rw [hδdef]
    by_cases h : 0 ≤ ε
    · linarith [le_max_left (2 * ε) (2 * Real.sqrt η), le_max_right (2 * ε) (2 * Real.sqrt η)]
    · have h' : ε < 0 := not_le.mp h
      linarith [le_max_right (2 * ε) (2 * Real.sqrt η), Real.sqrt_nonneg η]
  have h2ηδ : 2 * Real.sqrt η ≤ δ := by rw [hδdef]; exact le_max_right _ _
  -- lower regularity of `G` applies to `A`, `B` since `ε ≤ δ`.
  have hεnA : ε * (n : ℝ) ≤ (A.card : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hεδ hn
    linarith [hA]
  have hεnB : ε * (n : ℝ) ≤ (B.card : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hεδ hn
    linarith [hB]
  have hreg := hlr A B hdisj hεnA hεnB
  -- splitting the edge count
  have hspl : (crossEdges G A B : ℝ) ≤
      (crossEdges (G \ H) A B : ℝ) + (crossEdges H A B : ℝ) := by
    exact_mod_cast crossEdges_le_sdiff_add G H A B
  -- `e_H(A,B) ≤ |A| · ηn`
  have hdeg : (crossEdges H A B : ℝ) ≤ (A.card : ℝ) * (η * (n : ℝ)) := by
    have h1 : (crossEdges H A B : ℝ) ≤ ∑ a ∈ A, (Nat.card (H.neighborSet a) : ℝ) := by
      exact_mod_cast crossEdges_le_sum_deg H A B
    have h2 : ∑ a ∈ A, (Nat.card (H.neighborSet a) : ℝ) ≤ ∑ _a ∈ A, η * (n : ℝ) :=
      Finset.sum_le_sum (fun a _ => hH a)
    have h3 : ∑ _a ∈ A, η * (n : ℝ) = (A.card : ℝ) * (η * (n : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    linarith
  -- `ηn ≤ √η |B|`, because `|B| ≥ 2√η n`
  have hsqrtB : η * (n : ℝ) ≤ Real.sqrt η * (B.card : ℝ) := by
    have h1 : 2 * Real.sqrt η * (n : ℝ) ≤ δ * (n : ℝ) := mul_le_mul_of_nonneg_right h2ηδ hn
    have h2 : 2 * Real.sqrt η * (n : ℝ) ≤ (B.card : ℝ) := by linarith [hB]
    have h3 := mul_le_mul_of_nonneg_left h2 hsqrt
    nlinarith [h3, hsq, hη, hn, hsqrt]
  have hAZ : (A.card : ℝ) * (η * (n : ℝ)) ≤ Real.sqrt η * (A.card : ℝ) * (B.card : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hsqrtB hA0
    nlinarith [h1]
  -- `(p - δ)|A||B| ≤ (p - ε - √η)|A||B|`
  have hmul : (p - δ) * (A.card : ℝ) * (B.card : ℝ) ≤
      (p - ε - Real.sqrt η) * (A.card : ℝ) * (B.card : ℝ) := by
    have h : p - δ ≤ p - ε - Real.sqrt η := by linarith [hεηδ]
    have h' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hA0) hB0
    linarith [h']
  have hZ : (crossEdges H A B : ℝ) ≤ Real.sqrt η * (A.card : ℝ) * (B.card : ℝ) := by
    linarith [hdeg, hAZ]
  -- `(p - ε - √η)|A||B| ≤ e_{G∖H}(A,B)`
  have hcomb : (p - ε - Real.sqrt η) * (A.card : ℝ) * (B.card : ℝ) ≤
      (crossEdges (G \ H) A B : ℝ) := by
    nlinarith [hreg, hspl, hZ]
  linarith [hmul, hcomb]

end

end Work.Deep.GKO
