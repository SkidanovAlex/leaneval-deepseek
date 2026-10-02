import Submission.EFL.LargeEdgeCase22
import Submission.EFL.Case21

/-!
# Case 2.2 of Theorem 6.1: the FPP-extremal alternative

This module completes the extremal branch of Theorem 6.1 (`large-edge-thm`):
the Case 2.2 obligation `h22` of `LargeEdgeCases.largeEdge_of_blocks`.

In Case 2.2 the App-2 volume set `W₂` is non-empty and `r₃ ≥ (1−δ)√n`, so
`W₂` consists of FPP-extremal edges of volume `≥ 1 − δ³` (hence `≥ 1 − δ`) and,
crucially, *no* edge of `𝓗` has size `≥ δn/2`.

The blocks of Figure 3 are recoloured as follows (paper §7, Case 2.2):

* `𝓗₂^left` (`= Left₂`) together with `𝓗_huge` forms the left block
  `A = case2HugeLeft₂ β 𝓗 Left₂`; Lemma 5.1 (`linear_nearfull_colouring`)
  gives a colouring `φ₁` of `A` with at most `n` colours, every colour on at
  most two edges — hence every colour class of `φ₁` covers at most `δn`
  vertices, and `φ₁` restricted to the non-huge edges is `β/2`-bounded;
* `C_huge` is the set of colours that `φ₁` assigns to huge edges
  (`|C_huge| ≤ 32/β²`), and `C_med ⊆ univ ∖ C_huge` has size `⌊γ₂n⌋`;
* Proposition 6.9 on `𝓗₂^good` (`α₁ = σ`, `α₂ = β/5`) with the lists
  `(univ ∖ C_huge) ∖ φ₁(N_{Left₂}(e))` gives `φ₂` (Claim
  `claim:bounded-colouring-extension2`);
* Proposition 6.9 on `𝓗₁^good` (`α₁ = γ₂/3`, `α₂ = γ₁/2`) with the lists
  `C_med ∖ (φ₁(N_{Left₂}(e)) ∪ φ₂(N_{Good₂}(e)))` gives `φ₃` (Claim
  `claim:bounded-colouring-extension3`); since `𝓗_med ⊆ 𝓗₁^good` in Case 2.2,
  `φ₃` colours all medium edges inside `C_med`;
* the three colourings glue with `coloringUnionCross` (twice), and the
  colour-class estimates (i)–(iii) of `LargeEdgeExtremal` follow from the
  size bound `≤ δn/2` and the `α`-boundedness of the pieces.

There is a fourth sub-case: `W₂ ≠ ∅`, `(1−δ)√n ≤ r₃` and
`r₃ > √(n/(1−4σ))`.  The pair count `e(𝓗₂^left)·C(r₃,2) ≤ C(n,2)` then gives
`e(𝓗₂^left) ≤ (1−3σ)n` (`case22_left_card_le`), so the edges of the App-2
initial segment have all their preceding neighbours inside it, the App-2
ordering is *good* (`case22_good_ordering`), and Case 1 applies
(`case1_of_blocks_of_good`).  This supplies the paper's
`eqn:d3-upper-bound`; with it, `largeEdge_of_blocks_full` is the case split
of Theorem 6.1 with the Case-2.2 obligation discharged.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## The block decomposition of Case 2.2 -/

/-- The left block `𝓗_huge ∪ 𝓗₂^left` of Case 2.2 is a sub-hypergraph. -/
theorem case22_hugeLeft_subset {β : ℝ} {𝓗 Left₂ : Hypergraph (Fin n)} (hL₂sub : Left₂ ⊆ 𝓗) :
    case2HugeLeft₂ β 𝓗 Left₂ ⊆ 𝓗 := by
  rintro e (he | he)
  · exact (mem_hugeEdges 𝓗 β e).mp he |>.1
  · exact hL₂sub he

/-- The three blocks of Case 2.2 — `𝓗_huge ∪ 𝓗₂^left`, `𝓗₂^good`, `𝓗₁^good` —
cover `𝓗` (the Case-2 partition `𝓗 = 𝓗₃ ⊔ W₂ ⊔ 𝓗₂^good ⊔ 𝓗₁^good` with
`W₂ ⊆ Left₂` and `𝓗₃ = 𝓗_huge ∪ (𝓗₂^left ∖ W₂)`). -/
theorem case22_cover {n : ℕ} {β γ₂ σ δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂} {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃) :
    case2HugeLeft₂ β 𝓗 Left₂ ∪ Good₂ ∪ Good₁ = 𝓗 := by
  classical
  have hL₂𝓗 : Left₂ ⊆ 𝓗 := fun x hx => nonHuge_subset 𝓗 β (hB.hL₁sub (hB.hL₂sub hx))
  ext e
  constructor
  · rintro ((he | hG₂) | hG₁)
    · exact case22_hugeLeft_subset hL₂𝓗 he
    · exact nonHuge_subset 𝓗 β (hB.hL₁sub (hB.hG₂sub hG₂))
    · exact nonHuge_subset 𝓗 β (hB.hG₁sub hG₁)
  · intro he
    have h1 : e ∈ (H₃ ∪ W₂ ∪ Good₂) ∪ Good₁ := by rw [hB.hcover]; exact he
    rw [Set.mem_union] at h1
    rcases h1 with h1 | hG₁
    · rw [Set.mem_union] at h1
      rcases h1 with h1 | hG₂
      · rw [Set.mem_union] at h1
        rcases h1 with hH | hW
        · by_cases hh : β * (n : ℝ) / 4 ≤ (edgeSize e : ℝ)
          · exact Or.inl (Or.inl (Or.inl ((mem_hugeEdges 𝓗 β e).mpr ⟨hB.hH₃sub hH, hh⟩)))
          · have hnh : e ∈ nonHuge 𝓗 β := ⟨hB.hH₃sub hH, hh⟩
            have h2 : e ∈ Good₁ ∪ Left₁ := by rw [hB.hpart₁]; exact hnh
            rw [Set.mem_union] at h2
            rcases h2 with hg | hl
            · exact Or.inr hg
            · have h3 : e ∈ Good₂ ∪ Left₂ := by rw [hB.hpart₂]; exact hl
              rw [Set.mem_union] at h3
              rcases h3 with hg₂ | hl₂
              · exact Or.inl (Or.inr hg₂)
              · exact Or.inl (Or.inl (Or.inr hl₂))
        · exact Or.inl (Or.inl (Or.inr (hB.hW₂sub hW)))
      · exact Or.inl (Or.inr hG₂)
    · exact Or.inr hG₁

/-- `(𝓗_huge ∪ 𝓗₂^left) ∩ 𝓗₂^good = ∅`. -/
theorem case22_disjoint_hugeLeft_good₂ {n : ℕ} {β γ₂ σ δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂} {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃) :
    Disjoint (case2HugeLeft₂ β 𝓗 Left₂) Good₂ := by
  rw [Set.disjoint_left]
  rintro e (he | he) hG₂
  · exact (hB.hL₁sub (hB.hG₂sub hG₂)).2 he.2
  · exact (Set.disjoint_left.mp hB.hdisj₂) hG₂ he

/-- `(𝓗_huge ∪ 𝓗₂^left) ∩ 𝓗₁^good = ∅`. -/
theorem case22_disjoint_hugeLeft_good₁ {n : ℕ} {β γ₂ σ δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂} {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃) :
    Disjoint (case2HugeLeft₂ β 𝓗 Left₂) Good₁ := by
  rw [Set.disjoint_left]
  rintro e (he | he) hG₁
  · exact (hB.hG₁sub hG₁).2 he.2
  · exact (Set.disjoint_left.mp hB.hdisj₁) hG₁ (hB.hL₂sub he)

/-! ## Case 2.2: the edge-size bound -/

/-- **Case 2.2: every edge has size at most `δn/2`.**  Edges outside the
App-2 volume set `W₂` have `vol(e) ≤ 1 − vol(W₂) ≤ δ³`, whence `|e| ≤ δn/2`;
edges inside `W₂` have `|e| ≤ sizeFactor (3σ) 1 · r₃ ≤ (1+δ)√n ≤ δn/2`. -/
theorem case22_noBig {n r₁ r₀ r₃ : ℕ} {β γ₂ σ δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂} {r₂ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hW₂ne : W₂ ≠ ∅)
    (hr₃up : (r₃ : ℝ) ≤ Real.sqrt ((n : ℝ) / (1 - 4 * σ)))
    (hfac : sizeFactor (3 * σ) 1 * Real.sqrt ((n : ℝ) / (1 - 4 * σ)) ≤
      (1 + δ) * Real.sqrt (n : ℝ))
    (hlin : 𝓗.IsLinear) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 16) (hn1 : 1 ≤ n)
    (hnδ : 8 ≤ δ ^ 2 * (n : ℝ))
    (hsmall : (1 + δ) * Real.sqrt (n : ℝ) ≤ δ * (n : ℝ) / 2)
    (hden : 0 < (n : ℝ) * ((n - 1 : ℕ) : ℝ)) :
    ∀ e : Set (Fin n), e ∈ 𝓗 → (edgeSize e : ℝ) ≤ δ * (n : ℝ) / 2 := by
  refine edgeSize_le_half_mul_of_blocks (W := W₂) hlin ?_ ?_ ?_ hδ0 hδ1 hn1 hnδ hsmall hden
  · intro e he
    exact nonHuge_subset 𝓗 β (hB.hL₁sub (hB.hL₂sub (hB.hW₂sub he)))
  · rcases hB.hW₂vol with hemp | hvol
    · exact absurd hemp hW₂ne
    · exact hvol
  · intro e he
    have h1 := hB.hW₂size_le e he
    have h2 : sizeFactor (3 * σ) 1 * (r₃ : ℝ) ≤
        sizeFactor (3 * σ) 1 * Real.sqrt ((n : ℝ) / (1 - 4 * σ)) :=
      mul_le_mul_of_nonneg_left hr₃up (le_of_lt (sizeFactor_pos (3 * σ) 1))
    linarith

/-! ## Case 2.2: the lists of the two Proposition 6.9 applications -/

/-- The colours that `φ₁` assigns to the `𝓗₂^left`-neighbours of `e`: the
colours forbidden for the edge `e` in the colouring of `𝓗₂^good`. -/
def case22Forb₁ {β : ℝ} {𝓗 Left₂ : Hypergraph (Fin n)} [Fintype Left₂]
    (φ₁ : (case2HugeLeft₂ β 𝓗 Left₂).Coloring (Fin n)) (e : Set (Fin n)) : Finset (Fin n) := by
  classical
  exact ((Finset.univ : Finset Left₂).filter
    (fun g : Left₂ => (((g : Set (Fin n)) ∩ e).Nonempty))).image
      (fun g : Left₂ => φ₁.labels ⟨(g : Set (Fin n)), Or.inr g.2⟩)

/-- Membership in `case22Forb₁`. -/
theorem mem_case22Forb₁ {β : ℝ} {𝓗 Left₂ : Hypergraph (Fin n)} [Fintype Left₂]
    {φ₁ : (case2HugeLeft₂ β 𝓗 Left₂).Coloring (Fin n)} {e : Set (Fin n)} {c : Fin n} :
    c ∈ case22Forb₁ φ₁ e ↔
      ∃ g : Left₂, (((g : Set (Fin n)) ∩ e).Nonempty) ∧
        φ₁.labels ⟨(g : Set (Fin n)), Or.inr g.2⟩ = c := by
  rw [case22Forb₁]
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The forbidden colours are at most the number of neighbours. -/
theorem card_case22Forb₁_le {β : ℝ} {𝓗 Left₂ : Hypergraph (Fin n)} [Fintype Left₂]
    (φ₁ : (case2HugeLeft₂ β 𝓗 Left₂).Coloring (Fin n)) (e : Set (Fin n)) :
    (case22Forb₁ φ₁ e).card ≤
      Nat.card {g : Left₂ // (((g : Set (Fin n)) ∩ e).Nonempty)} := by
  classical
  have h1 : (case22Forb₁ φ₁ e).card ≤
      ((Finset.univ : Finset Left₂).filter
        (fun g : Left₂ => (((g : Set (Fin n)) ∩ e).Nonempty))).card := by
    rw [case22Forb₁]
    exact Finset.card_image_le
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h1

/-- The colours that `φ₂` assigns to the `𝓗₂^good`-neighbours of `e`. -/
def case22Forb₂ {Good₂ : Hypergraph (Fin n)} [Fintype Good₂]
    (φ₂ : Good₂.Coloring (Fin n)) (e : Set (Fin n)) : Finset (Fin n) := by
  classical
  exact ((Finset.univ : Finset Good₂).filter
    (fun g : Good₂ => (((g : Set (Fin n)) ∩ e).Nonempty))).image φ₂.labels

/-- Membership in `case22Forb₂`. -/
theorem mem_case22Forb₂ {Good₂ : Hypergraph (Fin n)} [Fintype Good₂]
    {φ₂ : Good₂.Coloring (Fin n)} {e : Set (Fin n)} {c : Fin n} :
    c ∈ case22Forb₂ φ₂ e ↔
      ∃ g : Good₂, (((g : Set (Fin n)) ∩ e).Nonempty) ∧ φ₂.labels g = c := by
  rw [case22Forb₂]
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The forbidden colours are at most the number of neighbours. -/
theorem card_case22Forb₂_le {Good₂ : Hypergraph (Fin n)} [Fintype Good₂]
    (φ₂ : Good₂.Coloring (Fin n)) (e : Set (Fin n)) :
    (case22Forb₂ φ₂ e).card ≤
      Nat.card {g : Good₂ // (((g : Set (Fin n)) ∩ e).Nonempty)} := by
  classical
  have h1 : (case22Forb₂ φ₂ e).card ≤
      ((Finset.univ : Finset Good₂).filter
        (fun g : Good₂ => (((g : Set (Fin n)) ∩ e).Nonempty))).card := by
    rw [case22Forb₂]
    exact Finset.card_image_le
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h1

/-- The list of colours available to the edge `e` of `𝓗₂^good`: all colours
outside `C_huge`, except the `φ₁`-colours of the `𝓗₂^left`-neighbours of `e`
(Claim `claim:bounded-colouring-extension2`). -/
def case22List₂ {β : ℝ} {𝓗 Left₂ : Hypergraph (Fin n)} [Fintype Left₂]
    (φ₁ : (case2HugeLeft₂ β 𝓗 Left₂).Coloring (Fin n)) (Chuge : Finset (Fin n))
    (e : Set (Fin n)) : Finset (Fin n) :=
  (Finset.univ \ Chuge) \ case22Forb₁ φ₁ e

/-- The list of colours available to the edge `e` of `𝓗₁^good`: the set
`C_med`, except the `φ₁`-colours of the `𝓗₂^left`-neighbours of `e` and the
`φ₂`-colours of the `𝓗₂^good`-neighbours of `e` (Claim
`claim:bounded-colouring-extension3`). -/
def case22List₃ {β : ℝ} {𝓗 Left₂ : Hypergraph (Fin n)} [Fintype Left₂]
    {Good₂ : Hypergraph (Fin n)} [Fintype Good₂]
    (φ₁ : (case2HugeLeft₂ β 𝓗 Left₂).Coloring (Fin n))
    (φ₂ : Good₂.Coloring (Fin n)) (Cmed : Finset (Fin n)) (e : Set (Fin n)) : Finset (Fin n) :=
  Cmed \ (case22Forb₁ φ₁ e ∪ case22Forb₂ φ₂ e)

/-- Membership in `case22List₂`. -/
theorem mem_case22List₂ {β : ℝ} {𝓗 Left₂ : Hypergraph (Fin n)} [Fintype Left₂]
    {φ₁ : (case2HugeLeft₂ β 𝓗 Left₂).Coloring (Fin n)} {Chuge : Finset (Fin n)}
    {e : Set (Fin n)} {c : Fin n} :
    c ∈ case22List₂ φ₁ Chuge e ↔ (c ∈ Finset.univ ∧ c ∉ Chuge) ∧ c ∉ case22Forb₁ φ₁ e := by
  simp only [case22List₂, Finset.mem_sdiff]

/-- Membership in `case22List₃`. -/
theorem mem_case22List₃ {β : ℝ} {𝓗 Left₂ : Hypergraph (Fin n)} [Fintype Left₂]
    {Good₂ : Hypergraph (Fin n)} [Fintype Good₂]
    {φ₁ : (case2HugeLeft₂ β 𝓗 Left₂).Coloring (Fin n)}
    {φ₂ : Good₂.Coloring (Fin n)} {Cmed : Finset (Fin n)} {e : Set (Fin n)} {c : Fin n} :
    c ∈ case22List₃ φ₁ φ₂ Cmed e ↔ c ∈ Cmed ∧ c ∉ case22Forb₁ φ₁ e ∧
      c ∉ case22Forb₂ φ₂ e := by
  simp only [case22List₃, Finset.mem_sdiff, Finset.mem_union, not_or]

/-! ## Case 2.2: the forward-degree bounds behind the two claims -/

/-- **Forward-degree bound for `𝓗₂^good` in Case 2.2.**  The number of
`𝓗₂^left`-neighbours of `e` plus its `𝓗₂^good`-forward degree (in any ordering
of `𝓗₂^good` restricting `ord₂`) is at most the `𝓗₁^left`-forward degree of
`e`, hence at most `(1−3σ)n`. -/
theorem case22_fwddeg_good₂ {n : ℕ} {Left₁ Left₂ Good₂ : Hypergraph (Fin n)}
    {k₂ : ℕ} (ord₂ : Left₁ ≃ Fin k₂) (hL₂sub : Left₂ ⊆ Left₁) (hG₂sub : Good₂ ⊆ Left₁)
    (hpart₂ : Good₂ ∪ Left₂ = Left₁) (hdisj₂ : Disjoint Good₂ Left₂)
    (hseg₂ : ∀ f u : Left₁, (f : Set (Fin n)) ∈ Left₂ → (u : Set (Fin n)) ∈ Good₂ →
      (ord₂ f : ℕ) ≤ (ord₂ u : ℕ))
    {kB : ℕ} (ordB : Good₂ ≃ Fin kB)
    (hrankB : ∀ a b : Good₂, (ordB a : ℕ) ≤ (ordB b : ℕ) ↔
      (ord₂ ⟨(a : Set (Fin n)), hG₂sub a.2⟩ : ℕ) ≤
        (ord₂ ⟨(b : Set (Fin n)), hG₂sub b.2⟩ : ℕ))
    {σ : ℝ}
    (hdeg₂ : ∀ e : Left₁, (e : Set (Fin n)) ∈ Good₂ →
      (precedingDegree Left₁ ord₂ e : ℝ) ≤ (1 - 3 * σ) * (n : ℝ)) :
    ∀ e : Good₂,
      ((Nat.card {g : Left₂ // (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) +
        (precedingDegree Good₂ ordB e : ℝ) ≤ (1 - 3 * σ) * (n : ℝ) := by
  classical
  intro e
  have hfib := precedingDegree_ge_fiber_add (𝓖 := Left₁) (𝓖₁ := Left₂) (𝓖₂ := Good₂)
    ord₂ hL₂sub hG₂sub
    (by
      intro x hx
      have h : x ∈ Good₂ ∨ x ∈ Left₂ := by
        have h2 := hpart₂ ▸ hx
        simpa only [Set.mem_union] using h2
      exact h.symm)
    hdisj₂.symm
    (by
      intro f u
      exact hseg₂ ⟨(f : Set (Fin n)), hL₂sub f.2⟩ ⟨(u : Set (Fin n)), hG₂sub u.2⟩ f.2 u.2)
    e
  have hpred : (precedingDegree Good₂ ordB e : ℝ) = (case2Pred₂ ord₂ Good₂ hG₂sub e : ℝ) := by
    rw [case2_pred₂_eq ord₂ hG₂sub ordB hrankB e]
  have hpred' : (Nat.card {f : Good₂ // f ≠ e ∧
        (ord₂ ⟨(f : Set (Fin n)), hG₂sub f.2⟩ : ℕ) ≤
          (ord₂ ⟨(e : Set (Fin n)), hG₂sub e.2⟩ : ℕ) ∧
        (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℝ) =
      (case2Pred₂ ord₂ Good₂ hG₂sub e : ℝ) := rfl
  have hfib' : ((Nat.card {f : Left₂ // (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) +
      (Nat.card {f : Good₂ // f ≠ e ∧
        (ord₂ ⟨(f : Set (Fin n)), hG₂sub f.2⟩ : ℕ) ≤
          (ord₂ ⟨(e : Set (Fin n)), hG₂sub e.2⟩ : ℕ) ∧
        (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℝ) ≤
      (precedingDegree Left₁ ord₂ ⟨(e : Set (Fin n)), hG₂sub e.2⟩ : ℝ) := by
    exact_mod_cast hfib
  have hdeg := hdeg₂ ⟨(e : Set (Fin n)), hG₂sub e.2⟩ e.2
  rw [hpred, ← hpred']
  linarith [hfib', hdeg]

/-- **Forward-degree bound for `𝓗₁^good` in Case 2.2.**  The numbers of
`𝓗₂^left`- and `𝓗₂^good`-neighbours of `e` plus its `𝓗₁^good`-forward degree
(in any ordering of `𝓗₁^good` restricting `ord₁`) is at most the
`𝓗₁`-forward degree of `e` in the App-1 ordering, hence at most `γ₂n/3`. -/
theorem case22_fwddeg_good₁ {n : ℕ} {β : ℝ}
    {𝓗 Left₁ Left₂ Good₂ Good₁ : Hypergraph (Fin n)}
    {k₁ : ℕ} (ord₁ : nonHuge 𝓗 β ≃ Fin k₁)
    (hL₁sub : Left₁ ⊆ nonHuge 𝓗 β) (hG₁sub : Good₁ ⊆ nonHuge 𝓗 β)
    (hpart₁ : Good₁ ∪ Left₁ = nonHuge 𝓗 β) (hdisj₁ : Disjoint Good₁ Left₁)
    (hseg₁ : ∀ f u : nonHuge 𝓗 β, (f : Set (Fin n)) ∈ Left₁ →
      (u : Set (Fin n)) ∈ Good₁ → (ord₁ f : ℕ) ≤ (ord₁ u : ℕ))
    (hG₂sub : Good₂ ⊆ Left₁) (hL₂sub : Left₂ ⊆ Left₁) (hdisj₂ : Disjoint Good₂ Left₂)
    {kC : ℕ} (ordC : Good₁ ≃ Fin kC)
    (hrankC : ∀ a b : Good₁, (ordC a : ℕ) ≤ (ordC b : ℕ) ↔
      (ord₁ ⟨(a : Set (Fin n)), hG₁sub a.2⟩ : ℕ) ≤
        (ord₁ ⟨(b : Set (Fin n)), hG₁sub b.2⟩ : ℕ))
    {γ₂ : ℝ}
    (hdeg₁ : ∀ e : nonHuge 𝓗 β, (e : Set (Fin n)) ∈ Good₁ →
      (precedingDegree (nonHuge 𝓗 β) ord₁ e : ℝ) ≤ (γ₂ / 3) * (n : ℝ)) :
    ∀ e : Good₁,
      ((Nat.card {g : Left₂ // (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) +
        ((Nat.card {g : Good₂ // (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) +
        (precedingDegree Good₁ ordC e : ℝ) ≤ (γ₂ / 3) * (n : ℝ) := by
  classical
  intro e
  have hfib := precedingDegree_ge_fiber_add (𝓖 := nonHuge 𝓗 β) (𝓖₁ := Left₁) (𝓖₂ := Good₁)
    ord₁ hL₁sub hG₁sub
    (by
      intro x hx
      have h : x ∈ Good₁ ∨ x ∈ Left₁ := by
        have h2 := hpart₁ ▸ hx
        simpa only [Set.mem_union] using h2
      exact h.symm)
    hdisj₁.symm
    (by
      intro f u
      exact hseg₁ ⟨(f : Set (Fin n)), hL₁sub f.2⟩ ⟨(u : Set (Fin n)), hG₁sub u.2⟩ f.2 u.2)
    e
  have hpred : (precedingDegree Good₁ ordC e : ℝ) = (case2Pred₁ ord₁ Good₁ hG₁sub e : ℝ) := by
    rw [case2_pred₁_eq ord₁ hG₁sub ordC hrankC e]
  have hpred' : (Nat.card {f : Good₁ // f ≠ e ∧
        (ord₁ ⟨(f : Set (Fin n)), hG₁sub f.2⟩ : ℕ) ≤
          (ord₁ ⟨(e : Set (Fin n)), hG₁sub e.2⟩ : ℕ) ∧
        (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℝ) =
      (case2Pred₁ ord₁ Good₁ hG₁sub e : ℝ) := rfl
  have hfib' : ((Nat.card {f : Left₁ // (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) +
      (Nat.card {f : Good₁ // f ≠ e ∧
        (ord₁ ⟨(f : Set (Fin n)), hG₁sub f.2⟩ : ℕ) ≤
          (ord₁ ⟨(e : Set (Fin n)), hG₁sub e.2⟩ : ℕ) ∧
        (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℝ) ≤
      (precedingDegree (nonHuge 𝓗 β) ord₁ ⟨(e : Set (Fin n)), hG₁sub e.2⟩ : ℝ) := by
    exact_mod_cast hfib
  have hadd := natCard_interFiber_add_le (𝓖 := Left₁) (𝓖₁ := Good₂) (𝓖₂ := Left₂)
    hG₂sub hL₂sub hdisj₂ (e : Set (Fin n))
  have hadd' : ((Nat.card {f : Good₂ // (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) +
      ((Nat.card {f : Left₂ // (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) ≤
      (Nat.card {f : Left₁ // (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) := by
    exact_mod_cast hadd
  have hdeg := hdeg₁ ⟨(e : Set (Fin n)), hG₁sub e.2⟩ e.2
  rw [hpred, ← hpred']
  linarith [hfib', hdeg, hadd']

/-! ## Case 2.2: the list-size bounds -/

/-- **List bound for `φ₂`** (Claim `claim:bounded-colouring-extension2`):
with `α₁ = σ` the lists `case22List₂` are long against the forward degrees,
because `|C_huge| ≤ 32/β² ≤ σn` and the forbidden colours are at most the
`𝓗₂^left`-neighbours. -/
theorem case22_list_bound₂ {n : ℕ} {β σ : ℝ}
    {𝓗 Left₂ Good₂ : Hypergraph (Fin n)} [Fintype Left₂]
    {Chuge : Finset (Fin n)} {φ₁ : (case2HugeLeft₂ β 𝓗 Left₂).Coloring (Fin n)}
    {kB : ℕ} {ordB : Good₂ ≃ Fin kB}
    (hchuge : (Chuge.card : ℝ) ≤ 32 / β ^ 2)
    (hσn : 32 / β ^ 2 ≤ σ * (n : ℝ)) (hσ0 : 0 < σ)
    (hsum : ∀ e : Good₂,
      ((Nat.card {g : Left₂ // (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) +
        (precedingDegree Good₂ ordB e : ℝ) ≤ (1 - 3 * σ) * (n : ℝ)) :
    ∀ e : Good₂,
      (precedingDegree Good₂ ordB e : ℝ) + σ * (n : ℝ) ≤
        ((case22List₂ φ₁ Chuge (e : Set (Fin n))).card : ℝ) := by
  classical
  intro e
  have hforb := card_case22Forb₁_le φ₁ (e : Set (Fin n))
  have hF : ((case22Forb₁ φ₁ (e : Set (Fin n))).card : ℝ) ≤
      (Nat.card {g : Left₂ // (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℝ) := by
    exact_mod_cast hforb
  have huniv : ((Finset.univ : Finset (Fin n)).card : ℝ) = (n : ℝ) := by
    simp
  have h1 : (n : ℝ) - (Chuge.card : ℝ) ≤
      ((Finset.univ \ Chuge : Finset (Fin n)).card : ℝ) := by
    have h := card_sdiff_ge (Finset.univ : Finset (Fin n)) Chuge
    have h' : (((Finset.univ : Finset (Fin n)).card - Chuge.card : ℕ) : ℝ) ≤
        ((Finset.univ \ Chuge : Finset (Fin n)).card : ℝ) := by exact_mod_cast h
    rwa [Nat.cast_sub (Finset.card_le_card (Finset.subset_univ Chuge)), huniv] at h'
  have h2 : ((Finset.univ \ Chuge : Finset (Fin n)).card : ℝ) ≤
      ((case22List₂ φ₁ Chuge (e : Set (Fin n))).card : ℝ) +
        ((case22Forb₁ φ₁ (e : Set (Fin n))).card : ℝ) := by
    have h := card_le_card_sdiff_add ((Finset.univ \ Chuge : Finset (Fin n)))
      (case22Forb₁ φ₁ (e : Set (Fin n)))
    rw [case22List₂]
    exact_mod_cast h
  have hsum' := hsum e
  linarith [huniv, h1, h2, hF, hsum', hchuge, hσn]

/-- **List bound for `φ₃`** (Claim `claim:bounded-colouring-extension3`): with
`α₁ = γ₂/3` the lists `case22List₃` are long against the forward degrees,
because `|C_med| = ⌊γ₂n⌋ ≥ γ₂n − 1` and the forbidden colours are at most the
`𝓗₂^left`- plus `𝓗₂^good`-neighbours. -/
theorem case22_list_bound₃ {n : ℕ} {β γ₂ : ℝ}
    {𝓗 Left₂ Good₂ Good₁ : Hypergraph (Fin n)} [Fintype Left₂] [Fintype Good₂]
    {φ₁ : (case2HugeLeft₂ β 𝓗 Left₂).Coloring (Fin n)}
    {φ₂ : Good₂.Coloring (Fin n)} {Cmed : Finset (Fin n)}
    {kC : ℕ} {ordC : Good₁ ≃ Fin kC}
    (hCmed : γ₂ * (n : ℝ) - 1 ≤ (Cmed.card : ℝ))
    (hγ₂n : 1 ≤ (γ₂ / 3) * (n : ℝ))
    (hsum : ∀ e : Good₁,
      ((Nat.card {g : Left₂ // (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) +
        ((Nat.card {g : Good₂ // (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) +
        (precedingDegree Good₁ ordC e : ℝ) ≤ (γ₂ / 3) * (n : ℝ)) :
    ∀ e : Good₁,
      (precedingDegree Good₁ ordC e : ℝ) + (γ₂ / 3) * (n : ℝ) ≤
        ((case22List₃ φ₁ φ₂ Cmed (e : Set (Fin n))).card : ℝ) := by
  classical
  intro e
  have hF₁ : ((case22Forb₁ φ₁ (e : Set (Fin n))).card : ℝ) ≤
      (Nat.card {g : Left₂ // (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℝ) := by
    exact_mod_cast card_case22Forb₁_le φ₁ (e : Set (Fin n))
  have hF₂ : ((case22Forb₂ φ₂ (e : Set (Fin n))).card : ℝ) ≤
      (Nat.card {g : Good₂ // (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℝ) := by
    exact_mod_cast card_case22Forb₂_le φ₂ (e : Set (Fin n))
  have hFU : ((case22Forb₁ φ₁ (e : Set (Fin n)) ∪ case22Forb₂ φ₂ (e : Set (Fin n))).card : ℝ) ≤
      ((case22Forb₁ φ₁ (e : Set (Fin n))).card : ℝ) +
        ((case22Forb₂ φ₂ (e : Set (Fin n))).card : ℝ) := by
    have h := Finset.card_union_le (case22Forb₁ φ₁ (e : Set (Fin n)))
      (case22Forb₂ φ₂ (e : Set (Fin n)))
    exact_mod_cast h
  have h2 : (Cmed.card : ℝ) ≤
      ((case22List₃ φ₁ φ₂ Cmed (e : Set (Fin n))).card : ℝ) +
        ((case22Forb₁ φ₁ (e : Set (Fin n)) ∪ case22Forb₂ φ₂ (e : Set (Fin n))).card : ℝ) := by
    have h := card_le_card_sdiff_add Cmed
      (case22Forb₁ φ₁ (e : Set (Fin n)) ∪ case22Forb₂ φ₂ (e : Set (Fin n)))
    rw [case22List₃]
    exact_mod_cast h
  have hsum' := hsum e
  linarith [h2, hFU, hF₁, hF₂, hsum', hCmed, hγ₂n]

/-- **The Case-2.2 colour set `C_med`**: a set of `⌊γ₂n⌋` colours inside
`univ ∖ C_huge`, which exists because `|C_huge| ≤ 32/β²`. -/
theorem case22_exists_Cmed {β γ₂ : ℝ} {𝓗 A : Hypergraph (Fin n)} [Fintype A]
    {φ₁ : A.Coloring (Fin n)}
    (hroom : ⌊γ₂ * (n : ℝ)⌋₊ + (hugeColourSet 𝓗 A β φ₁).card ≤ n) :
    ∃ Cmed : Finset (Fin n), Cmed ⊆ Finset.univ \ hugeColourSet 𝓗 A β φ₁ ∧
      Cmed.card = ⌊γ₂ * (n : ℝ)⌋₊ := by
  classical
  have h1 : ⌊γ₂ * (n : ℝ)⌋₊ ≤ ((Finset.univ : Finset (Fin n)) \
      hugeColourSet 𝓗 A β φ₁).card := by
    have h := card_sdiff_ge (Finset.univ : Finset (Fin n)) (hugeColourSet 𝓗 A β φ₁)
    have h' : ((Finset.univ : Finset (Fin n)).card - (hugeColourSet 𝓗 A β φ₁).card) ≤
        ((Finset.univ : Finset (Fin n)) \ hugeColourSet 𝓗 A β φ₁).card := h
    have hcard : (Finset.univ : Finset (Fin n)).card = n := Finset.card_univ.trans
      (Fintype.card_fin n)
    rw [hcard] at h'
    omega
  obtain ⟨Cmed, hsub, hcard⟩ := Finset.exists_subset_card_eq h1
  exact ⟨Cmed, hsub, hcard⟩

/-! ## Case 2.2: colour-class estimates for the pieces -/

/-- The label of an edge in the first part of a cross-combined colouring. -/
theorem labels_coloringUnionCross_of_mem {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    {h₁ : 𝓖₁ ⊆ 𝓗} {h₂ : 𝓖₂ ⊆ 𝓗} {hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂}
    {hdisjG : Disjoint 𝓖₁ 𝓖₂} {φ₁ : 𝓖₁.Coloring (Fin n)} {φ₂ : 𝓖₂.Coloring (Fin n)}
    {hcross : ∀ (e₁ : 𝓖₁) (e₂ : 𝓖₂),
      (((e₁ : Set (Fin n)) ∩ (e₂ : Set (Fin n))).Nonempty) → φ₁.labels e₁ ≠ φ₂.labels e₂}
    (e : 𝓗) (he : (e : Set (Fin n)) ∈ 𝓖₁) :
    (coloringUnionCross h₁ h₂ hcover hdisjG φ₁ φ₂ hcross).labels e =
      φ₁.labels ⟨(e : Set (Fin n)), he⟩ := by
  simp only [coloringUnionCross, unionLabelCross, dif_pos he]

/-- The label of an edge in the second part of a cross-combined colouring. -/
theorem labels_coloringUnionCross_of_notMem {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    {h₁ : 𝓖₁ ⊆ 𝓗} {h₂ : 𝓖₂ ⊆ 𝓗} {hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂}
    {hdisjG : Disjoint 𝓖₁ 𝓖₂} {φ₁ : 𝓖₁.Coloring (Fin n)} {φ₂ : 𝓖₂.Coloring (Fin n)}
    {hcross : ∀ (e₁ : 𝓖₁) (e₂ : 𝓖₂),
      (((e₁ : Set (Fin n)) ∩ (e₂ : Set (Fin n))).Nonempty) → φ₁.labels e₁ ≠ φ₂.labels e₂}
    (e : 𝓗) (he : (e : Set (Fin n)) ∉ 𝓖₁) :
    (coloringUnionCross h₁ h₂ hcover hdisjG φ₁ φ₂ hcross).labels e =
      φ₂.labels ⟨(e : Set (Fin n)), (hcover (e : Set (Fin n)) e.2).resolve_left he⟩ := by
  simp only [coloringUnionCross, unionLabelCross, dif_neg he]

/-- A colour outside the colour set of a colouring has empty class. -/
theorem colorClass_eq_empty_of_notMem_usesColourSet {𝓖 : Hypergraph (Fin n)}
    {φ : 𝓖.Coloring (Fin n)} {C : Finset (Fin n)} (hφ : φ.UsesColourSet C) {c : Fin n}
    (hc : c ∉ C) : φ.colorClass c = ∅ := by
  ext e
  constructor
  · intro he
    rw [mem_colorClass] at he
    exact absurd (he ▸ hφ e) hc
  · intro he
    exact absurd he (Set.notMem_empty e)

/-- A class of a colouring all of whose edges are non-huge covers at most
`2 · βn/4 = βn/2` vertices (each class has at most two edges). -/
theorem case22_classVertexCount_le_of_notMem_hugeColour {β : ℝ}
    {𝓗 A : Hypergraph (Fin n)} [Fintype A] {φ : A.Coloring (Fin n)} (hβ : 0 < β)
    (hcls : ∀ c : Fin n, (φ.colorClass c).ncard ≤ 2) (hAsub : A ⊆ 𝓗) {c : Fin n}
    (hc : c ∉ hugeColourSet 𝓗 A β φ) :
    (φ.classVertexCount c : ℝ) ≤ 2 * (β * (n : ℝ) / 4) := by
  classical
  refine classVertexCount_le_of_ncard_le φ c (hcls c) (M := β * (n : ℝ) / 4) ?_ ?_
  · nlinarith [hβ, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  intro e he
  have hlab : φ.labels e = c := (mem_colorClass φ c e).mp he
  have hnot : (e : Set (Fin n)) ∉ 𝓗.hugeEdges β := by
    intro hmem
    exact hc (mem_hugeColourSet.mpr ⟨e, hmem, hlab⟩)
  have h2 : ¬ (β * (n : ℝ) / 4 ≤ (edgeSize (e : Set (Fin n)) : ℝ)) := by
    intro hle
    exact hnot ((mem_hugeEdges 𝓗 β (e : Set (Fin n))).mpr ⟨hAsub e.2, hle⟩)
  linarith [not_le.mp h2]

/-- A class of an `α`-bounded colouring whose edges all lie in the non-huge
part covers at most `βn/4` vertices (for `α = β/5`). -/
theorem case22_hcv₂_le {β : ℝ} {Good₂ : Hypergraph (Fin n)} {φ₂ : Good₂.Coloring (Fin n)}
    (hβ : 0 < β) (hφ₂b : φ₂.AlphaBounded (β / 5))
    (hM : ∀ e : Good₂, (edgeSize (e : Set (Fin n)) : ℝ) ≤ β * (n : ℝ) / 4) :
    ∀ c : Fin n, (φ₂.classVertexCount c : ℝ) ≤ β * (n : ℝ) / 4 := by
  intro c
  have h := classVertexCount_le_of_alphaBounded φ₂ hφ₂b
    (by positivity : (0 : ℝ) ≤ (β / 5) * (n : ℝ)) (c := c) (fun e _ => hM e)
  have hle : (β / 5) * (n : ℝ) ≤ β * (n : ℝ) / 4 := by
    nlinarith [hβ, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  linarith [(max_eq_right hle).le, h]


/-! ## Case 2.2: the extremal alternative -/

/-- **The colouring of Case 2.2.**  From the Figure-3 block decomposition of
Theorem 6.1 with `W₂ ≠ ∅` and `r₃ ≥ (1−δ)√n`, build the proper
edge-colouring of `𝓗` and the medium colour set `C_med` satisfying (i)–(iii)
of `LargeEdgeExtremal`. -/
theorem case22_colouring {n r₁ r₀ : ℕ} {β γ₂ σ δ γ₁ : ℝ} {n₀' : ℕ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂}
    {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hW₂ne : W₂ ≠ ∅)
    (hr₃lo : (1 - δ) * Real.sqrt (n : ℝ) ≤ (r₃ : ℝ))
    (hr₃up : (r₃ : ℝ) ≤ Real.sqrt ((n : ℝ) / (1 - 4 * σ)))
    (hfac : sizeFactor (3 * σ) 1 * Real.sqrt ((n : ℝ) / (1 - 4 * σ)) ≤
      (1 + δ) * Real.sqrt (n : ℝ))
    (hlin : 𝓗.IsLinear) (hn1 : 1 ≤ n) (h2n : 2 ≤ n) (hσn : 32 / β ^ 2 ≤ σ * (n : ℝ))
    (hβ : 0 < β) (hγ₂0 : 0 < γ₂) (hσ0 : 0 < σ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 16)
    (hγ₁0 : 0 < γ₁) (hβc : 8 ≤ β * (n : ℝ))
    (hδ2n : 8 ≤ δ ^ 2 * (n : ℝ))
    (hsmall : (1 + δ) * Real.sqrt (n : ℝ) ≤ δ * (n : ℝ) / 2)
    (hden : 0 < (n : ℝ) * ((n - 1 : ℕ) : ℝ))
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ))
    (h2r₀ : 2 ≤ r₀) (h2r₁ : 2 ≤ r₁) (hr₀ : 1 ≤ r₀)
    (hLN : ∀ m : ℕ, n₀' ≤ m → ∀ 𝓖 : Hypergraph (Fin m), 𝓖.IsLinear →
      (∀ e : Set (Fin m), e ∈ 𝓖 → (1 - δ) * Real.sqrt (m : ℝ) ≤ (edgeSize e : ℝ)) →
      ∃ φ : 𝓖.Coloring (Fin m), ∀ c : Fin m, (φ.colorClass c).ncard ≤ 2)
    (hn₀ : n₀' ≤ n)
    (hhuge : (1 - δ) * Real.sqrt (n : ℝ) ≤ β * (n : ℝ) / 4)
    (hroomNat : ⌊γ₂ * (n : ℝ)⌋₊ + ⌈32 / β ^ 2⌉₊ ≤ n)
    (h69m₂ : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < (σ * (n : ℝ)) / 4)
    (h69b₂ : (((bigFinset (β / 5) Good₂).card : ℕ) : ℝ) < σ * (n : ℝ) / 2)
    (h69m₃ : (2 : ℝ) * (n : ℝ) / ((γ₁ / 2) * ((r₁ : ℝ) - 1)) < ((γ₂ / 3) * (n : ℝ)) / 4)
    (h69b₃ : (((bigFinset (γ₁ / 2) Good₁).card : ℕ) : ℝ) < ((γ₂ / 3) * (n : ℝ)) / 2)
    (hγ₂n : 1 ≤ (γ₂ / 3) * (n : ℝ))
    (hr₂r₃ : γ₂ ^ 10 * (r₃ : ℝ) ≤ (r₂ : ℝ))
    (hr₀h : 2 * (r₀ : ℝ) ≤ γ₂ ^ 10 * (1 - δ) * Real.sqrt (n : ℝ))
    (hβn : (r₀ : ℝ) < β * (n : ℝ) / 4)
    (hβγ : 2 * (β * (n : ℝ) / 4) + β * (n : ℝ) / 4 + (γ₁ / 2) * (n : ℝ) ≤ γ₁ * (n : ℝ)) :
    ∃ (φ : 𝓗.Coloring (Fin n)) (Cmed : Finset (Fin n)),
      (Cmed.card : ℝ) ≤ γ₂ * (n : ℝ) ∧
      (∀ e : 𝓗, edgeMedium r₁ r₀ (e : Set (Fin n)) → φ.labels e ∈ Cmed) ∧
      (∀ c ∈ Cmed, (φ.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ)) ∧
      (∀ c : Fin n, φ.AssignedToHuge β c → (φ.classVertexCount c : ℝ) ≤ δ * (n : ℝ)) ∧
      (∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c →
        (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ)) := by
  classical
  haveI hL₂fin : Fintype Left₂ := Fintype.ofFinite Left₂
  haveI hG₂fin : Fintype Good₂ := Fintype.ofFinite Good₂
  haveI hG₁fin : Fintype Good₁ := Fintype.ofFinite Good₁
  haveI hAfin : Fintype (case2HugeLeft₂ β 𝓗 Left₂) := Fintype.ofFinite _
  have hL₂𝓗 : Left₂ ⊆ 𝓗 := fun e he => nonHuge_subset 𝓗 β (hB.hL₁sub (hB.hL₂sub he))
  have hAsub : case2HugeLeft₂ β 𝓗 Left₂ ⊆ 𝓗 := case22_hugeLeft_subset hL₂𝓗
  have hGsub : Good₂ ⊆ 𝓗 := fun e he => nonHuge_subset 𝓗 β (hB.hL₁sub (hB.hG₂sub he))
  have hCsub : Good₁ ⊆ 𝓗 := fun e he => nonHuge_subset 𝓗 β (hB.hG₁sub he)
  -- Step 1: no edge has size at least `δn/2`
  have hNoBig : ∀ e : Set (Fin n), e ∈ 𝓗 → (edgeSize e : ℝ) ≤ δ * (n : ℝ) / 2 :=
    case22_noBig (r₁ := r₁) (r₀ := r₀) hB hW₂ne hr₃up hfac hlin hδ0 hδ1 hn1 hδ2n hsmall hden
  have hNoBigA : ∀ e : case2HugeLeft₂ β 𝓗 Left₂, (edgeSize (e : Set (Fin n)) : ℝ) ≤
      δ * (n : ℝ) / 2 := fun e => hNoBig _ (hAsub e.2)
  -- Step 2: the Lemma 5.1 colouring of the left block
  obtain ⟨φ₁, hcls₁⟩ :=
    case22_left_colouring (δ := δ) (n₀ := n₀') hLN hn₀ hlin hL₂𝓗
      (fun e he => hB.hsize₂ ⟨e, hB.hL₂sub he⟩ he) hr₃lo hhuge
  have hcv₁ : ∀ c : Fin n, (φ₁.classVertexCount c : ℝ) ≤ δ * (n : ℝ) :=
    case22_classVertexCount_le φ₁ hcls₁ hδ0 hNoBigA
  -- Step 3: the colour sets `C_huge` and `C_med`
  have hchuge : (((hugeColourSet 𝓗 (case2HugeLeft₂ β 𝓗 Left₂) β φ₁).card : ℕ) : ℝ) ≤
      32 / β ^ 2 := card_hugeColours_le φ₁ hlin hβ hβc hn1
  have hCmedroom : ⌊γ₂ * (n : ℝ)⌋₊ +
      (hugeColourSet 𝓗 (case2HugeLeft₂ β 𝓗 Left₂) β φ₁).card ≤ n := by
    have h1 : ((hugeColourSet 𝓗 (case2HugeLeft₂ β 𝓗 Left₂) β φ₁).card : ℝ) ≤
        ((⌈32 / β ^ 2⌉₊ : ℕ) : ℝ) := le_trans hchuge (Nat.le_ceil _)
    have h2 : (hugeColourSet 𝓗 (case2HugeLeft₂ β 𝓗 Left₂) β φ₁).card ≤ ⌈32 / β ^ 2⌉₊ := by
      exact_mod_cast h1
    omega
  obtain ⟨C_med, hCmedsub, hCmedcard⟩ :=
    case22_exists_Cmed (β := β) (γ₂ := γ₂) (𝓗 := 𝓗) (A := case2HugeLeft₂ β 𝓗 Left₂) (φ₁ := φ₁)
      hCmedroom
  have hCmed_le : (C_med.card : ℝ) ≤ γ₂ * (n : ℝ) := by
    rw [hCmedcard]; exact Nat.floor_le (by positivity)
  have hCmed_ge : γ₂ * (n : ℝ) - 1 ≤ (C_med.card : ℝ) := by
    rw [hCmedcard]
    have := Nat.lt_floor_add_one (γ₂ * (n : ℝ))
    linarith
  have hCmed_nothuge : ∀ c : Fin n, c ∈ C_med →
      c ∉ hugeColourSet 𝓗 (case2HugeLeft₂ β 𝓗 Left₂) β φ₁ :=
    fun c hc hc' => (Finset.mem_sdiff.mp (hCmedsub hc)).2 hc'
  -- Step 4: restricted orderings of the two good blocks
  obtain ⟨kB, ordB, hrankB, _⟩ := exists_restricted_ordering (𝓖 := Left₁) ord₂ (𝓖' := Good₂) hB.hG₂sub
  obtain ⟨kC, ordC, hrankC, _⟩ :=
    exists_restricted_ordering (𝓖 := nonHuge 𝓗 β) ord₁ (𝓖' := Good₁) hB.hG₁sub
  -- Step 5: Proposition 6.9 on `𝓗₂^good`
  have hlinB : Good₂.IsLinear := hlin.mono hGsub
  have hsizeB : ∀ e : Good₂, r₀ ≤ edgeSize (e : Set (Fin n)) := by
    intro e
    have h := hB.hsize₁ ⟨(e : Set (Fin n)), hB.hL₁sub (hB.hG₂sub e.2)⟩ (hB.hG₂sub e.2)
    have h2 : r₀ ≤ r₂ := le_of_lt (r₀_lt_r₂_of_blocks hB hr₂r₃ hr₀h hγ₂0 h2r₀ hr₃lo)
    exact le_trans h2 h
  have hsum₂ := case22_fwddeg_good₂ ord₂ hB.hL₂sub hB.hG₂sub hB.hpart₂ hB.hdisj₂ hB.hseg₂
    ordB hrankB hB.hdeg₂
  obtain ⟨φ₂, hφ₂b, hφ₂list⟩ :=
    prop69_colouring (n := n) (r := r₀) (k := kB) (α₁ := σ) (α₂ := β / 5) (𝓗 := Good₂)
      h2n h2r₀ (by positivity) h69m₂ h69b₂ hlinB hsizeB ordB
      (fun e : Good₂ => case22List₂ φ₁
        (hugeColourSet 𝓗 (case2HugeLeft₂ β 𝓗 Left₂) β φ₁) (e : Set (Fin n)))
      (fun e => case22_list_bound₂ (Chuge := hugeColourSet 𝓗 (case2HugeLeft₂ β 𝓗 Left₂) β φ₁)
        hchuge hσn hσ0 hsum₂ e)
  -- Step 6: Proposition 6.9 on `𝓗₁^good`
  have hlinC : Good₁.IsLinear := hlin.mono hCsub
  have hsizeC : ∀ e : Good₁, r₁ ≤ edgeSize (e : Set (Fin n)) := by
    intro e
    have h := hsize ⟨(e : Set (Fin n)), hCsub e.2⟩
    exact_mod_cast (le_of_lt h)
  have hsum₃ := case22_fwddeg_good₁ ord₁ hB.hL₁sub hB.hG₁sub hB.hpart₁ hB.hdisj₁ hB.hseg₁
    hB.hG₂sub hB.hL₂sub hB.hdisj₂ ordC hrankC hB.hdeg₁
  obtain ⟨φ₃, hφ₃b, hφ₃list⟩ :=
    prop69_colouring (n := n) (r := r₁) (k := kC) (α₁ := γ₂ / 3) (α₂ := γ₁ / 2) (𝓗 := Good₁)
      h2n h2r₁ (by positivity) h69m₃ h69b₃ hlinC hsizeC ordC
      (fun e : Good₁ => case22List₃ φ₁ φ₂ C_med (e : Set (Fin n)))
      (fun e => case22_list_bound₃ (Cmed := C_med) hCmed_ge hγ₂n hsum₃ e)
  -- Step 7: the cross-conditions and the combined colouring
  have hdisjAB : Disjoint (case2HugeLeft₂ β 𝓗 Left₂) Good₂ := case22_disjoint_hugeLeft_good₂ hB
  have hcoverAB : ∀ e ∈ (case2HugeLeft₂ β 𝓗 Left₂ ∪ Good₂ : Hypergraph (Fin n)),
      e ∈ case2HugeLeft₂ β 𝓗 Left₂ ∨ e ∈ Good₂ := fun _ he => he
  have hcrossAB : ∀ (e₁ : case2HugeLeft₂ β 𝓗 Left₂) (e₂ : Good₂),
      (((e₁ : Set (Fin n)) ∩ (e₂ : Set (Fin n))).Nonempty) → φ₁.labels e₁ ≠ φ₂.labels e₂ := by
    intro e₁ e₂ hne
    have hkey : (e₁ : Set (Fin n)) ∈ 𝓗.hugeEdges β ∨ (e₁ : Set (Fin n)) ∈ Left₂ := e₁.2
    rcases hkey with hhm | hL₂
    · intro hEq
      have hCh : φ₁.labels e₁ ∈ hugeColourSet 𝓗 (case2HugeLeft₂ β 𝓗 Left₂) β φ₁ :=
        mem_hugeColourSet.mpr ⟨e₁, hhm, rfl⟩
      exact ((mem_case22List₂.mp (hφ₂list e₂)).1.2) (hEq ▸ hCh)
    · intro hEq
      have hforb : φ₁.labels e₁ ∈ case22Forb₁ φ₁ (e₂ : Set (Fin n)) :=
        mem_case22Forb₁.mpr ⟨⟨(e₁ : Set (Fin n)), hL₂⟩, hne, rfl⟩
      exact ((mem_case22List₂.mp (hφ₂list e₂)).2) (hEq ▸ hforb)
  let φAB : (case2HugeLeft₂ β 𝓗 Left₂ ∪ Good₂ : Hypergraph (Fin n)).Coloring (Fin n) :=
    coloringUnionCross Set.subset_union_left Set.subset_union_right hcoverAB hdisjAB
      φ₁ φ₂ hcrossAB
  have hAsubAB : (case2HugeLeft₂ β 𝓗 Left₂ ∪ Good₂ : Hypergraph (Fin n)) ⊆ 𝓗 :=
    Set.union_subset hAsub hGsub
  have hdisjABC : Disjoint (case2HugeLeft₂ β 𝓗 Left₂ ∪ Good₂ : Hypergraph (Fin n)) Good₁ := by
    rw [Set.disjoint_left]
    rintro e (he | he) hG₁
    · exact (Set.disjoint_left.mp (case22_disjoint_hugeLeft_good₁ hB)) he hG₁
    · exact (Set.disjoint_left.mp hB.hdisjG₂G₁) he hG₁
  have hcoverABC : ∀ e ∈ 𝓗,
      e ∈ (case2HugeLeft₂ β 𝓗 Left₂ ∪ Good₂ : Hypergraph (Fin n)) ∨ e ∈ Good₁ := by
    intro e he
    have h : e ∈ (case2HugeLeft₂ β 𝓗 Left₂ ∪ Good₂) ∪ Good₁ := by
      rw [case22_cover hB]; exact he
    simpa only [Set.mem_union] using h
  have hcrossC : ∀ (e₁ : (case2HugeLeft₂ β 𝓗 Left₂ ∪ Good₂ : Hypergraph (Fin n))) (e₂ : Good₁),
      (((e₁ : Set (Fin n)) ∩ (e₂ : Set (Fin n))).Nonempty) → φAB.labels e₁ ≠ φ₃.labels e₂ := by
    intro e₁ e₂ hne
    by_cases hA : (e₁ : Set (Fin n)) ∈ case2HugeLeft₂ β 𝓗 Left₂
    · have hlab := labels_coloringUnionCross_of_mem (h₁ := Set.subset_union_left)
        (h₂ := Set.subset_union_right) (hcover := hcoverAB) (hdisjG := hdisjAB)
        (φ₁ := φ₁) (φ₂ := φ₂) (hcross := hcrossAB) e₁ hA
      rw [hlab]
      intro hEq
      have hkey : (e₁ : Set (Fin n)) ∈ 𝓗.hugeEdges β ∨ (e₁ : Set (Fin n)) ∈ Left₂ := hA
      rcases hkey with hhm | hL₂
      · have hCh : φ₁.labels ⟨(e₁ : Set (Fin n)), hA⟩ ∈
            hugeColourSet 𝓗 (case2HugeLeft₂ β 𝓗 Left₂) β φ₁ :=
          mem_hugeColourSet.mpr ⟨⟨(e₁ : Set (Fin n)), hA⟩, hhm, rfl⟩
        have h2 : φ₃.labels e₂ ∈ C_med := (mem_case22List₃.mp (hφ₃list e₂)).1
        have h3 : φ₃.labels e₂ ∉ hugeColourSet 𝓗 (case2HugeLeft₂ β 𝓗 Left₂) β φ₁ :=
          (Finset.mem_sdiff.mp (hCmedsub h2)).2
        exact h3 (hEq ▸ hCh)
      · have hforb : φ₁.labels ⟨(e₁ : Set (Fin n)), hA⟩ ∈ case22Forb₁ φ₁ (e₂ : Set (Fin n)) := by
          have h0 : φ₁.labels ⟨(e₁ : Set (Fin n)), Or.inr hL₂⟩ ∈
              case22Forb₁ φ₁ (e₂ : Set (Fin n)) :=
            mem_case22Forb₁.mpr ⟨⟨(e₁ : Set (Fin n)), hL₂⟩, hne, rfl⟩
          have heq : (⟨(e₁ : Set (Fin n)), Or.inr hL₂⟩ :
              case2HugeLeft₂ β 𝓗 Left₂) = ⟨(e₁ : Set (Fin n)), hA⟩ := Subtype.ext rfl
          rwa [heq] at h0
        have h2 : φ₃.labels e₂ ∉ case22Forb₁ φ₁ (e₂ : Set (Fin n)) :=
          (mem_case22List₃.mp (hφ₃list e₂)).2.1
        exact h2 (hEq ▸ hforb)
    · have hG₂ : (e₁ : Set (Fin n)) ∈ Good₂ := (hcoverAB _ e₁.2).resolve_left hA
      have hlab : φAB.labels e₁ = φ₂.labels ⟨(e₁ : Set (Fin n)), hG₂⟩ := by
        have h := labels_coloringUnionCross_of_notMem (h₁ := Set.subset_union_left)
          (h₂ := Set.subset_union_right) (hcover := hcoverAB) (hdisjG := hdisjAB)
          (φ₁ := φ₁) (φ₂ := φ₂) (hcross := hcrossAB) e₁ hA
        have heq : (⟨(e₁ : Set (Fin n)),
            (hcoverAB (e₁ : Set (Fin n)) e₁.2).resolve_left hA⟩ : Good₂) =
            ⟨(e₁ : Set (Fin n)), hG₂⟩ := Subtype.ext rfl
        rw [h, heq]
      rw [hlab]
      intro hEq
      have hforb : φ₂.labels ⟨(e₁ : Set (Fin n)), hG₂⟩ ∈ case22Forb₂ φ₂ (e₂ : Set (Fin n)) :=
        mem_case22Forb₂.mpr ⟨⟨(e₁ : Set (Fin n)), hG₂⟩, hne, rfl⟩
      have h2 : φ₃.labels e₂ ∉ case22Forb₂ φ₂ (e₂ : Set (Fin n)) :=
        (mem_case22List₃.mp (hφ₃list e₂)).2.2
      exact h2 (hEq ▸ hforb)
  let φ : 𝓗.Coloring (Fin n) :=
    coloringUnionCross hAsubAB hCsub hcoverABC hdisjABC φAB φ₃ hcrossC
  -- Step 8: the colour-class estimates
  have hvcAB : ∀ c : Fin n, (φAB.classVertexCount c : ℝ) ≤
      (φ₁.classVertexCount c : ℝ) + (φ₂.classVertexCount c : ℝ) := fun c => by
    have h := classVertexCount_coloringUnionCross_le (h₁ := Set.subset_union_left)
      (h₂ := Set.subset_union_right) (hcover := hcoverAB) (hdisjG := hdisjAB)
      (φ₁ := φ₁) (φ₂ := φ₂) (hcross := hcrossAB) c
    exact_mod_cast h
  have hvc : ∀ c : Fin n, (φ.classVertexCount c : ℝ) ≤
      (φ₁.classVertexCount c : ℝ) + (φ₂.classVertexCount c : ℝ) +
        (φ₃.classVertexCount c : ℝ) := fun c => by
    have h := classVertexCount_coloringUnionCross_le (h₁ := hAsubAB) (h₂ := hCsub)
      (hcover := hcoverABC) (hdisjG := hdisjABC) (φ₁ := φAB) (φ₂ := φ₃) (hcross := hcrossC) c
    have h2 := hvcAB c
    have h3 : (φ.classVertexCount c : ℝ) ≤
        (φAB.classVertexCount c : ℝ) + (φ₃.classVertexCount c : ℝ) := by exact_mod_cast h
    linarith
  have hcv₂ : ∀ c : Fin n, (φ₂.classVertexCount c : ℝ) ≤ β * (n : ℝ) / 4 :=
    case22_hcv₂_le hβ hφ₂b (fun e => le_of_lt (not_le.mp (hB.hL₁sub (hB.hG₂sub e.2)).2))
  have hcv₃zero : ∀ c : Fin n, c ∉ C_med → φ₃.classVertexCount c = 0 := fun c hc => by
    have hempty : φ₃.colorClass c = ∅ :=
      colorClass_eq_empty_of_notMem_usesColourSet
        (fun e => (mem_case22List₃.mp (hφ₃list e)).1) hc
    exact classVertexCount_eq_zero_of_classVertices_eq_empty φ₃
      (classVertices_eq_empty_of_colorClass_eq_empty φ₃ hempty)
  have hφ₁nh : ∀ c : Fin n, c ∉ hugeColourSet 𝓗 (case2HugeLeft₂ β 𝓗 Left₂) β φ₁ →
      (φ₁.classVertexCount c : ℝ) ≤ 2 * (β * (n : ℝ) / 4) :=
    fun c hc => case22_classVertexCount_le_of_notMem_hugeColour hβ hcls₁ hAsub hc
  have hφ₁big : ∀ c : Fin n, (φ₁.classVertexCount c : ℝ) ≤ δ * (n : ℝ) := hcv₁
  -- Step 9: the four properties
  have hlabA : ∀ (e : 𝓗) (heA : (e : Set (Fin n)) ∈ case2HugeLeft₂ β 𝓗 Left₂),
      φ.labels e = φ₁.labels ⟨(e : Set (Fin n)), heA⟩ := by
    intro e heA
    have h3 : (e : Set (Fin n)) ∈ (case2HugeLeft₂ β 𝓗 Left₂ ∪ Good₂ : Hypergraph (Fin n)) :=
      Or.inl heA
    have h := labels_coloringUnionCross_of_mem (h₁ := hAsubAB) (h₂ := hCsub)
      (hcover := hcoverABC) (hdisjG := hdisjABC) (φ₁ := φAB) (φ₂ := φ₃) (hcross := hcrossC)
      e h3
    have h4 := labels_coloringUnionCross_of_mem (h₁ := Set.subset_union_left)
      (h₂ := Set.subset_union_right) (hcover := hcoverAB) (hdisjG := hdisjAB)
      (φ₁ := φ₁) (φ₂ := φ₂) (hcross := hcrossAB)
      (⟨(e : Set (Fin n)), h3⟩ : (case2HugeLeft₂ β 𝓗 Left₂ ∪ Good₂ : Hypergraph (Fin n))) heA
    exact h.trans (h4.trans (congrArg φ₁.labels (Subtype.ext rfl)))
  have hmemA : ∀ e : 𝓗, β * (n : ℝ) / 4 ≤ (edgeSize (e : Set (Fin n)) : ℝ) →
      (e : Set (Fin n)) ∈ case2HugeLeft₂ β 𝓗 Left₂ := by
    intro e hebig
    have h2 : (e : Set (Fin n)) ∈ (case2HugeLeft₂ β 𝓗 Left₂ ∪ Good₂) ∪ Good₁ := by
      rw [case22_cover hB]; exact e.2
    rw [Set.mem_union] at h2
    rcases h2 with h2 | hG₁
    · rw [Set.mem_union] at h2
      rcases h2 with h2 | hG₂
      · exact h2
      · exact absurd hebig (hB.hL₁sub (hB.hG₂sub hG₂)).2
    · exact absurd hebig (hB.hG₁sub hG₁).2
  have hbig_to_huge : ∀ c : Fin n, φ.AssignedToHuge β c →
      c ∈ hugeColourSet 𝓗 (case2HugeLeft₂ β 𝓗 Left₂) β φ₁ := by
    intro c hc
    obtain ⟨e, hecl, hebig⟩ := hc
    rw [mem_colorClass] at hecl
    have heA := hmemA e hebig
    exact mem_hugeColourSet.mpr ⟨⟨(e : Set (Fin n)), heA⟩,
      (mem_hugeEdges 𝓗 β (e : Set (Fin n))).mpr ⟨e.2, hebig⟩,
      (hlabA e heA).symm.trans hecl⟩
  have huge_to_big : ∀ c : Fin n,
      c ∈ hugeColourSet 𝓗 (case2HugeLeft₂ β 𝓗 Left₂) β φ₁ → φ.AssignedToHuge β c := by
    intro c hc
    obtain ⟨e, hmem, hlab⟩ := mem_hugeColourSet.mp hc
    refine ⟨⟨(e : Set (Fin n)), hAsub e.2⟩, ?_, hmem.2⟩
    rw [mem_colorClass]
    exact (hlabA ⟨(e : Set (Fin n)), hAsub e.2⟩ e.2).trans hlab
  have hprop_i : ∀ c : Fin n, φ.AssignedToHuge β c →
      (φ.classVertexCount c : ℝ) ≤ δ * (n : ℝ) := by
    intro c hc
    have hCh := hbig_to_huge c hc
    have h₂z : φ₂.classVertexCount c = 0 := by
      have hempty : φ₂.colorClass c = ∅ :=
        colorClass_eq_empty_of_notMem_usesColourSet
          (C := Finset.univ \ hugeColourSet 𝓗 (case2HugeLeft₂ β 𝓗 Left₂) β φ₁)
          (fun e => by
            have h := (mem_case22List₂.mp (hφ₂list e)).1
            exact Finset.mem_sdiff.mpr h)
          (fun hc' => (Finset.mem_sdiff.mp hc').2 hCh)
      exact classVertexCount_eq_zero_of_classVertices_eq_empty φ₂
        (classVertices_eq_empty_of_colorClass_eq_empty φ₂ hempty)
    have h₃z : φ₃.classVertexCount c = 0 := hcv₃zero c (fun hcm => (hCmed_nothuge c hcm) hCh)
    have h := hvc c
    have h₁ := hcv₁ c
    rw [h₂z, h₃z] at h
    push_cast at h
    linarith
  have hprop_ii : ∀ c ∈ C_med, (φ.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ) := by
    intro c hc
    have h₁ := hφ₁nh c (hCmed_nothuge c hc)
    have h₂ := hcv₂ c
    have h₃ := classVertexCount_le_of_alphaBounded φ₃ hφ₃b
      (by positivity : (0 : ℝ) ≤ (γ₁ / 2) * (n : ℝ)) (c := c)
      (fun e _ => le_of_lt (not_le.mp (hB.hG₁sub e.2).2))
    have hmax : max ((γ₁ / 2) * (n : ℝ)) (β * (n : ℝ) / 4) = (γ₁ / 2) * (n : ℝ) := by
      refine max_eq_left ?_
      nlinarith [hβ, hγ₁0, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)), hβγ]
    have h₃' : (φ₃.classVertexCount c : ℝ) ≤ (γ₁ / 2) * (n : ℝ) := by
      rw [hmax] at h₃; exact h₃
    have h := hvc c
    linarith
  have hprop_iii : ∀ c : Fin n, c ∉ C_med → ¬ φ.AssignedToHuge β c →
      (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ) := by
    intro c hcmed hnot
    have h₃z := hcv₃zero c hcmed
    have h₁ : (φ₁.classVertexCount c : ℝ) ≤ 2 * (β * (n : ℝ) / 4) :=
      hφ₁nh c (fun hCh => hnot (huge_to_big c hCh))
    have h₂ := hcv₂ c
    have h := hvc c
    rw [h₃z] at h
    push_cast at h
    linarith
  have hprop_med : ∀ e : 𝓗, edgeMedium r₁ r₀ (e : Set (Fin n)) → φ.labels e ∈ C_med := by
    intro e he
    obtain ⟨h1, h2⟩ := he
    have h1' : r₁ < edgeSize (e : Set (Fin n)) := by exact_mod_cast h1
    have h2' : edgeSize (e : Set (Fin n)) ≤ r₀ := by exact_mod_cast h2
    have hmed : (e : Set (Fin n)) ∈ 𝓗.medEdges r₁ r₀ :=
      (mem_medEdges 𝓗 r₁ r₀ _).mpr ⟨e.2, h1', h2'⟩
    have hr₀r₂ := r₀_lt_r₂_of_blocks hB hr₂r₃ hr₀h hγ₂0 h2r₀ hr₃lo
    have hG₁ : (e : Set (Fin n)) ∈ Good₁ := medEdges_subset_good₁ hB hβn hr₀r₂ hmed
    have hnotA : (e : Set (Fin n)) ∉ (case2HugeLeft₂ β 𝓗 Left₂ ∪ Good₂ : Hypergraph (Fin n)) := by
      intro hc
      rw [Set.mem_union] at hc
      rcases hc with hc | hc
      · exact (Set.disjoint_left.mp (case22_disjoint_hugeLeft_good₁ hB)) hc hG₁
      · exact (Set.disjoint_left.mp hB.hdisjG₂G₁) hc hG₁
    have h := labels_coloringUnionCross_of_notMem (h₁ := hAsubAB) (h₂ := hCsub)
      (hcover := hcoverABC) (hdisjG := hdisjABC) (φ₁ := φAB) (φ₂ := φ₃) (hcross := hcrossC)
      e hnotA
    rw [h]
    have h0 := (mem_case22List₃.mp (hφ₃list ⟨(e : Set (Fin n)), hG₁⟩)).1
    have heq : (⟨(e : Set (Fin n)),
        (hcoverABC (e : Set (Fin n)) e.2).resolve_left hnotA⟩ : Good₁) =
        ⟨(e : Set (Fin n)), hG₁⟩ := Subtype.ext rfl
    rwa [heq] at h0
  exact ⟨φ, C_med, hCmed_le, hprop_med, hprop_ii, hprop_i, hprop_iii⟩

/-- **Case 2.2 of Theorem 6.1** (`W₂ ≠ ∅` and `r₃ ≥ (1−δ)√n`): the
FPP-extremal alternative.  The extremal witness is the App-2 volume set `W₂`
and the colouring (with properties (i)–(iii)) is `case22_colouring`. -/
theorem case22_extremal {n r₁ r₀ : ℕ} {β γ₂ σ δ γ₁ : ℝ} {n₀' : ℕ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂}
    {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hW₂ne : W₂ ≠ ∅)
    (hr₃lo : (1 - δ) * Real.sqrt (n : ℝ) ≤ (r₃ : ℝ))
    (hr₃up : (r₃ : ℝ) ≤ Real.sqrt ((n : ℝ) / (1 - 4 * σ)))
    (hfac : sizeFactor (3 * σ) 1 * Real.sqrt ((n : ℝ) / (1 - 4 * σ)) ≤
      (1 + δ) * Real.sqrt (n : ℝ))
    (hlin : 𝓗.IsLinear) (hn1 : 1 ≤ n) (h2n : 2 ≤ n) (hσn : 32 / β ^ 2 ≤ σ * (n : ℝ))
    (hβ : 0 < β) (hγ₂0 : 0 < γ₂) (hσ0 : 0 < σ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 16)
    (hγ₁0 : 0 < γ₁) (hβc : 8 ≤ β * (n : ℝ))
    (hδ2n : 8 ≤ δ ^ 2 * (n : ℝ))
    (hsmall : (1 + δ) * Real.sqrt (n : ℝ) ≤ δ * (n : ℝ) / 2)
    (hden : 0 < (n : ℝ) * ((n - 1 : ℕ) : ℝ))
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ))
    (h2r₀ : 2 ≤ r₀) (h2r₁ : 2 ≤ r₁) (hr₀ : 1 ≤ r₀)
    (hLN : ∀ m : ℕ, n₀' ≤ m → ∀ 𝓖 : Hypergraph (Fin m), 𝓖.IsLinear →
      (∀ e : Set (Fin m), e ∈ 𝓖 → (1 - δ) * Real.sqrt (m : ℝ) ≤ (edgeSize e : ℝ)) →
      ∃ φ : 𝓖.Coloring (Fin m), ∀ c : Fin m, (φ.colorClass c).ncard ≤ 2)
    (hn₀ : n₀' ≤ n)
    (hhuge : (1 - δ) * Real.sqrt (n : ℝ) ≤ β * (n : ℝ) / 4)
    (hroomNat : ⌊γ₂ * (n : ℝ)⌋₊ + ⌈32 / β ^ 2⌉₊ ≤ n)
    (h69m₂ : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < (σ * (n : ℝ)) / 4)
    (h69b₂ : (((bigFinset (β / 5) Good₂).card : ℕ) : ℝ) < σ * (n : ℝ) / 2)
    (h69m₃ : (2 : ℝ) * (n : ℝ) / ((γ₁ / 2) * ((r₁ : ℝ) - 1)) < ((γ₂ / 3) * (n : ℝ)) / 4)
    (h69b₃ : (((bigFinset (γ₁ / 2) Good₁).card : ℕ) : ℝ) < ((γ₂ / 3) * (n : ℝ)) / 2)
    (hγ₂n : 1 ≤ (γ₂ / 3) * (n : ℝ))
    (hr₂r₃ : γ₂ ^ 10 * (r₃ : ℝ) ≤ (r₂ : ℝ))
    (hr₀h : 2 * (r₀ : ℝ) ≤ γ₂ ^ 10 * (1 - δ) * Real.sqrt (n : ℝ))
    (hβn : (r₀ : ℝ) < β * (n : ℝ) / 4)
    (hβγ : 2 * (β * (n : ℝ) / 4) + β * (n : ℝ) / 4 + (γ₁ / 2) * (n : ℝ) ≤ γ₁ * (n : ℝ)) :
    LargeEdgeExtremal n δ γ₂ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 := by
  obtain ⟨φ, C_med, h1, h2, h3, h4, h5⟩ :=
    case22_colouring (n := n) (r₁ := r₁) (r₀ := r₀) (n₀' := n₀') hB hW₂ne hr₃lo hr₃up hfac
      hlin hn1 h2n hσn hβ hγ₂0 hσ0 hδ0 hδ1 hγ₁0 hβc hδ2n hsmall hden hsize h2r₀ h2r₁ hr₀
      hLN hn₀ hhuge hroomNat h69m₂ h69b₂ h69m₃ h69b₃ hγ₂n hr₂r₃ hr₀h hβn hβγ
  exact ⟨extremal_witness_of_blocks hB hW₂ne hr₃lo hr₃up hfac hδ0
    (le_trans hδ1 (by norm_num)), φ, C_med, h1, h2, h3, h4, h5⟩


/-! ## Theorem 6.1: the case split with Case 2.2 discharged

`largeEdge_of_blocks_full` is the case split `largeEdge_of_blocks` of
`LargeEdgeCases.lean` with the Case-2.2 obligation `h22` supplied by
`case22_extremal`; the additional numeric hypotheses are the Case-2.2
`≪`-hierarchy obligations (see the Roadmap). -/

/-- **If `r₃ > √(n/(1−4σ))` then the App-2 left part is small.**  The pair
count `e(𝓗₂^left)·C(r₃,2) ≤ C(n,2)` (from `vol ≤ 1` and `(d3)`) and
`r₃ > √(n/(1−4σ))` give `e(𝓗₂^left) ≤ (1−3σ)n`, so the App-2 ordering is in
fact *good* — the case `⪯₂` good of the figure-3 analysis. -/
theorem case22_left_card_le {n r₃ : ℕ} {σ : ℝ} {Left₂ : Hypergraph (Fin n)}
    [Fintype Left₂] (hlin : Left₂.IsLinear) (h2n : 2 ≤ n) (hr₃ : 2 ≤ r₃)
    (hσ0 : 0 < σ) (hσ4 : 4 * σ ≤ 1 / 2) (hσ1 : 1 ≤ σ * (n : ℝ))
    (hsize₂ : ∀ e : Left₂, r₃ ≤ edgeSize (e : Set (Fin n)))
    (hup : Real.sqrt ((n : ℝ) / (1 - 4 * σ)) < (r₃ : ℝ))
    (hbig : 8 / σ ^ 2 ≤ (1 - 3 * σ) * (n : ℝ)) :
    (Nat.card Left₂ : ℝ) ≤ (1 - 3 * σ) * (n : ℝ) := by
  classical
  have h4σ : (0 : ℝ) < 1 - 4 * σ := by linarith
  have h3σ : (0 : ℝ) < 1 - 3 * σ := by linarith
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2n
  have hR2 : (2 : ℝ) ≤ (r₃ : ℝ) := by exact_mod_cast hr₃
  have hRpos : (0 : ℝ) < (r₃ : ℝ) := by linarith
  have hRsub : ((r₃ - 1 : ℕ) : ℝ) = (r₃ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r₃), Nat.cast_one]
  have hnsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  -- the pair count
  have hpair := card_edges_size_ge_mul_le (𝓗 := Left₂) hlin r₃
  have hfilter : (Finset.univ.filter
      (fun e : Left₂ => r₃ ≤ edgeSize (e : Set (Fin n)))).card
      = (Finset.univ : Finset Left₂).card :=
    congrArg Finset.card (Finset.filter_true_of_mem (fun e _ => hsize₂ e))
  rw [hfilter, Finset.card_univ] at hpair
  set k : ℕ := Nat.card Left₂ with hk
  have hkcard : k = Fintype.card Left₂ := by rw [hk, Nat.card_eq_fintype_card]
  have hpair' : (k : ℝ) * ((r₃ : ℝ) * ((r₃ : ℝ) - 1)) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    have h2 : ((k * (r₃ * (r₃ - 1)) : ℕ) : ℝ) ≤ ((n * (n - 1) : ℕ) : ℝ) := by
      rw [hkcard]
      exact_mod_cast hpair
    push_cast at h2
    rw [hRsub, hnsub] at h2
    exact h2
  by_cases hcase : (σ * (n : ℝ)) / 2 ≤ (r₃ : ℝ)
  · -- `r₃ ≥ σn/2`: the pair count alone gives `k ≤ 8/σ²`
    have hprod : σ ^ 2 * (n : ℝ) ^ 2 / 8 ≤ (r₃ : ℝ) * ((r₃ : ℝ) - 1) := by
      have h1 : (r₃ : ℝ) / 2 ≤ (r₃ : ℝ) - 1 := by linarith
      have h2 : (r₃ : ℝ) * ((r₃ : ℝ) / 2) ≤ (r₃ : ℝ) * ((r₃ : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hRpos)
      nlinarith [h2, hcase, hσ0, hn2, sq_nonneg (σ * (n : ℝ))]
    have hstep : (k : ℝ) * (σ ^ 2 * (n : ℝ) ^ 2 / 8) ≤ (n : ℝ) ^ 2 :=
      le_trans (mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg k))
        (by nlinarith [hpair', hn2])
    have hk8 : (k : ℝ) ≤ 8 / σ ^ 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < σ ^ 2)]
      nlinarith [hstep, hσ0, hn2]
    linarith [hk8, hbig]
  · -- `r₃ < σn/2`: `r₃² > n/(1−4σ)` gives the bound via the `(n−1)` slack
    have hRlt : (r₃ : ℝ) < σ * (n : ℝ) / 2 := not_le.mp hcase
    have hsq : (n : ℝ) / (1 - 4 * σ) < (r₃ : ℝ) ^ 2 := by
      have h1 : Real.sqrt ((n : ℝ) / (1 - 4 * σ)) ^ 2 = (n : ℝ) / (1 - 4 * σ) :=
        Real.sq_sqrt (by positivity)
      nlinarith [hup, h1, Real.sqrt_nonneg ((n : ℝ) / (1 - 4 * σ)), hRpos]
    have hkey : ((n : ℝ) - 1) / (1 - 3 * σ) ≤
        (n : ℝ) / (1 - 4 * σ) - σ * (n : ℝ) / 2 := by
      rw [div_le_iff₀ h3σ, sub_mul]
      have hL : (n : ℝ) / (1 - 4 * σ) * (1 - 3 * σ) - σ * (n : ℝ) / 2 * (1 - 3 * σ) =
          (n : ℝ) * (1 - 3 * σ) / (1 - 4 * σ) - σ * (n : ℝ) * (1 - 3 * σ) / 2 := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      rw [hL]
      have hkey2 : (n : ℝ) - 1 + σ * (n : ℝ) * (1 - 3 * σ) / 2 ≤
          (n : ℝ) * (1 - 3 * σ) / (1 - 4 * σ) := by
        have hσle : σ ≤ 1 / 8 := by linarith
        have hcube : σ ^ 3 * (n : ℝ) ≤ σ ^ 2 * (n : ℝ) / 8 := by
          have h := mul_le_mul_of_nonneg_right hσle
            (by positivity : (0 : ℝ) ≤ σ ^ 2 * ((n : ℝ) * 1))
          nlinarith [h]
        rw [le_div_iff₀ h4σ]
        nlinarith [hσ1, hσ4, hn2, hσ0, hcube]
      linarith [hkey2]
    have hprod : ((n : ℝ) - 1) / (1 - 3 * σ) ≤ (r₃ : ℝ) * ((r₃ : ℝ) - 1) := by
      nlinarith [hkey, hsq, hRlt]
    have hstep : (k : ℝ) * (((n : ℝ) - 1) / (1 - 3 * σ)) ≤ (n : ℝ) * ((n : ℝ) - 1) :=
      le_trans (mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg k)) hpair'
    have hnm1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have h2 : (k : ℝ) * ((n : ℝ) - 1) ≤ ((n : ℝ) * ((n : ℝ) - 1)) * (1 - 3 * σ) := by
      have h3 : (k : ℝ) * ((n : ℝ) - 1) =
          ((k : ℝ) * (((n : ℝ) - 1) / (1 - 3 * σ))) * (1 - 3 * σ) := by
        field_simp
      rw [h3]
      exact mul_le_mul_of_nonneg_right hstep (le_of_lt h3σ)
    nlinarith [h2, hnm1, h3σ]

/-- **The App-2 ordering is good when the left part is small.**  If
`e(𝓗₂^left) ≤ (1−3σ)n` then every edge of `𝓗₁^left` has `ord₂`-preceding degree
at most `(1−3σ)n`: the edges of `𝓗₂^left` (an initial segment) have all their
preceding neighbours inside `𝓗₂^left`, and `𝓗₂^good` is the App-2 goodness
`(reordering-goodness2)`. -/
theorem case22_good_ordering {n : ℕ} {Left₁ Left₂ Good₂ : Hypergraph (Fin n)} {k₂ : ℕ}
    (ord₂ : Left₁ ≃ Fin k₂) (hG₂sub : Good₂ ⊆ Left₁) (hL₂sub : Left₂ ⊆ Left₁)
    (hpart₂ : Good₂ ∪ Left₂ = Left₁) (hdisj₂ : Disjoint Good₂ Left₂)
    (hseg₂ : ∀ f u : Left₁, (f : Set (Fin n)) ∈ Left₂ → (u : Set (Fin n)) ∈ Good₂ →
      (ord₂ f : ℕ) ≤ (ord₂ u : ℕ))
    {σ : ℝ} (hdeg₂ : ∀ e : Left₁, (e : Set (Fin n)) ∈ Good₂ →
      (precedingDegree Left₁ ord₂ e : ℝ) ≤ (1 - 3 * σ) * (n : ℝ))
    (hcard : (Nat.card Left₂ : ℝ) ≤ (1 - 3 * σ) * (n : ℝ)) :
    ∀ e : Left₁, (precedingDegree Left₁ ord₂ e : ℝ) ≤ (1 - 3 * σ) * (n : ℝ) := by
  classical
  haveI : Fintype Left₂ := Fintype.ofFinite Left₂
  intro e
  have hmemAll : (e : Set (Fin n)) ∈ Good₂ ∨ (e : Set (Fin n)) ∈ Left₂ := by
    have h : (e : Set (Fin n)) ∈ Good₂ ∪ Left₂ := by rw [hpart₂]; exact e.2
    simpa only [Set.mem_union] using h
  rcases hmemAll with he | he
  · exact hdeg₂ e he
  · have hmem : ∀ g : {g : Left₁ // g ≠ e ∧ ord₂ g ≤ ord₂ e ∧
        (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)},
        (g.1 : Set (Fin n)) ∈ Left₂ := by
      intro g
      have hgAll : (g.1 : Set (Fin n)) ∈ Good₂ ∨ (g.1 : Set (Fin n)) ∈ Left₂ := by
        have h : ((g.1 : Set (Fin n))) ∈ Good₂ ∪ Left₂ := by rw [hpart₂]; exact g.1.2
        simpa only [Set.mem_union] using h
      rcases hgAll with hg | hl
      · exfalso
        have h1 : (ord₂ e : ℕ) ≤ (ord₂ g.1 : ℕ) := hseg₂ e g.1 he hg
        have h2 : (ord₂ g.1 : ℕ) ≤ (ord₂ e : ℕ) := g.2.2.1
        have h3 : ord₂ g.1 = ord₂ e := le_antisymm h2 h1
        exact g.2.1 (ord₂.injective h3)
      · exact hl
    have h1 : Nat.card {g : Left₁ // g ≠ e ∧ ord₂ g ≤ ord₂ e ∧
          (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} ≤ Nat.card Left₂ :=
      Nat.card_le_card_of_injective
        (fun g => (⟨(g.1 : Set (Fin n)), hmem g⟩ : Left₂))
        (by
          intro a b hab
          exact Subtype.ext (Subtype.ext
            (congrArg (fun x : Left₂ => (x : Set (Fin n))) hab)))
    rw [precedingDegree_eq_natCard]
    exact le_trans (by exact_mod_cast h1) hcard
/-- **Case 1 of Figure 3 with the App-2 ordering good.**  If every edge of
`𝓗₁^left` has `ord₂`-preceding degree at most `(1−3σ)n` (equivalently, the
App-2 ordering is *good*), the non-extremal alternative of Theorem 6.1 holds.
This is the version of `case1_of_blocks` used when the App-2 firing is in the
volume case but the resulting ordering is in fact good because `𝓗₂^left` is
small. -/
theorem case1_of_blocks_of_good {n r₁ r₀ : ℕ} {β γ₂ σ δ γ₁ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂}
    {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hdeg₂ : ∀ e : Left₁, (precedingDegree Left₁ ord₂ e : ℝ) ≤ (1 - 3 * σ) * (n : ℝ)) (hlin : 𝓗.IsLinear) (h2n : 2 ≤ n) (hr₁ : 2 ≤ r₁)
    (hβ : 0 < β) (hγ₂0 : 0 < γ₂) (hσ0 : 0 < σ) (hσ3 : 3 * σ ≤ 1) (hσ23 : σ ≤ 2 / 3)
    (hr₀ : 1 ≤ r₀) (hγ₁σ : γ₁ ≤ σ / 2) (hβn8 : 8 ≤ β * (n : ℝ))
    (hsize : ∀ e : 𝓗, r₁ < edgeSize (e : Set (Fin n)))
    (hsizeR : ∀ e : 𝓗, (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ))
    (hβn : (r₀ : ℝ) < β * (n : ℝ) / 4)
    (hA₁ : 32 / β ^ 2 ≤ σ * (n : ℝ))
    (hA₂ : 32 / β ^ 2 + 2 * γ₂ * (n : ℝ) / 3 ≤ (1 - 2 * σ) * (n : ℝ))
    (hmargin : (2 : ℝ) * (n : ℝ) / ((β / 5) * (r₀ : ℝ)) < ((σ / 2) * (n : ℝ)) / 4)
    (hbig : ((bigFinset (β / 5) (𝓗.largeEdges r₀)).card : ℝ) < ((σ / 2) * (n : ℝ)) / 2)
    {φmed : (𝓗.medEdges r₁ r₀).Coloring (Fin n)} {Cmed : Finset (Fin n)}
    (hφmed : φmed.UsesColourSet Cmed) (hCmed : (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ))
    (hmedb : ∀ c : Fin n, (φmed.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ))
    (hbudget : (Cmed.card : ℝ) + 1 ≤ (σ / 2) * (n : ℝ)) :
    LargeEdgeNonExtremal n σ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 := by
  exact largeEdge_nonExtremal_of_app1_app2 (n := n) (r₁ := r₁) (r₀ := r₀)
    (𝓗 := 𝓗) (β := β) (γ₂ := γ₂) (σ := σ) (γ₁ := γ₁)
    hβ hγ₂0 hσ0 hσ3 hσ23 hr₁ h2n hr₀ hβn8 hsize hsizeR hlin hγ₁σ hβn hA₁ hA₂
    ord₁ Good₁ Left₁ hB.hG₁sub hB.hL₁sub hB.hpart₁ hB.hdisj₁ hB.hdeg₁ hB.hseg₁
    ord₂ hdeg₂ hmargin hbig hφmed hCmed hmedb hbudget

/-- **`r₂ ≥ γ₂^{10} r₃` in Case 2.2.**  The App-1 volume set `W₁` and the
App-2 volume set `W₂` both have large volume (`volBound τ₁ K₁ ≤ vol(W₁)` and
`1 − δ³ ≤ vol(W₂)`); were they disjoint inside the linear family `𝓗'`, their
volumes would add up to at most one, contradicting
`δ³ < volBound τ₁ K₁`.  Hence they meet, and an edge `e ∈ W₁ ∩ W₂` has
`|e| ≥ r₃` and `|e| ≤ sizeFactor τ₁ K₁ · r₂ ≤ γ₂^{-10} r₂`. -/
theorem r₂_ge_r₃_of_blocks {n : ℕ} {β γ₂ σ δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂}
    {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hW₂ne : W₂ ≠ ∅) (hlin : 𝓗.IsLinear)
    (hV₁ : δ ^ 3 < volBound (app1tau γ₂) (app1K γ₂))
    (hA : sizeFactor (app1tau γ₂) (app1K γ₂) ≤ 1 / γ₂ ^ 10)
    (hγ₂0 : 0 < γ₂) :
    γ₂ ^ 10 * (r₃ : ℝ) ≤ (r₂ : ℝ) := by
  classical
  obtain ⟨W₁, hW₁sub, hW₁emp, hW₁vol, hW₁siz, -⟩ := hB.hasW₁
  have hW₁ne : W₁ ≠ ∅ := by
    intro hemp
    have hL₁emp : Left₁ = ∅ := hW₁emp hemp
    have hsub : W₂ ⊆ Left₁ := fun e he => hB.hL₂sub (hB.hW₂sub he)
    rw [hL₁emp] at hsub
    have hemp₂ : W₂ = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun e he => hsub he)
    exact hW₂ne hemp₂
  have hvol₁ : volBound (app1tau γ₂) (app1K γ₂) ≤ volume n (finFam W₁) := by
    rcases hW₁vol with hemp | hvol
    · exact absurd hemp hW₁ne
    · rwa [volume_finFam W₁] at hvol
  have hvol₂ : (1 : ℝ) - δ ^ 3 ≤ volume n W₂ := by
    rcases hB.hW₂vol with hemp | hvol
    · exact absurd hemp hW₂ne
    · exact hvol
  have hmeet : ∃ e : Set (Fin n), e ∈ finFam (𝓗 := nonHuge 𝓗 β) W₁ ∧ e ∈ W₂ := by
    by_contra hcon
    have hdisj : Disjoint (finFam (𝓗 := nonHuge 𝓗 β) W₁) W₂ := by
      rw [Set.disjoint_left]
      intro e he₁ he₂
      exact hcon ⟨e, he₁, he₂⟩
    have hsub : finFam (𝓗 := nonHuge 𝓗 β) W₁ ∪ W₂ ⊆ 𝓗 := by
      rintro e (he | he)
      · exact nonHuge_subset 𝓗 β (finFam_subset W₁ he)
      · exact nonHuge_subset 𝓗 β (hB.hL₁sub (hB.hL₂sub (hB.hW₂sub he)))
    have hle : volume n (finFam (𝓗 := nonHuge 𝓗 β) W₁ ∪ W₂) ≤ 1 :=
      volume_le_one_of_linear (IsLinear.mono hsub hlin)
    have hadd : volume n (finFam (𝓗 := nonHuge 𝓗 β) W₁ ∪ W₂) =
        volume n (finFam (𝓗 := nonHuge 𝓗 β) W₁) + volume n W₂ :=
      volume_subfamily_union hdisj
    linarith [hle, hadd, hvol₁, hvol₂, hV₁]
  obtain ⟨e, heW₁, heW₂⟩ := hmeet
  obtain ⟨heL₁, heW₁f⟩ := mem_finFam.mp heW₁
  have hge : (r₃ : ℝ) ≤ (edgeSize e : ℝ) := by
    have h := hB.hW₂size e heW₂
    exact_mod_cast h
  have hle : (edgeSize e : ℝ) ≤ sizeFactor (app1tau γ₂) (app1K γ₂) * (r₂ : ℝ) :=
    hW₁siz ⟨e, heL₁⟩ heW₁f
  have hkey : (r₃ : ℝ) ≤ (1 / γ₂ ^ 10) * (r₂ : ℝ) :=
    le_trans hge (le_trans hle
      (mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg r₂ : (0 : ℝ) ≤ (r₂ : ℝ))))
  have hpos : (0 : ℝ) < γ₂ ^ 10 := by positivity
  have hmul : γ₂ ^ 10 * ((1 / γ₂ ^ 10) * (r₂ : ℝ)) = (r₂ : ℝ) := by
    field_simp
  nlinarith [hkey, hpos, hmul, (Nat.cast_nonneg r₃ : (0 : ℝ) ≤ (r₃ : ℝ))]

/-- **Theorem 6.1 with Case 2.2 discharged.**  The only remaining hypotheses
beyond the Figure-3 block decomposition are the numeric hierarchy: the
Case-2.1 margins of `largeEdge_of_blocks` together with the Case-2.2 margins
(`hr₃up`, `hfac`, `h69b₂`, …) consumed by `case22_extremal`. -/
theorem largeEdge_of_blocks_full {Δ₀ : ℝ → ℝ} {C : ℝ} {m : ℕ}
    (hC : 0 < C)
    (hΔ₀bnd : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → Δ₀ ζ' ≤ C / ζ' ^ m)
    (hMRe : ∀ (ζ' : ℝ), 0 < ζ' → ζ' ≤ 1 → ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ), Δ₀ ζ' ≤ Δ →
        (G.maxDegree : ℝ) ≤ Δ →
        (∀ v : V, (nbrEdges G v : ℝ) ≤ (1 - ζ') * Δ ^ 2 / 2) →
        ∃ k : ℕ, (k : ℝ) ≤ (1 - ζ' / Real.exp 6) * Δ ∧ G.Colorable k)
    {n r₁ r₀ : ℕ} {β γ₂ σ δ γ₁ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂}
    {r₂ r₃ : ℕ} {Cmed : Finset (Fin n)}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hσ4 : 4 * σ ≤ 1 / 2) (hβ1 : β ≤ 1)
    (hbigcase : 8 / σ ^ 2 ≤ (1 - 3 * σ) * (n : ℝ))
    {n₀' : ℕ}
    (hLN : ∀ m : ℕ, n₀' ≤ m → ∀ 𝓖 : Hypergraph (Fin m), 𝓖.IsLinear →
      (∀ e : Set (Fin m), e ∈ 𝓖 → (1 - δ) * Real.sqrt (m : ℝ) ≤ (edgeSize e : ℝ)) →
      ∃ φ : 𝓖.Coloring (Fin m), ∀ c : Fin m, (φ.colorClass c).ncard ≤ 2)
    (hn₀ : n₀' ≤ n) (hγ₁0 : 0 < γ₁) (hδ16 : δ ≤ 1 / 16)
    (hfac : sizeFactor (3 * σ) 1 * Real.sqrt ((n : ℝ) / (1 - 4 * σ)) ≤
      (1 + δ) * Real.sqrt (n : ℝ))
    (hδ2n : 8 ≤ δ ^ 2 * (n : ℝ))
    (hsmall : (1 + δ) * Real.sqrt (n : ℝ) ≤ δ * (n : ℝ) / 2)
    (hhuge : (1 - δ) * Real.sqrt (n : ℝ) ≤ β * (n : ℝ) / 4)
    (hroomNat : ⌊γ₂ * (n : ℝ)⌋₊ + ⌈32 / β ^ 2⌉₊ ≤ n)
    (hm22₂ : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < (σ * (n : ℝ)) / 4)
    (hb22₂ : (((bigFinset (β / 5) Good₂).card : ℕ) : ℝ) < σ * (n : ℝ) / 2)
    (hm22₃ : (2 : ℝ) * (n : ℝ) / ((γ₁ / 2) * ((r₁ : ℝ) - 1)) < ((γ₂ / 3) * (n : ℝ)) / 4)
    (hb22₃ : (((bigFinset (γ₁ / 2) Good₁).card : ℕ) : ℝ) < ((γ₂ / 3) * (n : ℝ)) / 2)
    (hγ₂n : 1 ≤ (γ₂ / 3) * (n : ℝ))
    (hV₁ : δ ^ 3 < volBound (app1tau γ₂) (app1K γ₂)) (hγ₂2000 : γ₂ ≤ 1 / 2000)
    (hr₀h : 2 * (r₀ : ℝ) ≤ γ₂ ^ 10 * (1 - δ) * Real.sqrt (n : ℝ))
    (hβγ : 2 * (β * (n : ℝ) / 4) + β * (n : ℝ) / 4 + (γ₁ / 2) * (n : ℝ) ≤ γ₁ * (n : ℝ))
    (hlin : 𝓗.IsLinear) (hn : 0 < n) (h2n : 2 ≤ n) (hβ : 0 < β) (hγ₂0 : 0 < γ₂)
    (hσ0 : 0 < σ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 256)
    (hγ₁σ : γ₁ ≤ σ / 2) (hσ31 : 3 * σ ≤ 1) (hr₀ : 1 ≤ r₀) (h2r₀ : 2 ≤ r₀)
    (h2r₁ : 2 ≤ r₁) (hR : (100000000 : ℝ) ≤ (r₁ : ℝ))
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ))
    (hδV : δ ≤ volBound app3tau app3K)
    (h69m : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < ((1 / 6000 : ℝ) * (n : ℝ)) / 4)
    (h69b : (((bigFinset (β / 5) (case2H3med r₁ r₀ 𝓗 H₃)).card : ℕ) : ℝ) <
      ((1 / 6000 : ℝ) * (n : ℝ)) / 2)
    (h69mσ : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < ((σ / 4) * (n : ℝ)) / 4)
    (h69bσ : (((bigFinset (β / 5) (case2Right r₁ r₀ 𝓗 Good₁ Good₂)).card : ℕ) : ℝ) <
      ((σ / 4) * (n : ℝ)) / 2)
    (hnbig : 16 / Real.sqrt δ ≤ (n : ℝ))
    (hσsmall : (2 : ℝ) * σ + 1 / (n : ℝ) ≤ 1 / 12000)
    (h2βn : (2 : ℝ) ≤ (β / 5) * (n : ℝ))
    /- the Case-2.1 (`ζ := 1 − r₃/√n`) margins, in their `δ`-form -/
    (hδbig : δ ≤ 1 / 10 ^ 3)
    (hr₁δ : 10 ^ 7 / δ ≤ (r₁ : ℝ))
    (hsqrt : 4 * Real.sqrt (n : ℝ) ≤ β * (n : ℝ))
    (hαδ : 3 * tauQuarter (3 * σ) ≤ δ / 10 ^ 7)
    (hΔ₀δ : C * (6 / (5 * δ)) ^ m ≤ (n : ℝ))
    (hk2δ : 2 * δ ^ 2 + 2 * σ ≤ δ / 1000)
    (hmarginAδ : ((2 : ℝ) / ((β / 5) / 2) + 1) *
      ((n : ℝ) / (((β / 5) / 2 : ℝ) * (r₀ : ℝ))) ≤ δ * (n : ℝ) / 1000)
    (h2σδ : 2000 * σ ≤ δ)
    (hroom1C : (Cmed.card : ℝ) + (1 / 1000) * (n : ℝ) + 1 ≤ (n : ℝ))
    (hroom2C : (Cmed.card : ℝ) + 2 ≤ 2 * σ * (n : ℝ))
    (hbudgetC : (1 - 2 * σ) * (n : ℝ) + 2 ≤ (⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ : ℝ))
    (hβc : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n)
    (hσn : 32 / β ^ 2 ≤ σ * (n : ℝ))
    (hγm : (γ₂ / 3) * (n : ℝ) + 32 / β ^ 2 ≤ (1 - 2 * σ) * (n : ℝ))
    (hKroom : ⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ + Cmed.card ≤ n)
    (hslack : 1 + 32 / β ^ 2 ≤ (σ / 4) * (n : ℝ))
    (hβn : (r₀ : ℝ) < β * (n : ℝ) / 4)
    (hA₁ : 32 / β ^ 2 ≤ σ * (n : ℝ))
    (hA₂ : 32 / β ^ 2 + 2 * γ₂ * (n : ℝ) / 3 ≤ (1 - 2 * σ) * (n : ℝ))
    (hmargin : (2 : ℝ) * (n : ℝ) / ((β / 5) * (r₀ : ℝ)) < ((σ / 2) * (n : ℝ)) / 4)
    (hbig : ((bigFinset (β / 5) (𝓗.largeEdges r₀)).card : ℝ) < ((σ / 2) * (n : ℝ)) / 2)
    (hCmed : (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ))
    {φmed : (𝓗.medEdges r₁ r₀).Coloring (Fin n)} (hφmed : φmed.UsesColourSet Cmed)
    (hmedb : ∀ c : Fin n, (φmed.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ))
    (hbudget : (Cmed.card : ℝ) + 1 ≤ (σ / 2) * (n : ℝ)) :
    LargeEdgeNonExtremal n σ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 ∨
      LargeEdgeExtremal n δ γ₂ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 := by
  classical
  have hden : 0 < (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
    have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have h2 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
      have h3 : 0 < n - 1 := by omega
      exact_mod_cast h3
    exact mul_pos h1 h2
  have hσ23 : σ ≤ 2 / 3 := by linarith only [hσ31]
  have hσ32 : 3 * σ / 2 ≤ 1 := by linarith only [hσ31]
  have hsizeN : ∀ e : 𝓗, r₁ < edgeSize (e : Set (Fin n)) := fun e => by
    exact_mod_cast hsize e
  have hsizeR : ∀ e : 𝓗, (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) :=
    fun e => le_of_lt (hsize e)
  have hσn1 : 1 ≤ σ * (n : ℝ) := by
    have h32 : (1 : ℝ) ≤ 32 / β ^ 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < β ^ 2)]
      nlinarith [hβ, hβ1]
    linarith only [h32, hσn]
  have hlinL₂ : Left₂.IsLinear :=
    hlin.mono (fun e he => nonHuge_subset 𝓗 β (hB.hL₁sub (hB.hL₂sub he)))
  by_cases hW : W₂ = ∅
  · exact Or.inl (case1_of_blocks (n := n) (r₁ := r₁) (r₀ := r₀) hB hW hlin h2n h2r₁ hβ
      hγ₂0 hσ0 hσ31 hσ23 hr₀ hγ₁σ hβc hsizeN hsizeR hβn hA₁ hA₂
      hmargin hbig hφmed hCmed hmedb hbudget)
  · by_cases hr : (r₃ : ℝ) < (1 - δ) * Real.sqrt (n : ℝ)
    · -- the Case-2.1 specific numeric facts
      have hr₃big : 10 ^ 7 / δ ≤ (r₃ : ℝ) :=
        case21_hr₃big hB.hL₁sub hB.hL₂sub hB.hW₂sub hB.hW₂thr hW hr₁δ hsize
      have hbig3 : (r₃ : ℝ) ≤ β * (n : ℝ) / 4 := case21_hbig3 hδ0 hr hsqrt
      exact Or.inl (case2_nonExtremal' (Δ₀ := Δ₀) (C := C) (m := m) hC hΔ₀bnd hMRe hB hW
        hlin hn h2n hβ hσ0 hγ₁σ hσ32 hr₀ h2r₀ h2r₁ hR hsize hδ0 hδ1 hδV hr
        hδbig hr₃big hαδ hΔ₀δ hk2δ hbig3 hnbig hσsmall hmarginAδ h69m h69b h69mσ h69bσ
        h2βn hCmed h2σδ hroom1C hroom2C hbudgetC hβc hn1 hσn hγm hKroom hslack hβn hφmed
        hmedb)
    · have hr₃lo : (1 - δ) * Real.sqrt (n : ℝ) ≤ (r₃ : ℝ) := not_lt.mp hr
      by_cases hup : (r₃ : ℝ) ≤ Real.sqrt ((n : ℝ) / (1 - 4 * σ))
      · have hr₂r₃ : γ₂ ^ 10 * (r₃ : ℝ) ≤ (r₂ : ℝ) :=
          r₂_ge_r₃_of_blocks hB hW hlin hV₁ (app1_sizeFactor_le hγ₂0 hγ₂2000) hγ₂0
        exact Or.inr (case22_extremal (n := n) (r₁ := r₁) (r₀ := r₀) (n₀' := n₀') hB hW
          hr₃lo hup hfac hlin hn1 h2n hσn hβ hγ₂0 hσ0 hδ0 hδ16 hγ₁0 hβc hδ2n hsmall hden
          hsize h2r₀ h2r₁ hr₀ hLN hn₀ hhuge hroomNat hm22₂ hb22₂ hm22₃ hb22₃ hγ₂n hr₂r₃
          hr₀h hβn hβγ)
      · -- `r₃ > √(n/(1−4σ))`: the App-2 ordering is good, so Case 1 applies.
        have hup' : Real.sqrt ((n : ℝ) / (1 - 4 * σ)) < (r₃ : ℝ) := not_le.mp hup
        have hcard := case22_left_card_le (σ := σ) (r₃ := r₃) hlinL₂ h2n hB.hr₃ hσ0 hσ4 hσn1
          (fun e => hB.hsize₂ ⟨(e : Set (Fin n)), hB.hL₂sub e.2⟩ e.2) hup' hbigcase
        have hgood := case22_good_ordering ord₂ hB.hG₂sub hB.hL₂sub hB.hpart₂ hB.hdisj₂
          hB.hseg₂ hB.hdeg₂ hcard
        exact Or.inl (case1_of_blocks_of_good (n := n) (r₁ := r₁) (r₀ := r₀) hB hgood hlin h2n
          h2r₁ hβ hγ₂0 hσ0 hσ31 hσ23 hr₀ hγ₁σ hβc hsizeN hsizeR hβn hA₁ hA₂
          hmargin hbig hφmed hCmed hmedb hbudget)



end

end ErdosFaberLovaszConjecture

