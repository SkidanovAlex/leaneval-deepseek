import Submission.EFL.ColourCombine2
import Submission.EFL.LargeEdgeBlocks

/-!
# Theorem 6.1, Case 2: the two halves of `𝓗_large` and the huge colours

This module collects the elementary facts about the Case-2 splitting of the
large edges and about the set of colours assigned to *huge* edges.

* `case2Left` / `case2Right` are the two blocks `𝓗₂^left ∖ 𝓗_med` and
  `(𝓗₂^good ∪ 𝓗₁^good) ∖ 𝓗_med`.
* `case2_parts`: for a `BlocksOK` block decomposition they partition
  `𝓗_large`, every edge of the right block has size at least `r₀`, and the
  right block lies in `𝓗 ∖ 𝓗_huge`.
* `card_hugeColours_le`: a colouring of a subfamily assigns at most `32/β²`
  colours to its huge edges — the bound on the set `C_huge` of
  Case 2.1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The left half of `𝓗_large` in Case 2: `𝓗₂^left ∖ 𝓗_med`. -/
def case2Left (r₁ r₀ : ℕ) (𝓗 W₂ H₃ : Hypergraph (Fin n)) : Hypergraph (Fin n) :=
  (H₃ ∪ W₂) \ 𝓗.medEdges r₁ r₀

/-- The right half of `𝓗_large` in Case 2:
`(𝓗₂^good ∪ 𝓗₁^good) ∖ 𝓗_med`. -/
def case2Right (r₁ r₀ : ℕ) (𝓗 Good₁ Good₂ : Hypergraph (Fin n)) : Hypergraph (Fin n) :=
  (Good₂ ∪ Good₁) \ 𝓗.medEdges r₁ r₀

/-- `𝓗₃ ∖ 𝓗_med`: the part of the residual family that Proposition 6.9 is
applied to in Case 2.2 (and in the `𝓗₃` colouring of Case 2.1). -/
def case2H3med (r₁ r₀ : ℕ) (𝓗 H₃ : Hypergraph (Fin n)) : Hypergraph (Fin n) :=
  H₃ \ 𝓗.medEdges r₁ r₀

/-- `W₂ ∖ 𝓗_med`: the sparse block of Case 2.1 (Claim
`claim:sparse-colouring`). -/
def case2W2med (r₁ r₀ : ℕ) (𝓗 W₂ : Hypergraph (Fin n)) : Hypergraph (Fin n) :=
  W₂ \ 𝓗.medEdges r₁ r₀

/-- `𝓗₂^good ∖ 𝓗_med`: the first block of `case2Right`. -/
def case2Good₂med (r₁ r₀ : ℕ) (𝓗 Good₂ : Hypergraph (Fin n)) : Hypergraph (Fin n) :=
  Good₂ \ 𝓗.medEdges r₁ r₀

/-- `𝓗_huge ∪ (𝓗₂^left ∩ 𝓗₁^left)`: the family containing `𝓗₂^left`. -/
def case2HugeLeft₂ (β : ℝ) (𝓗 Left₂ : Hypergraph (Fin n)) : Hypergraph (Fin n) :=
  𝓗.hugeEdges β ∪ Left₂

/-- `𝓗₁^good ∖ 𝓗_med`: the second block of `case2Right`. -/
def case2Good₁med (r₁ r₀ : ℕ) (𝓗 Good₁ : Hypergraph (Fin n)) : Hypergraph (Fin n) :=
  Good₁ \ 𝓗.medEdges r₁ r₀

/-- **Case 2: the two halves of the large edges.** -/
theorem case2_parts {n r₁ r₀ : ℕ} {β γ₂ σ δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂} {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hsize : ∀ e : 𝓗, r₁ < edgeSize (e : Set (Fin n))) :
    case2Left r₁ r₀ 𝓗 W₂ H₃ ∪ case2Right r₁ r₀ 𝓗 Good₁ Good₂ = 𝓗.largeEdges r₀ ∧
    Disjoint (case2Left r₁ r₀ 𝓗 W₂ H₃) (case2Right r₁ r₀ 𝓗 Good₁ Good₂) ∧
    (∀ e : case2Right r₁ r₀ 𝓗 Good₁ Good₂, (r₀ : ℕ) ≤ edgeSize (e : Set (Fin n))) ∧
    (Good₂ ∪ Good₁) ⊆ nonHuge 𝓗 β := by
  classical
  have hnonhuge : (Good₂ ∪ Good₁) ⊆ nonHuge 𝓗 β := by
    rintro e (h | h)
    · exact hB.hL₁sub (hB.hG₂sub h)
    · exact hB.hG₁sub h
  have hsizeMed : ∀ e : Set (Fin n), e ∈ 𝓗 → e ∉ 𝓗.medEdges r₁ r₀ →
      r₀ < edgeSize e := by
    intro e he hnot
    have h1 : r₁ < edgeSize e := hsize ⟨e, he⟩
    by_contra hc
    have h2 : edgeSize e ≤ r₀ := by omega
    exact hnot ((mem_medEdges 𝓗 r₁ r₀ e).mpr ⟨he, h1, h2⟩)
  have hAsub : (H₃ ∪ W₂) ⊆ 𝓗 := by
    rintro e (h | h)
    · exact hB.hH₃sub h
    · exact nonHuge_subset 𝓗 β (hB.hL₁sub (hB.hL₂sub (hB.hW₂sub h)))
  have hBsub : (Good₂ ∪ Good₁) ⊆ 𝓗 := fun e he => nonHuge_subset 𝓗 β (hnonhuge he)
  refine ⟨?_, ?_, ?_, hnonhuge⟩
  · ext e
    constructor
    · rintro (⟨hA, hnm⟩ | ⟨hBm, hnm⟩)
      · exact ⟨hAsub hA, hsizeMed e (hAsub hA) hnm⟩
      · exact ⟨hBsub hBm, hsizeMed e (hBsub hBm) hnm⟩
    · intro he
      have he𝓗 : e ∈ 𝓗 := (mem_largeEdges 𝓗 r₀ e).mp he |>.1
      have hgt : r₀ < edgeSize e := (mem_largeEdges 𝓗 r₀ e).mp he |>.2
      have hnotmed : e ∉ 𝓗.medEdges r₁ r₀ := by
        intro hc
        exact absurd ((mem_medEdges 𝓗 r₁ r₀ e).mp hc).2.2 (by omega : ¬ edgeSize e ≤ r₀)
      rw [hB.hcover.symm] at he𝓗
      have he' : e ∈ (H₃ ∪ W₂) ∪ (Good₂ ∪ Good₁) := by
        rw [Set.union_assoc (H₃ ∪ W₂) Good₂ Good₁] at he𝓗
        exact he𝓗
      rcases he' with hv | hv
      · exact Or.inl ⟨hv, hnotmed⟩
      · exact Or.inr ⟨hv, hnotmed⟩
  · rw [Set.disjoint_left]
    intro e he he'
    simp only [case2Left, case2Right, Set.mem_sdiff, Set.mem_union] at he he'
    rcases he.1 with h3 | hW <;> rcases he'.1 with hG₂ | hG₁
    · exact (Set.disjoint_left.mp hB.hdisjH₃G₂) h3 hG₂
    · exact (Set.disjoint_left.mp hB.hdisjH₃G₁) h3 hG₁
    · exact (Set.disjoint_left.mp hB.hdisjW₂G₂) hW hG₂
    · exact (Set.disjoint_left.mp hB.hdisjW₂G₁) hW hG₁
  · intro e
    exact le_of_lt (hsizeMed (e : Set (Fin n)) (hBsub e.2.1) e.2.2)

/-- The set of colours assigned to the *huge* edges of a subfamily `A ⊆ 𝓗`. -/
def hugeColourSet {n : ℕ} (𝓗 A : Hypergraph (Fin n)) [Fintype A] (β : ℝ)
    (φ : A.Coloring (Fin n)) : Finset (Fin n) := by
  classical
  exact ((Finset.univ : Finset A).filter
    (fun e : A => (e : Set (Fin n)) ∈ 𝓗.hugeEdges β)).image φ.labels

/-- **App 3 in subfamily-volume form.**  If two disjoint subfamilies `𝓖₂`,
`𝓖₃` of a linear hypergraph are such that `𝓖₂` contains a volume set `W₂` of
volume at least `1 − δ³` (`δ ≤ volBound app3tau app3K`), then `𝓖₃` admits an
ordering with all preceding degrees at most `n/2000` (`app3tau`).  This is the
App-3 step of Figure 3 in the form used for `𝓖₂ = 𝓗₂^left` (`∋ W₂`) and
`𝓖₃ = 𝓗₃`: the volume alternative of the Reordering Lemma on `𝓖₃` would give
a set `W' ⊆ 𝓖₃` with `vol(W') ≥ δ`, contradicting
`vol(W₂) + vol(W') ≤ 1`. -/
theorem app3_goodOrdering_of_volume {n r₁ : ℕ} {𝓗 𝓖₂ 𝓖₃ W₂ : Hypergraph (Fin n)} {δ : ℝ}
    (hsub₂ : 𝓖₂ ⊆ 𝓗) (hsub₃ : 𝓖₃ ⊆ 𝓗) (h2n : 2 ≤ n) (h2r₁ : 2 ≤ r₁)
    (hR : (100000000 : ℝ) ≤ (r₁ : ℝ)) (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ))
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδV : δ ≤ volBound app3tau app3K)
    (hW₂sub : W₂ ⊆ 𝓖₂) (hdisj : Disjoint W₂ 𝓖₃)
    (hvol₂ : (1 : ℝ) - δ ^ 3 ≤ volume n W₂) :
    ∃ k₃ : ℕ, ∃ ord₃ : 𝓖₃ ≃ Fin k₃, GoodOrdering app3tau ord₃ := by
  classical
  obtain ⟨k₃, ord₃, hgood | hvol⟩ :=
    app3_firing (𝓖 := 𝓖₃) hsub₃ h2n h2r₁ (by norm_num [app3K]) hR hlin
      (fun e he => hsize ⟨e, he⟩)
  · exact ⟨k₃, ord₃, hgood⟩
  · exfalso
    obtain ⟨W', hW'⟩ := volume_ge_delta_of_witness δ hδV hvol
    have hW'sub : finFam W' ⊆ 𝓖₃ := finFam_subset W'
    have hvolW' : δ ≤ volume n (finFam W') := by
      rw [← volume_finFam W']; exact hW'
    have hdisj' : Disjoint W₂ (finFam W') := by
      rw [Set.disjoint_left]
      intro e he hf
      exact (Set.disjoint_left.mp hdisj) he (hW'sub hf)
    have hunion : volume n (W₂ ∪ finFam W') = volume n W₂ + volume n (finFam W') :=
      volume_subfamily_union hdisj'
    have hle : volume n (W₂ ∪ finFam W') ≤ 1 :=
      volume_le_one_of_linear (IsLinear.mono (fun e he => by
        rcases he with he | he
        · exact hsub₂ (hW₂sub he)
        · exact hsub₃ (hW'sub he)) hlin)
    have hcube : δ ^ 3 < δ := by
      have h2 : δ ^ 2 < δ := by nlinarith [hδ0, hδ1]
      nlinarith [h2, hδ0]
    linarith [hunion, hle, hvol₂, hvolW', hcube]

/-- **App 3 on `𝓗₃` (Case 2 of Theorem 6.1).**  In the volume case of App 2,
`𝓗₃` admits an ordering with all preceding degrees at most `n/2000`
(`GoodOrdering app3tau`), and consequently so does `𝓗₃ ∖ 𝓗_med`. -/
theorem case2_H3_goodOrdering {n r₁ r₀ : ℕ} {β γ₂ σ δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂} {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hW₂ne : W₂ ≠ ∅)
    (hlin : 𝓗.IsLinear) (h2n : 2 ≤ n) (h2r₁ : 2 ≤ r₁)
    (hR : (100000000 : ℝ) ≤ (r₁ : ℝ))
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ))
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδV : δ ≤ volBound app3tau app3K) :
    (∃ k₃ : ℕ, ∃ ord₃ : H₃ ≃ Fin k₃, GoodOrdering app3tau ord₃) ∧
    (∃ k₃ : ℕ, ∃ ord₃ : case2H3med r₁ r₀ 𝓗 H₃ ≃ Fin k₃,
      ∀ e : case2H3med r₁ r₀ 𝓗 H₃,
        (precedingDegree (case2H3med r₁ r₀ 𝓗 H₃) ord₃ e : ℝ) ≤ (1 - app3tau) * (n : ℝ)) := by
  classical
  have hvol₂ : (1 : ℝ) - δ ^ 3 ≤ volume n W₂ := by
    rcases hB.hW₂vol with h | h
    · exact absurd h hW₂ne
    · exact h
  obtain ⟨k₃, ord₃, hgood⟩ :=
    app3_goodOrdering_of_volume (𝓖₂ := Left₂) (𝓖₃ := H₃) (W₂ := W₂)
      (fun e he => nonHuge_subset 𝓗 β (hB.hL₁sub (hB.hL₂sub he))) hB.hH₃sub h2n h2r₁ hR hlin
      hsize hδ0 hδ1 hδV hB.hW₂sub hB.hH₃W₂disj.symm hvol₂
  refine ⟨⟨k₃, ord₃, hgood⟩, ?_⟩
  obtain ⟨m, ord₃', -, hdeg⟩ :=
    exists_restricted_ordering (𝓖 := H₃) ord₃ (𝓖' := case2H3med r₁ r₀ 𝓗 H₃)
      (fun e he => he.1)
  refine ⟨m, ord₃', fun e => ?_⟩
  have h1 : (precedingDegree (case2H3med r₁ r₀ 𝓗 H₃) ord₃' e : ℝ) ≤
      (precedingDegree H₃ ord₃ ⟨(e : Set (Fin n)), e.2.1⟩ : ℝ) := by
    exact_mod_cast hdeg e
  have h2 : (precedingDegree H₃ ord₃ ⟨(e : Set (Fin n)), e.2.1⟩ : ℝ) ≤
      (1 - app3tau) * (n : ℝ) := hgood _
  linarith

/-- An edge of `𝓗` that is not *medium* and is longer than `r₁` has size at
least `r₀`. -/
theorem lt_edgeSize_of_not_mem_medEdges {n r₁ r₀ : ℕ} {𝓗 : Hypergraph (Fin n)} {e : Set (Fin n)}
    (he : e ∈ 𝓗) (hnot : e ∉ 𝓗.medEdges r₁ r₀) (hsize : r₁ < edgeSize e) :
    r₀ < edgeSize e := by
  by_contra hc
  have h2 : edgeSize e ≤ r₀ := by omega
  exact hnot ((mem_medEdges 𝓗 r₁ r₀ e).mpr ⟨he, hsize, h2⟩)

/-- **Colouring `𝓗₃ ∖ 𝓗_med`** (Claim `claim:before-W-colouring` of the paper,
in its Proposition-6.9 form): every edge has size `> r₀`, the App-3 ordering
gives forward degree at most `n/2000`, so constant lists of size `n/1500`
suffice for Proposition 6.9 with `α₁ = 1/6000`, `α₂ = β/5`; hence there is a
`β/5`-bounded colouring using any prescribed colour set `D` with
`|D| ≥ n/1500`. -/
theorem case2_H3_colouring {n r₁ r₀ : ℕ} {β γ₂ σ δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂} {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hW₂ne : W₂ ≠ ∅)
    (hlin : 𝓗.IsLinear) (h2n : 2 ≤ n) (h2r₀ : 2 ≤ r₀) (hβ : 0 < β) (h2r₁ : 2 ≤ r₁)
    (hR : (100000000 : ℝ) ≤ (r₁ : ℝ))
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ))
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδV : δ ≤ volBound app3tau app3K)
    (h69m : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < ((1 / 6000 : ℝ) * (n : ℝ)) / 4)
    (h69b : (((bigFinset (β / 5) (case2H3med r₁ r₀ 𝓗 H₃)).card : ℕ) : ℝ) <
      ((1 / 6000 : ℝ) * (n : ℝ)) / 2)
    {D : Finset (Fin n)} (hD : (1 / 1500 : ℝ) * (n : ℝ) ≤ (D.card : ℝ)) :
    ∃ φ'' : (case2H3med r₁ r₀ 𝓗 H₃).Coloring (Fin n),
      φ''.UsesColourSet D ∧ φ''.AlphaBounded (β / 5) := by
  classical
  obtain ⟨-, k₃, ord₃, hgood₃⟩ :=
    case2_H3_goodOrdering hB hW₂ne hlin h2n h2r₁ hR (fun e => le_of_lt (hsize e)) hδ0 hδ1 hδV
  have hlist : ∀ e : case2H3med r₁ r₀ 𝓗 H₃,
      ((precedingDegree (case2H3med r₁ r₀ 𝓗 H₃) ord₃ e : ℝ) + (1 / 6000) * (n : ℝ)) ≤
        ((fun _ : case2H3med r₁ r₀ 𝓗 H₃ => D) e).card := by
    intro e
    have h1 := hgood₃ e
    have h2 : (1 - app3tau) * (n : ℝ) = (n : ℝ) / 2000 := by
      simp only [app3tau]; ring
    rw [h2] at h1
    have h3 : (1 / 1500 : ℝ) * (n : ℝ) = (n : ℝ) / 2000 + (1 / 6000) * (n : ℝ) := by ring
    linarith [h1, hD, h3]
  have hsize' : ∀ e : case2H3med r₁ r₀ 𝓗 H₃, (r₀ : ℕ) ≤ edgeSize (e : Set (Fin n)) := by
    intro e
    refine le_of_lt (lt_edgeSize_of_not_mem_medEdges (hB.hH₃sub e.2.1) e.2.2 ?_)
    have h := hsize ⟨(e : Set (Fin n)), hB.hH₃sub e.2.1⟩
    exact_mod_cast h
  have hlin' : (case2H3med r₁ r₀ 𝓗 H₃).IsLinear :=
    IsLinear.mono (fun e he => hB.hH₃sub he.1) hlin
  obtain ⟨φ'', hb, hmem⟩ :=
    prop69_colouring (n := n) (r := r₀) (k := k₃) (α₁ := 1 / 6000) (α₂ := β / 5)
      (𝓗 := case2H3med r₁ r₀ 𝓗 H₃) h2n h2r₀ (by linarith) h69m h69b hlin' hsize' ord₃
      (fun _ => D) hlist
  exact ⟨φ'', hmem, hb⟩

/-- **The colours assigned to huge edges are few.**  A colouring of a
subfamily assigns at most `32/β²` colours to its huge edges. -/
theorem card_hugeColours_le {n : ℕ} {𝓗 A : Hypergraph (Fin n)} [Fintype A] {β : ℝ}
    (φ : A.Coloring (Fin n)) (hlin : 𝓗.IsLinear) (hβ : 0 < β) (hβn : 8 ≤ β * (n : ℝ))
    (hn1 : 1 ≤ n) :
    ((hugeColourSet 𝓗 A β φ).card : ℝ) ≤ 32 / β ^ 2 := by
  classical
  let F : Finset A := (Finset.univ : Finset A).filter
    (fun e : A => (e : Set (Fin n)) ∈ 𝓗.hugeEdges β)
  have hF : hugeColourSet 𝓗 A β φ = F.image φ.labels := rfl
  rw [hF]
  have h1 : (F.image φ.labels).card ≤ F.card := Finset.card_image_le
  have h2 : F.card ≤ Nat.card (𝓗.hugeEdges β) := by
    have hinj : Function.Injective (fun e : {x : A // x ∈ F} =>
        (⟨(e.1 : Set (Fin n)), (Finset.mem_filter.mp e.2).2⟩ : 𝓗.hugeEdges β)) := by
      intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun x : 𝓗.hugeEdges β => (x : Set (Fin n))) hab))
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at this
  have h3 : ((Nat.card (𝓗.hugeEdges β) : ℕ) : ℝ) ≤ 32 / β ^ 2 :=
    natCard_hugeEdges_le (𝓗 := 𝓗) hlin hβ hβn hn1
  have h12 : ((F.image φ.labels).card : ℝ) ≤ ((Nat.card (𝓗.hugeEdges β) : ℕ) : ℝ) := by
    exact_mod_cast le_trans h1 h2
  exact le_trans h12 h3

/-- **The trivial colouring of `𝓗₃∖𝓗_med`** (the `k ≤ (ζ/1000 − 2σ)n` branch of
`claim:before-W-colouring`): if there are at least as many colours in `D` as
edges in `𝓗₃∖𝓗_med`, give every edge its own colour.  The colouring is
`(β/5)`-bounded because every class is a singleton. -/
theorem case2_H3med_distinct {r₁ r₀ : ℕ} {β : ℝ} {𝓗 H₃ : Hypergraph (Fin n)}
    [Fintype (case2H3med r₁ r₀ 𝓗 H₃)] (D : Finset (Fin n))
    (h : Nat.card (case2H3med r₁ r₀ 𝓗 H₃) ≤ D.card) :
    ∃ φ : (case2H3med r₁ r₀ 𝓗 H₃).Coloring (Fin n),
      φ.UsesColourSet D ∧ φ.AlphaBounded (β / 5) := by
  classical
  obtain ⟨t, htD, htcard⟩ := Finset.exists_subset_card_eq h
  have hcard : Fintype.card (case2H3med r₁ r₀ 𝓗 H₃) = t.card := by
    rw [← Nat.card_eq_fintype_card]
    exact htcard.symm
  let σ : (case2H3med r₁ r₀ 𝓗 H₃) ≃ ↥t :=
    (Fintype.equivFin _).trans ((Finset.equivFinOfCardEq hcard.symm).symm)
  refine ⟨⟨fun e => ((σ e : ↥t) : Fin n), ?_⟩, ?_, ?_⟩
  · intro e₁ e₂ hne _ hcol
    have h1 : (σ e₁ : ↥t) = (σ e₂ : ↥t) := Subtype.ext hcol
    exact hne (σ.injective h1)
  · intro e
    exact htD (σ e).2
  · intro c
    left
    rw [Set.ncard_le_one_iff_eq]
    by_cases hc : ∃ e : case2H3med r₁ r₀ 𝓗 H₃, ((σ e : ↥t) : Fin n) = c
    · obtain ⟨e, he⟩ := hc
      refine Or.inr ⟨e, ?_⟩
      ext e'
      simp only [Hypergraph.Coloring.colorClass, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro h'
        have h2 : (σ e' : ↥t) = (σ e : ↥t) := Subtype.ext (h'.trans he.symm)
        exact σ.injective h2
      · intro h'
        rw [h']; exact he
    · refine Or.inl ?_
      ext e'
      simp only [Hypergraph.Coloring.colorClass, Set.mem_ofPred_eq]
      exact ⟨fun h' => absurd ⟨e', h'⟩ hc, fun h' => absurd h' (Set.notMem_empty e')⟩



/-- **Lower bound on the volume of a subfamily from a minimum edge size.**  If
every edge of `𝓕` has size at least `r ≥ 1` then
`|𝓕|·(r−1)² ≤ vol(𝓕)·n²` (the volume is `∑_e |e|(|e|−1) / n(n−1)` and
`|e|(|e|−1) ≥ (r−1)²`). -/
theorem volume_ge_card_mul_sq {n : ℕ} {𝓕 : Hypergraph (Fin n)} [Fintype 𝓕] {r : ℕ}
    (h2n : 2 ≤ n) (hr : 1 ≤ r) (hsz : ∀ e : 𝓕, r ≤ edgeSize (e : Set (Fin n))) :
    (Nat.card 𝓕 : ℝ) * (((r : ℝ) - 1) ^ 2) ≤ volume n 𝓕 * ((n : ℝ) ^ 2) := by
  classical
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hsub1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  -- the per-edge bound
  have hterm : ∀ e ∈ canonFinset 𝓕,
      ((r - 1) * (r - 1) : ℕ) ≤ edgeSize e * (edgeSize e - 1) := by
    intro e he
    have he𝓕 : e ∈ 𝓕 := by simpa [canonFinset] using he
    have h1 : r ≤ edgeSize e := hsz ⟨e, he𝓕⟩
    have hr1 : 1 ≤ edgeSize e := le_trans hr h1
    have h2 : r - 1 ≤ edgeSize e - 1 := Nat.sub_le_sub_right h1 1
    exact Nat.mul_le_mul (le_trans (Nat.sub_le r 1) h1) h2
  have hsum : ((canonFinset 𝓕).card) * ((r - 1) * (r - 1)) ≤
      (canonFinset 𝓕).sum (fun e : Set (Fin n) => edgeSize e * (edgeSize e - 1)) := by
    calc ((canonFinset 𝓕).card) * ((r - 1) * (r - 1))
        = (canonFinset 𝓕).sum (fun _ : Set (Fin n) => (r - 1) * (r - 1)) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (canonFinset 𝓕).sum (fun e : Set (Fin n) => edgeSize e * (edgeSize e - 1)) :=
          Finset.sum_le_sum hterm
  have hcard : (canonFinset 𝓕).card = Nat.card 𝓕 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  -- cast the sum bound to `ℝ`
  have hcast : ((Nat.card 𝓕 : ℕ) : ℝ) * (((r : ℝ) - 1) * ((r : ℝ) - 1)) ≤
      (((canonFinset 𝓕).sum (fun e : Set (Fin n) =>
        edgeSize e * (edgeSize e - 1)) : ℕ) : ℝ) := by
    rw [← hcard]
    exact_mod_cast hsum
  have hns : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have h2nR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2n
  have hnn : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hSnn : (0 : ℝ) ≤ (((canonFinset 𝓕).sum (fun e : Set (Fin n) =>
      edgeSize e * (edgeSize e - 1)) : ℕ) : ℝ) := by
    have h0 : (0 : ℝ) ≤ (Nat.card 𝓕 : ℝ) * (((r : ℝ) - 1) * ((r : ℝ) - 1)) := by
      have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      have h2 : (0 : ℝ) ≤ (r : ℝ) - 1 := by linarith
      exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg h2 h2)
    linarith [hcast, h0]
  rw [volume_eq_canon, hns, div_mul_eq_mul_div, le_div_iff₀ hnn]
  nlinarith [hcast, hSnn, hnn]


/-- `vol(𝓗₃) ≤ δ³` in the volume case of App 2: `𝓗₃` is disjoint from the
volume set `W₂`, so `vol(𝓗₃) ≤ 1 − vol(W₂) ≤ δ³`. -/
theorem volume_H3_le {n : ℕ} {β γ₂ σ δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂} {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hW₂ne : W₂ ≠ ∅) (hlin : 𝓗.IsLinear) :
    volume n H₃ ≤ δ ^ 3 := by
  have hvol₂ : (1 : ℝ) - δ ^ 3 ≤ volume n W₂ := by
    rcases hB.hW₂vol with hemp | hvol
    · exact absurd hemp hW₂ne
    · exact hvol
  have hunion : volume n (H₃ ∪ W₂) = volume n H₃ + volume n W₂ :=
    volume_subfamily_union hB.hH₃W₂disj
  have hsub : H₃ ∪ W₂ ⊆ 𝓗 := by
    rintro e (he | he)
    · exact hB.hH₃sub he
    · exact nonHuge_subset 𝓗 β (hB.hL₁sub (hB.hL₂sub (hB.hW₂sub he)))
  have hle : volume n (H₃ ∪ W₂) ≤ 1 :=
    volume_le_one_of_linear (IsLinear.mono hsub hlin)
  linarith

/-- **The paper's `eqn:d3-upper-bound` in the `k`-large branch of Case 2.1.**
If `k := e(𝓗₃∖𝓗_med) > (ζ/1000 − 2σ)n ≥ 2δ²n` then the volume estimate
`k·(r₃−1)² ≤ vol(𝓗₃∖𝓗_med)·n² ≤ δ³n²` forces `(r₃−1)² < δn/2`, i.e.
`r₃ < δ^{1/4}√n`. -/
theorem r₃_lt_sqrt_of_k_large {n r₁ r₀ : ℕ} {β γ₂ σ δ ζ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂} {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hW₂ne : W₂ ≠ ∅) (hlin : 𝓗.IsLinear)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 16) (h2n : 2 ≤ n) (hr₃ : 1 ≤ r₃)
    (hsize₃ : ∀ e : case2H3med r₁ r₀ 𝓗 H₃, r₃ ≤ edgeSize (e : Set (Fin n)))
    (hk : (ζ / 1000 - 2 * σ) * (n : ℝ) < (Nat.card (case2H3med r₁ r₀ 𝓗 H₃) : ℝ))
    (hk2 : 2 * δ ^ 2 ≤ ζ / 1000 - 2 * σ)
    (hnbig : 16 / Real.sqrt δ ≤ (n : ℝ)) :
    (r₃ : ℝ) < Real.sqrt (Real.sqrt δ) * Real.sqrt (n : ℝ) := by
  classical
  haveI : Fintype (case2H3med r₁ r₀ 𝓗 H₃) := Fintype.ofFinite _
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hr₃R : (1 : ℝ) ≤ (r₃ : ℝ) := by exact_mod_cast hr₃
  -- the volume is squeezed between `k·(r₃−1)²/n²` and `δ³`
  have hlow := volume_ge_card_mul_sq (𝓕 := case2H3med r₁ r₀ 𝓗 H₃) h2n hr₃ hsize₃
  have hup : volume n (case2H3med r₁ r₀ 𝓗 H₃) ≤ δ ^ 3 :=
    le_trans (volume_subfamily_mono Set.sdiff_subset) (volume_H3_le hB hW₂ne hlin)
  have hmain : (Nat.card (case2H3med r₁ r₀ 𝓗 H₃) : ℝ) * (((r₃ : ℝ) - 1) ^ 2) ≤
      δ ^ 3 * (n : ℝ) ^ 2 := by
    have h1 : volume n (case2H3med r₁ r₀ 𝓗 H₃) * (n : ℝ) ^ 2 ≤ δ ^ 3 * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hup (sq_nonneg (n : ℝ))
    linarith [hlow, h1]
  have hk' : 2 * δ ^ 2 * (n : ℝ) < (Nat.card (case2H3med r₁ r₀ 𝓗 H₃) : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hk2 (le_of_lt hnpos)
    linarith [h1, hk]
  -- the arithmetic
  have harith : ((r₃ : ℝ) - 1) ^ 2 < δ * (n : ℝ) / 2 := by
    have hkpos : (0 : ℝ) < (Nat.card (case2H3med r₁ r₀ 𝓗 H₃) : ℝ) := by
      nlinarith [hk', hδ0, hnpos]
    have hmain' : ((r₃ : ℝ) - 1) ^ 2 ≤
        δ ^ 3 * (n : ℝ) ^ 2 / (Nat.card (case2H3med r₁ r₀ 𝓗 H₃) : ℝ) :=
      (le_div_iff₀ hkpos).mpr (by linarith [hmain])
    have h1 : δ ^ 3 * (n : ℝ) ^ 2 / (Nat.card (case2H3med r₁ r₀ 𝓗 H₃) : ℝ) <
        δ * (n : ℝ) / 2 := by
      rw [div_lt_div_iff₀ hkpos (by norm_num : (0 : ℝ) < 2)]
      have hδn : (0 : ℝ) < δ * (n : ℝ) := by positivity
      have hkey := mul_lt_mul_of_pos_left hk' hδn
      nlinarith [hkey]
    linarith [hmain', h1]
  -- take square roots
  have hsqrt : (r₃ : ℝ) - 1 < Real.sqrt (δ * (n : ℝ) / 2) := by
    have h1 : (0 : ℝ) ≤ (r₃ : ℝ) - 1 := by linarith
    have h2 : (0 : ℝ) ≤ δ * (n : ℝ) / 2 := by positivity
    have h3 : Real.sqrt (δ * (n : ℝ) / 2) ^ 2 = δ * (n : ℝ) / 2 := Real.sq_sqrt h2
    nlinarith [harith, h1, h2, h3, Real.sqrt_nonneg (δ * (n : ℝ) / 2)]
  -- the remaining arithmetic `1 + √(δn/2) < δ^{1/4}√n`
  have hbig : 1 + Real.sqrt (δ * (n : ℝ) / 2) <
      Real.sqrt (Real.sqrt δ) * Real.sqrt (n : ℝ) := by
    have hδpos : (0 : ℝ) < Real.sqrt δ := Real.sqrt_pos_of_pos hδ0
    have hδ4pos : (0 : ℝ) < Real.sqrt (Real.sqrt δ) := Real.sqrt_pos_of_pos hδpos
    have hsqq : Real.sqrt (Real.sqrt δ) * Real.sqrt (Real.sqrt δ) = Real.sqrt δ := by
      rw [← pow_two, Real.sq_sqrt (Real.sqrt_nonneg δ)]
    have hδ4le : Real.sqrt (Real.sqrt δ) ≤ 1 / 2 := by
      have h1 : Real.sqrt (Real.sqrt δ) ≤ Real.sqrt (Real.sqrt (1 / 16 : ℝ)) :=
        Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hδ1)
      have h2 : Real.sqrt (Real.sqrt (1 / 16 : ℝ)) = 1 / 2 := by
        have h3 : Real.sqrt (1 / 16 : ℝ) = 1 / 4 := by
          rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        rw [h3, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rwa [h2] at h1
    have h2sqrt : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by norm_num, by norm_num⟩
    have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
    have hEq : δ * (n : ℝ) / 2 = (Real.sqrt δ * Real.sqrt (n : ℝ)) ^ 2 / 2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hδ0),
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ))]
    have hroot : Real.sqrt (δ * (n : ℝ) / 2) =
        Real.sqrt δ * Real.sqrt (n : ℝ) / Real.sqrt 2 := by
      rw [hEq, Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
    -- `4 ≤ δ^{1/4}√n`
    have hX : 4 ≤ Real.sqrt (Real.sqrt δ) * Real.sqrt (n : ℝ) := by
      have h7 : Real.sqrt (Real.sqrt δ) * Real.sqrt (16 / Real.sqrt δ) ≤
          Real.sqrt (Real.sqrt δ) * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnbig) (le_of_lt hδ4pos)
      have h9 : Real.sqrt (16 / Real.sqrt δ) = 4 / Real.sqrt (Real.sqrt δ) := by
        rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 16),
          show Real.sqrt (16 : ℝ) = 4 by
            rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      have h8 : Real.sqrt (Real.sqrt δ) * Real.sqrt (16 / Real.sqrt δ) = 4 := by
        rw [h9]
        field_simp
      rwa [h8] at h7
    rw [hroot]
    have hstep : Real.sqrt δ * Real.sqrt (n : ℝ) / Real.sqrt 2 ≤
        Real.sqrt (Real.sqrt δ) * Real.sqrt (n : ℝ) / 2 := by
      have h1 : Real.sqrt δ = Real.sqrt (Real.sqrt δ) * Real.sqrt (Real.sqrt δ) := hsqq.symm
      have h2ge : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]
        norm_num
      have h2 : Real.sqrt (Real.sqrt δ) / Real.sqrt 2 ≤ 1 / 2 := by
        rw [div_le_iff₀ h2pos]
        nlinarith [hδ4le, h2ge]
      have h3 : (0 : ℝ) ≤ Real.sqrt (Real.sqrt δ) * Real.sqrt (n : ℝ) := by positivity
      have h4 : Real.sqrt (Real.sqrt δ) * Real.sqrt (Real.sqrt δ) * Real.sqrt (n : ℝ) /
          Real.sqrt 2 = (Real.sqrt (Real.sqrt δ) / Real.sqrt 2) *
            (Real.sqrt (Real.sqrt δ) * Real.sqrt (n : ℝ)) := by ring
      conv_lhs => rw [hsqq.symm]
      rw [h4]
      nlinarith [h2, h3]
    linarith [hstep, hX]
  linarith [hsqrt, hbig]



/-- **The `𝓗₃∖𝓗_med` colouring with the `k`-split.**  If `k` is small the
edges get distinct colours; otherwise `r₃ < δ^{1/4}√n` and `ζ` is close to one,
so the App-3 greedy colouring fits in the budget. -/
theorem case2_H3med_split {n r₁ r₀ : ℕ} {β γ₂ σ δ ζ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂} {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hW₂ne : W₂ ≠ ∅) (hlin : 𝓗.IsLinear) (h2n : 2 ≤ n) (h2r₀ : 2 ≤ r₀) (hβ : 0 < β)
    (h2r₁ : 2 ≤ r₁) (hR : (100000000 : ℝ) ≤ (r₁ : ℝ))
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 256) (hδV : δ ≤ volBound app3tau app3K)
    (h69m : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < ((1 / 6000 : ℝ) * (n : ℝ)) / 4)
    (h69b : (((bigFinset (β / 5) (case2H3med r₁ r₀ 𝓗 H₃)).card : ℕ) : ℝ) <
      ((1 / 6000 : ℝ) * (n : ℝ)) / 2)
    (hζdef : ζ = 1 - (r₃ : ℝ) / Real.sqrt (n : ℝ))
    (hk2 : 2 * δ ^ 2 ≤ ζ / 1000 - 2 * σ)
    (hnbig : 16 / Real.sqrt δ ≤ (n : ℝ))
    (hσsmall : (2 : ℝ) * σ + 1 / (n : ℝ) ≤ 1 / 12000)
    (hζpos : 0 < ζ)
    (hsize₃ : ∀ e : case2H3med r₁ r₀ 𝓗 H₃, r₃ ≤ edgeSize (e : Set (Fin n)))
    {C'' : Finset (Fin n)}
    (hD'' : ((⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ : ℕ) : ℝ) ≤ (C''.card : ℝ)) :
    ∃ φ'' : (case2H3med r₁ r₀ 𝓗 H₃).Coloring (Fin n),
      φ''.UsesColourSet C'' ∧ φ''.AlphaBounded (β / 5) := by
  classical
  by_cases hk : Nat.card (case2H3med r₁ r₀ 𝓗 H₃) ≤ ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊
  · -- the small-`k` branch: distinct colours
    exact case2_H3med_distinct C'' (le_trans hk (by exact_mod_cast hD''))
  · -- the large-`k` branch: `r₃ < δ^{1/4}√n`, so `ζ > 1 − δ^{1/4}` is close to one
    rw [not_le] at hk
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    have hrootpos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos_of_pos hnpos
    have hkR : (ζ / 1000 - 2 * σ) * (n : ℝ) <
        (Nat.card (case2H3med r₁ r₀ 𝓗 H₃) : ℝ) := by
      have h1 : (ζ / 1000 - 2 * σ) * (n : ℝ) ≤
          ((⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : ((⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ : ℕ) : ℝ) <
          (Nat.card (case2H3med r₁ r₀ 𝓗 H₃) : ℝ) := by exact_mod_cast hk
      linarith
    have hr₃ : (r₃ : ℝ) < Real.sqrt (Real.sqrt δ) * Real.sqrt (n : ℝ) :=
      r₃_lt_sqrt_of_k_large hB hW₂ne hlin hδ0 (by linarith) h2n
        (le_trans (by norm_num : 1 ≤ 2) hB.hr₃) hsize₃ hkR hk2 hnbig
    have hδ4le : Real.sqrt (Real.sqrt δ) ≤ 1 / 4 := by
      have h1 : Real.sqrt (Real.sqrt δ) ≤ Real.sqrt (Real.sqrt (1 / 256 : ℝ)) :=
        Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hδ1)
      have h2 : Real.sqrt (Real.sqrt (1 / 256 : ℝ)) = 1 / 4 := by
        have h3 : Real.sqrt (1 / 256 : ℝ) = 1 / 16 := by
          rw [show (1 / 256 : ℝ) = (1 / 16) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        rw [h3, show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rwa [h2] at h1
    -- `1/1500 + 2σ + 1/n ≤ ζ/1000`
    have hζbig : (1 : ℝ) / 1500 + 2 * σ + 1 / (n : ℝ) ≤ ζ / 1000 := by
      have h1 : (r₃ : ℝ) / Real.sqrt (n : ℝ) ≤ Real.sqrt (Real.sqrt δ) := by
        rw [div_le_iff₀ hrootpos]
        linarith [hr₃]
      have h2 : 1 - Real.sqrt (Real.sqrt δ) ≤ ζ := by
        rw [hζdef]; linarith [h1]
      have h3 : (1 : ℝ) / 1500 + 2 * σ + 1 / (n : ℝ) ≤ 3 / 4000 := by
        linarith [hσsmall]
      have h4 : (3 : ℝ) / 4000 ≤ (1 - Real.sqrt (Real.sqrt δ)) / 1000 := by
        nlinarith [hδ4le]
      linarith [h3, h4, h2]
    -- room for `⌈n/1500⌉₊` colours
    have hroom : (1 / 1500 : ℝ) * (n : ℝ) ≤ (C''.card : ℝ) := by
      have h2 : (1 / 1500 + 2 * σ + 1 / (n : ℝ)) * (n : ℝ) ≤ (ζ / 1000) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hζbig (le_of_lt hnpos)
      have h3 : (1 / 1500 + 2 * σ + 1 / (n : ℝ)) * (n : ℝ) =
          (1 / 1500) * (n : ℝ) + 2 * σ * (n : ℝ) + 1 := by
        field_simp
      rw [h3] at h2
      have h5 : (1 / 1500 : ℝ) * (n : ℝ) ≤ (ζ / 1000 - 2 * σ) * (n : ℝ) := by
        have h6 : (ζ / 1000 - 2 * σ) * (n : ℝ) = (ζ / 1000) * (n : ℝ) - 2 * σ * (n : ℝ) := by ring
        rw [h6]; linarith [h2]
      have h7 : (ζ / 1000 - 2 * σ) * (n : ℝ) ≤
          ((⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      linarith [h5, h7, hD'']
    obtain ⟨φ'', hφ''C, hφ''b⟩ :=
      case2_H3_colouring (hB := hB) (hW₂ne := hW₂ne) (hlin := hlin) (h2n := h2n)
        (h2r₀ := h2r₀) (hβ := hβ) (h2r₁ := h2r₁) (hR := hR) (hsize := hsize)
        (hδ0 := hδ0) (hδ1 := by linarith) (hδV := hδV) (h69m := h69m) (h69b := h69b)
        (D := C'') (hD := hroom)
    exact ⟨φ'', hφ''C, hφ''b⟩

/-- **The sparse colouring in a prescribed colour set** (Claim
`claim:sparse-colouring` of the paper, after Proposition 6.8(ii)).  If a
linear hypergraph has edge sizes in `[r, B]` and satisfies the locally-sparse
margins of Corollary 6.5 for `ζ`, and all edges have size at least `r' + 1`,
then for any prescribed colour set `D` of size at least `(1 − ζ/1000)n` there
is a proper edge-colouring using only colours of `D` whose classes are
`β'`-bounded. -/
theorem sparse_colouring_usesColourSet {Δ₀ : ℝ → ℝ}
    (hMR : ∀ (ζ' : ℝ), 0 < ζ' → ζ' ≤ 1 → ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ), Δ₀ ζ' ≤ Δ →
        (G.maxDegree : ℝ) ≤ Δ →
        (∀ v : V, (nbrEdges G v : ℝ) ≤ (1 - ζ') * Δ ^ 2 / 2) →
        ∃ k : ℕ, (k : ℝ) ≤ (1 - ζ' / Real.exp 6) * Δ ∧ G.Colorable k)
    {n : ℕ} {ζ : ℝ} {r B : ℕ} {𝓖 : Hypergraph (Fin n)} [Fintype 𝓖] {Δ : ℝ}
    (hm : Corollary65Margins Δ₀ ζ r B n Δ) (hlin : 𝓖.IsLinear)
    (hsize_ge : ∀ e : 𝓖, r ≤ edgeSize (e : Set (Fin n)))
    (hsize_le : ∀ e : 𝓖, edgeSize (e : Set (Fin n)) ≤ B)
    {β' : ℝ} (hβ' : 0 < β') (h2β'n : (2 : ℝ) ≤ β' * (n : ℝ)) (h2n : 2 ≤ n)
    {r' : ℕ} (hr' : 1 ≤ r') (hsize' : ∀ e : 𝓖, (r' + 1 : ℕ) ≤ edgeSize (e : Set (Fin n)))
    (hmargin : ((2 : ℝ) / (β' / 2) + 1) * ((n : ℝ) / ((β' / 2 : ℝ) * (r' : ℝ))) ≤
      ζ * (n : ℝ) / 1000)
    (D : Finset (Fin n)) (hD : (1 - ζ / 1000) * (n : ℝ) ≤ (D.card : ℝ)) :
    ∃ φ : 𝓖.Coloring (Fin n), φ.UsesColourSet D ∧ φ.AlphaBounded β' := by
  classical
  obtain ⟨k, hk, hcol⟩ := corollary_6_5 hMR hm hlin hsize_ge hsize_le
  obtain ⟨φk⟩ := hcol
  have hζ0 : 0 < ζ := hm.hζ0
  have hkn : k ≤ n := by
    have h1 : (k : ℝ) ≤ (n : ℝ) := by
      have h2 : (k : ℝ) ≤ (1 : ℝ) * (n : ℝ) := by
        refine hk.trans ?_
        nlinarith [hζ0, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
      simpa using h2
    exact_mod_cast h1
  let C : Finset (Fin n) := (Finset.univ : Finset (Fin k)).image (Fin.castLE hkn)
  have hCcard : C.card = k := by
    rw [Finset.card_image_of_injective _ (Fin.castLE_injective hkn), Finset.card_univ,
      Fintype.card_fin]
  have hφnC : (φk.ofLeColors hkn).UsesColourSet C := by
    intro e
    exact Finset.mem_image.mpr ⟨φk.labels e, Finset.mem_univ _, rfl⟩
  obtain ⟨m, ψ, hψb, hψm⟩ :=
    alpha_bounded_recolour (n := n) (r := r') (β := β') hβ' h2β'n h2n hr' hlin hsize'
      (φk.ofLeColors hkn) hφnC
  have hmD : m ≤ D.card := by
    rw [hCcard] at hψm
    have h1 : (m : ℝ) ≤ (1 - ζ / 1000) * (n : ℝ) := by
      refine hψm.trans ?_
      have h2 : (k : ℝ) + (((2 : ℝ) / (β' / 2) + 1) *
          ((n : ℝ) / ((β' / 2 : ℝ) * (r' : ℝ)))) ≤
          (1 - ζ / 500) * (n : ℝ) + ζ * (n : ℝ) / 1000 := by linarith [hk, hmargin]
      refine h2.trans ?_
      have : (1 - ζ / 500) * (n : ℝ) + ζ * (n : ℝ) / 1000 = (1 - ζ / 1000) * (n : ℝ) := by
        ring
      rw [this]
    exact_mod_cast h1.trans hD
  exact exists_coloring_usesColourSet D hmD ψ hψb

/-- **Colouring `W₂ ∖ 𝓗_med`** (Claim `claim:sparse-colouring` of the paper):
the sizes of `W₂` are in `[r₃, sizeFactor (3σ) 1 · r₃]`, so with the
locally-sparse margins (`Corollary65Margins` for `ζ` at `r₃`) and
Proposition 6.8(ii) at `β/5` one gets a `β/5`-bounded colouring of
`W₂ ∖ 𝓗_med` using any prescribed colour set `D` with
`|D| ≥ (1 − ζ/1000)n`. -/
theorem case2_W2_sparse {Δ₀ : ℝ → ℝ}
    (hMRe : ∀ (ζ' : ℝ), 0 < ζ' → ζ' ≤ 1 → ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ), Δ₀ ζ' ≤ Δ →
        (G.maxDegree : ℝ) ≤ Δ →
        (∀ v : V, (nbrEdges G v : ℝ) ≤ (1 - ζ') * Δ ^ 2 / 2) →
        ∃ k : ℕ, (k : ℝ) ≤ (1 - ζ' / Real.exp 6) * Δ ∧ G.Colorable k)
    {n r₁ r₀ : ℕ} {β γ₂ σ δ : ℝ} {ζ : ℝ} {B₀ : ℕ} {Δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂} {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hlin : 𝓗.IsLinear) (h2n : 2 ≤ n) (hβ : 0 < β) (h2βn : (2 : ℝ) ≤ (β / 5) * (n : ℝ))
    (hr₀ : 1 ≤ r₀) (hsize : ∀ e : 𝓗, (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ))
    (hm : Corollary65Margins Δ₀ ζ r₃ B₀ n Δ)
    (hB₀ : sizeFactor (3 * σ) 1 * (r₃ : ℝ) ≤ (B₀ : ℝ))
    (hmargin : ((2 : ℝ) / ((β / 5) / 2) + 1) *
      ((n : ℝ) / (((β / 5) / 2 : ℝ) * (r₀ : ℝ))) ≤ ζ * (n : ℝ) / 1000)
    {D : Finset (Fin n)} (hD : (1 - ζ / 1000) * (n : ℝ) ≤ (D.card : ℝ)) :
    ∃ φ' : (case2W2med r₁ r₀ 𝓗 W₂).Coloring (Fin n),
      φ'.UsesColourSet D ∧ φ'.AlphaBounded (β / 5) := by
  classical
  haveI : Fintype (case2W2med r₁ r₀ 𝓗 W₂) := Fintype.ofFinite _
  have hsub : case2W2med r₁ r₀ 𝓗 W₂ ⊆ 𝓗 := fun e he =>
    nonHuge_subset 𝓗 β (hB.hL₁sub (hB.hL₂sub (hB.hW₂sub he.1)))
  have hsize_ge : ∀ e : case2W2med r₁ r₀ 𝓗 W₂, r₃ ≤ edgeSize (e : Set (Fin n)) :=
    fun e => hB.hW₂size (e : Set (Fin n)) e.2.1
  have hsize_le : ∀ e : case2W2med r₁ r₀ 𝓗 W₂, edgeSize (e : Set (Fin n)) ≤ B₀ := by
    intro e
    have h1 := hB.hW₂size_le (e : Set (Fin n)) e.2.1
    have h2 : (edgeSize (e : Set (Fin n)) : ℝ) ≤ (B₀ : ℝ) := le_trans h1 hB₀
    exact_mod_cast h2
  have hsize' : ∀ e : case2W2med r₁ r₀ 𝓗 W₂, (r₀ + 1 : ℕ) ≤ edgeSize (e : Set (Fin n)) := by
    intro e
    have h1 : r₁ < edgeSize (e : Set (Fin n)) := by
      have := hsize ⟨(e : Set (Fin n)), hsub e.2⟩
      exact_mod_cast this
    have h2 : r₀ < edgeSize (e : Set (Fin n)) :=
      lt_edgeSize_of_not_mem_medEdges (𝓗 := 𝓗) (r₁ := r₁) (r₀ := r₀) (hsub e.2) e.2.2 h1
    omega
  exact sparse_colouring_usesColourSet hMRe hm (IsLinear.mono hsub hlin) hsize_ge hsize_le
    (by linarith) h2βn h2n hr₀ hsize' hmargin D hD


/-- **The two Case-2 blocks cover `𝓗₂^left ∖ 𝓗_med`.** -/
theorem case2_cover_parts {n r₁ r₀ : ℕ} {𝓗 W₂ H₃ : Hypergraph (Fin n)} :
    case2W2med r₁ r₀ 𝓗 W₂ ∪ case2H3med r₁ r₀ 𝓗 H₃ = case2Left r₁ r₀ 𝓗 W₂ H₃ := by
  rw [case2W2med, case2H3med, case2Left, ← Set.union_diff_distrib, Set.union_comm W₂ H₃]


/-- **The colour class of the combined colouring, at a colour of the first
part, is the image of the first colouring's class** (so in particular it has
the same cardinality).  This is the `ncard` companion of
`mem_colorClass_coloringUnionOfCover_left`, needed to transport
`AlphaBounded` across `coloringUnionOfCover`. -/
theorem ncard_colorClass_coloringUnionOfCover_left {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    {h₁ : 𝓖₁ ⊆ 𝓗} {h₂ : 𝓖₂ ⊆ 𝓗} {hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂}
    {hdisjG : Disjoint 𝓖₁ 𝓖₂} {C₁ C₂ : Finset (Fin n)} {hdisj : Disjoint C₁ C₂}
    {φ₁ : 𝓖₁.Coloring (Fin n)} {φ₂ : 𝓖₂.Coloring (Fin n)}
    (hφ₁ : φ₁.UsesColourSet C₁) (hφ₂ : φ₂.UsesColourSet C₂)
    {c : Fin n} (hc : c ∈ C₁) :
    ((coloringUnionOfCover h₁ h₂ hcover hdisjG hdisj φ₁ φ₂ hφ₁ hφ₂).colorClass c).ncard =
      (φ₁.colorClass c).ncard := by
  let f : 𝓖₁ → 𝓗 := fun x => ⟨(x : Set (Fin n)), h₁ x.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun y : 𝓗 => (y : Set (Fin n))) hab)
  have hset : f '' (φ₁.colorClass c) =
      (coloringUnionOfCover h₁ h₂ hcover hdisjG hdisj φ₁ φ₂ hφ₁ hφ₂).colorClass c := by
    apply Set.Subset.antisymm
    · rintro e ⟨e₀, hcl, hv⟩
      have hval : (e₀ : Set (Fin n)) = (e : Set (Fin n)) :=
        congrArg (fun y : 𝓗 => (y : Set (Fin n))) hv
      have hmem : (e : Set (Fin n)) ∈ 𝓖₁ := hval ▸ e₀.2
      refine (mem_colorClass_coloringUnionOfCover_left hφ₁ hφ₂ hc e).mpr ⟨hmem, ?_⟩
      have hEq : e₀ = (⟨(e : Set (Fin n)), hmem⟩ : 𝓖₁) := Subtype.ext hval
      rwa [hEq] at hcl
    · intro e he
      obtain ⟨he₁, hcl⟩ := (mem_colorClass_coloringUnionOfCover_left hφ₁ hφ₂ hc e).mp he
      exact ⟨⟨(e : Set (Fin n)), he₁⟩, hcl, Subtype.ext rfl⟩
  rw [← hset]
  exact Set.ncard_image_of_injective _ hf

/-- **The colour class of the combined colouring, at a colour outside the
first part's colour set, is the image of the second colouring's class.** -/
theorem ncard_colorClass_coloringUnionOfCover_right {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    {h₁ : 𝓖₁ ⊆ 𝓗} {h₂ : 𝓖₂ ⊆ 𝓗} {hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂}
    {hdisjG : Disjoint 𝓖₁ 𝓖₂} {C₁ C₂ : Finset (Fin n)} {hdisj : Disjoint C₁ C₂}
    {φ₁ : 𝓖₁.Coloring (Fin n)} {φ₂ : 𝓖₂.Coloring (Fin n)}
    (hφ₁ : φ₁.UsesColourSet C₁) (hφ₂ : φ₂.UsesColourSet C₂)
    {c : Fin n} (hc : c ∉ C₁) :
    ((coloringUnionOfCover h₁ h₂ hcover hdisjG hdisj φ₁ φ₂ hφ₁ hφ₂).colorClass c).ncard =
      (φ₂.colorClass c).ncard := by
  let f : 𝓖₂ → 𝓗 := fun x => ⟨(x : Set (Fin n)), h₂ x.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun y : 𝓗 => (y : Set (Fin n))) hab)
  have hset : f '' (φ₂.colorClass c) =
      (coloringUnionOfCover h₁ h₂ hcover hdisjG hdisj φ₁ φ₂ hφ₁ hφ₂).colorClass c := by
    apply Set.Subset.antisymm
    · rintro e ⟨e₀, hcl, hv⟩
      have hval : (e₀ : Set (Fin n)) = (e : Set (Fin n)) :=
        congrArg (fun y : 𝓗 => (y : Set (Fin n))) hv
      have hmem : (e : Set (Fin n)) ∈ 𝓖₂ := hval ▸ e₀.2
      refine (mem_colorClass_coloringUnionOfCover_right hφ₁ hφ₂ hc e).mpr ⟨hmem, ?_⟩
      have hEq : e₀ = (⟨(e : Set (Fin n)), hmem⟩ : 𝓖₂) := Subtype.ext hval
      rwa [hEq] at hcl
    · intro e he
      obtain ⟨he₂, hcl⟩ := (mem_colorClass_coloringUnionOfCover_right hφ₁ hφ₂ hc e).mp he
      exact ⟨⟨(e : Set (Fin n)), he₂⟩, hcl, Subtype.ext rfl⟩
  rw [← hset]
  exact Set.ncard_image_of_injective _ hf


/-- **`φ₁`: the Case-2.1 colouring of `𝓗₂^left ∖ 𝓗_med`.**  The sparse
colouring of `W₂ ∖ 𝓗_med` (Claim `claim:sparse-colouring`,
`case2_W2_sparse`) and the Proposition 6.9 colouring of `𝓗₃ ∖ 𝓗_med`
(Claim `claim:before-W-colouring`, `case2_H3_colouring`) live on disjoint
subfamilies (`case2_cover_parts`) and use disjoint prescribed colour sets, so
`coloringUnionOfCover` combines them into a `β/5`-bounded colouring of
`𝓗₂^left ∖ 𝓗_med` using at most `(1−2σ)n` colours (Lemma
`case2_colouring_left`). -/
theorem case2_colouring_left {Δ₀ : ℝ → ℝ}
    (hMRe : ∀ (ζ' : ℝ), 0 < ζ' → ζ' ≤ 1 → ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ), Δ₀ ζ' ≤ Δ →
        (G.maxDegree : ℝ) ≤ Δ →
        (∀ v : V, (nbrEdges G v : ℝ) ≤ (1 - ζ') * Δ ^ 2 / 2) →
        ∃ k : ℕ, (k : ℝ) ≤ (1 - ζ' / Real.exp 6) * Δ ∧ G.Colorable k)
    {n r₁ r₀ : ℕ} {β γ₂ σ δ ζ : ℝ} {B₀ : ℕ} {Δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂} {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hW₂ne : W₂ ≠ ∅)
    (hlin : 𝓗.IsLinear) (h2n : 2 ≤ n) (hβ : 0 < β) (hσ0 : 0 < σ) (hσ32 : 3 * σ / 2 ≤ 1)
    (h2βn : (2 : ℝ) ≤ (β / 5) * (n : ℝ))
    (hr₀ : 1 ≤ r₀) (h2r₀ : 2 ≤ r₀) (h2r₁ : 2 ≤ r₁) (hR : (100000000 : ℝ) ≤ (r₁ : ℝ))
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 256) (hδV : δ ≤ volBound app3tau app3K)
    (hm : Corollary65Margins Δ₀ ζ r₃ B₀ n Δ)
    (hB₀ : sizeFactor (3 * σ) 1 * (r₃ : ℝ) ≤ (B₀ : ℝ))
    (hmarginA : ((2 : ℝ) / ((β / 5) / 2) + 1) *
      ((n : ℝ) / (((β / 5) / 2 : ℝ) * (r₀ : ℝ))) ≤ ζ * (n : ℝ) / 1000)
    (h69m : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < ((1 / 6000 : ℝ) * (n : ℝ)) / 4)
    (h69b : (((bigFinset (β / 5) (case2H3med r₁ r₀ 𝓗 H₃)).card : ℕ) : ℝ) <
      ((1 / 6000 : ℝ) * (n : ℝ)) / 2)
    /- the Case-2.1 `k`-split data -/
    (hζdef : ζ = 1 - (r₃ : ℝ) / Real.sqrt (n : ℝ)) (hζpos : 0 < ζ)
    (hk2 : 2 * δ ^ 2 ≤ ζ / 1000 - 2 * σ)
    (hnbig : 16 / Real.sqrt δ ≤ (n : ℝ))
    (hσsmall : (2 : ℝ) * σ + 1 / (n : ℝ) ≤ 1 / 12000)
    (hsize₃ : ∀ e : case2H3med r₁ r₀ 𝓗 H₃, r₃ ≤ edgeSize (e : Set (Fin n)))
    {Cmed : Finset (Fin n)}
    (hroom1 : ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ ≤ (Finset.univ \ Cmed).card)
    (hroom2 : ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ + ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ ≤
      (Finset.univ \ Cmed).card)
    (hbudget : ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ + ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ ≤
      ⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊) :
    ∃ (C₁ : Finset (Fin n)) (φ₁ : (case2Left r₁ r₀ 𝓗 W₂ H₃).Coloring (Fin n)),
      φ₁.UsesColourSet C₁ ∧ φ₁.AlphaBounded (β / 5) ∧
      (C₁.card : ℝ) ≤ (1 - 3 * σ / 2) * (n : ℝ) ∧
      C₁.card ≤ ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ + ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ ∧
      Disjoint C₁ Cmed := by
  classical
  -- the cover and its disjointness
  have hcover : case2W2med r₁ r₀ 𝓗 W₂ ∪ case2H3med r₁ r₀ 𝓗 H₃ = case2Left r₁ r₀ 𝓗 W₂ H₃ :=
    case2_cover_parts
  have hsubW : case2W2med r₁ r₀ 𝓗 W₂ ⊆ case2Left r₁ r₀ 𝓗 W₂ H₃ := by
    rw [← hcover]; exact Set.subset_union_left
  have hsubH : case2H3med r₁ r₀ 𝓗 H₃ ⊆ case2Left r₁ r₀ 𝓗 W₂ H₃ := by
    rw [← hcover]; exact Set.subset_union_right
  have hdisjGH : Disjoint (case2W2med r₁ r₀ 𝓗 W₂) (case2H3med r₁ r₀ 𝓗 H₃) := by
    rw [Set.disjoint_left]
    intro e he he'
    exact (Set.disjoint_left.mp hB.hH₃W₂disj) he'.1 he.1
  have hcov : ∀ e ∈ case2Left r₁ r₀ 𝓗 W₂ H₃,
      e ∈ case2W2med r₁ r₀ 𝓗 W₂ ∨ e ∈ case2H3med r₁ r₀ 𝓗 H₃ := by
    intro e he
    rw [← hcover] at he
    simpa only [Set.mem_union] using he
  -- the two prescribed colour sets
  obtain ⟨C', hC'sub, hC'card⟩ := Finset.exists_subset_card_eq hroom1
  have hroom2' : ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ ≤ (Finset.univ \ (Cmed ∪ C')).card := by
    have h1 : Finset.univ \ (Cmed ∪ C') = (Finset.univ \ Cmed) \ C' := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, true_and, not_or]
    rw [h1]
    have h2 : (Finset.univ \ Cmed).card - C'.card ≤ ((Finset.univ \ Cmed) \ C').card := by
      have h3 : (Finset.univ \ Cmed).card =
          ((Finset.univ \ Cmed) \ C').card + ((Finset.univ \ Cmed) ∩ C').card :=
        (Finset.card_sdiff_add_card_inter _ _).symm
      have h4 : ((Finset.univ \ Cmed) ∩ C').card ≤ C'.card :=
        Finset.card_le_card Finset.inter_subset_right
      rw [Nat.sub_le_iff_le_add, h3]
      exact Nat.add_le_add_left h4 _
    have h5 : ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ ≤ (Finset.univ \ Cmed).card - C'.card := by
      rw [hC'card]
      omega
    linarith
  obtain ⟨C'', hC''sub, hC''card⟩ := Finset.exists_subset_card_eq hroom2'
  have hC'disj : Disjoint C' Cmed := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp (hC'sub hx)).2 hx'
  have hC''disj : Disjoint C'' (Cmed ∪ C') := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp (hC''sub hx)).2 hx'
  have hC'C''disj : Disjoint C' C'' := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp (hC''sub hx')).2 (Finset.mem_union.mpr (Or.inr hx))
  -- the two colourings
  have hD' : (1 - ζ / 1000) * (n : ℝ) ≤ (C'.card : ℝ) := by
    rw [hC'card]; exact Nat.le_ceil _
  have hD'' : ((⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ : ℕ) : ℝ) ≤ (C''.card : ℝ) := by
    rw [hC''card]
  obtain ⟨φ', hφ'C, hφ'b⟩ :=
    case2_W2_sparse (Δ₀ := Δ₀) (hMRe := hMRe) (hB := hB) (hlin := hlin) (h2n := h2n)
      (hβ := hβ) (h2βn := h2βn) (hr₀ := hr₀) (hsize := hsize) (hm := hm) (hB₀ := hB₀)
      (hmargin := hmarginA) (D := C') (hD := hD')
  obtain ⟨φ'', hφ''C, hφ''b⟩ :=
    case2_H3med_split (hB := hB) (hW₂ne := hW₂ne) (hlin := hlin) (h2n := h2n)
      (h2r₀ := h2r₀) (hβ := hβ) (h2r₁ := h2r₁) (hR := hR) (hsize := hsize) (hδ0 := hδ0)
      (hδ1 := hδ1) (hδV := hδV) (h69m := h69m) (h69b := h69b) (hζdef := hζdef)
      (hk2 := hk2) (hnbig := hnbig) (hσsmall := hσsmall) (hζpos := hζpos)
      (hsize₃ := hsize₃) (C'' := C'') (hD'' := hD'')
  refine ⟨C' ∪ C'', coloringUnionOfCover hsubW hsubH hcov hdisjGH hC'C''disj φ' φ'' hφ'C hφ''C,
    coloringUnionOfCover_usesColourSet hφ'C hφ''C, ?_, ?_, ?_, ?_⟩
  · -- `β/5`-boundedness of the combined colouring
    intro c
    by_cases hc : c ∈ C'
    · rcases (AlphaBounded_iff_classVertexCount (β / 5) φ').mp hφ'b c with h1 | h1
      · left
        rw [ncard_colorClass_coloringUnionOfCover_left hφ'C hφ''C hc]
        exact h1
      · right
        rw [← classVertexCount_eq_FamilyVertexCount _ c]
        rw [classVertexCount_eq_of_classVertices_eq _
          (classVertices_coloringUnionOfCover_left hφ'C hφ''C hc)]
        exact h1
    · rcases (AlphaBounded_iff_classVertexCount (β / 5) φ'').mp hφ''b c with h1 | h1
      · left
        rw [ncard_colorClass_coloringUnionOfCover_right hφ'C hφ''C hc]
        exact h1
      · right
        rw [← classVertexCount_eq_FamilyVertexCount _ c]
        rw [classVertexCount_eq_of_classVertices_eq _
          (classVertices_coloringUnionOfCover_right hφ'C hφ''C hc)]
        exact h1
  · rw [Finset.card_union_of_disjoint hC'C''disj, hC'card, hC''card]
    have hb1 : ((⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ + ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ : ℕ) : ℝ) ≤
        (⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ : ℝ) := by exact_mod_cast hbudget
    have hb2 : (⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ : ℝ) ≤ (1 - 3 * σ / 2) * (n : ℝ) :=
      Nat.floor_le (by nlinarith [hσ32, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])
    linarith [hb1, hb2]
  · rw [Finset.card_union_of_disjoint hC'C''disj, hC'card, hC''card]
  · rw [Finset.disjoint_left]
    intro x hx hxM
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.disjoint_left.mp hC'disj) hx hxM
    · exact (Finset.disjoint_left.mp hC''disj) hx (Finset.mem_union.mpr (Or.inl hxM))



/-- Membership in the set of colours assigned to huge edges. -/
theorem mem_hugeColourSet {n : ℕ} {𝓗 A : Hypergraph (Fin n)} [Fintype A] {β : ℝ}
    {φ : A.Coloring (Fin n)} {c : Fin n} :
    c ∈ hugeColourSet 𝓗 A β φ ↔
      ∃ e : A, (e : Set (Fin n)) ∈ 𝓗.hugeEdges β ∧ φ.labels e = c := by
  rw [hugeColourSet]
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

theorem card_sdiff_ge {α : Type*} [DecidableEq α] (s t : Finset α) :
    s.card - t.card ≤ (s \ t).card := by
  have h := Finset.card_sdiff_add_card_inter s t
  have h2 : (s ∩ t).card ≤ t.card := Finset.card_le_card Finset.inter_subset_right
  omega

/-- `|s| ≤ |s \ t| + |t|` (natural-number form). -/
theorem card_le_card_sdiff_add {α : Type*} [DecidableEq α] (s t : Finset α) :
    s.card ≤ (s \ t).card + t.card := by
  have h := Finset.card_sdiff_add_card_inter s t
  have h2 : (s ∩ t).card ≤ t.card := Finset.card_le_card Finset.inter_subset_right
  omega

/-- **Membership in a colour class of the cross-combined colouring.**  An edge
belongs to the class of `c` iff it comes from the first part and is coloured
`c` there, or from the second part and is coloured `c` there. -/
theorem mem_colorClass_coloringUnionCross {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    {h₁ : 𝓖₁ ⊆ 𝓗} {h₂ : 𝓖₂ ⊆ 𝓗} {hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂}
    {hdisjG : Disjoint 𝓖₁ 𝓖₂} {φ₁ : 𝓖₁.Coloring (Fin n)} {φ₂ : 𝓖₂.Coloring (Fin n)}
    {hcross : ∀ (e₁ : 𝓖₁) (e₂ : 𝓖₂),
      (((e₁ : Set (Fin n)) ∩ (e₂ : Set (Fin n))).Nonempty) → φ₁.labels e₁ ≠ φ₂.labels e₂}
    (e : 𝓗) (c : Fin n) :
    e ∈ (coloringUnionCross h₁ h₂ hcover hdisjG φ₁ φ₂ hcross).colorClass c ↔
      (∃ he : (e : Set (Fin n)) ∈ 𝓖₁, (⟨(e : Set (Fin n)), he⟩ : 𝓖₁) ∈ φ₁.colorClass c) ∨
      (∃ he : (e : Set (Fin n)) ∈ 𝓖₂, (⟨(e : Set (Fin n)), he⟩ : 𝓖₂) ∈ φ₂.colorClass c) := by
  by_cases he : (e : Set (Fin n)) ∈ 𝓖₁
  · have hlab : (coloringUnionCross h₁ h₂ hcover hdisjG φ₁ φ₂ hcross).labels e =
        φ₁.labels ⟨(e : Set (Fin n)), he⟩ := by
      simp only [coloringUnionCross, unionLabelCross, dif_pos he]
    rw [mem_colorClass, hlab]
    constructor
    · intro h
      exact Or.inl ⟨he, by simpa [Hypergraph.Coloring.colorClass] using h⟩
    · rintro (⟨he', hcl⟩ | ⟨he', hcl⟩)
      · have hEq : (⟨(e : Set (Fin n)), he'⟩ : 𝓖₁) = ⟨(e : Set (Fin n)), he⟩ := Subtype.ext rfl
        rw [hEq] at hcl
        simpa [Hypergraph.Coloring.colorClass] using hcl
      · exact absurd he' ((Set.disjoint_left.mp hdisjG) he)
  · have hlab : (coloringUnionCross h₁ h₂ hcover hdisjG φ₁ φ₂ hcross).labels e =
        φ₂.labels ⟨(e : Set (Fin n)), (hcover (e : Set (Fin n)) e.2).resolve_left he⟩ := by
      simp only [coloringUnionCross, unionLabelCross, dif_neg he]
    rw [mem_colorClass, hlab]
    constructor
    · intro h
      exact Or.inr ⟨(hcover (e : Set (Fin n)) e.2).resolve_left he,
        by simpa [Hypergraph.Coloring.colorClass] using h⟩
    · rintro (⟨he', hcl⟩ | ⟨he', hcl⟩)
      · exact absurd he' he
      · have hEq : (⟨(e : Set (Fin n)), he'⟩ : 𝓖₂) =
            ⟨(e : Set (Fin n)), (hcover (e : Set (Fin n)) e.2).resolve_left he⟩ := Subtype.ext rfl
        rw [hEq] at hcl
        simpa [Hypergraph.Coloring.colorClass] using hcl


/-! ## The lists used for the `𝓗₂^good ∪ 𝓗₁^good` colouring (Case 2.1)

The colours `φ₁` assigns to the neighbours (in `𝓗₂^left ∖ 𝓗_med`) of an edge
`e` of `𝓗₂^good ∪ 𝓗₁^good` are *forbidden* for `e` (`case2Forb`); the list of
`e` is the extra colour set `C₁ ∪ C₂` minus `C_huge` (the colours assigned to
huge edges by `φ₁`) minus the forbidden colours (`case2List`). -/

/-- The colours assigned by `φ₁` to the edges of `𝓗₂^left ∖ 𝓗_med` meeting
`e`: the colours forbidden for `e` when it is coloured by `φ₂`. -/
def case2Forb (r₁ r₀ : ℕ) (𝓗 W₂ H₃ : Hypergraph (Fin n))
    [Fintype (case2Left r₁ r₀ 𝓗 W₂ H₃)]
    (φ₁ : (case2Left r₁ r₀ 𝓗 W₂ H₃).Coloring (Fin n)) (e : Set (Fin n)) : Finset (Fin n) := by
  classical
  exact ((Finset.univ : Finset (case2Left r₁ r₀ 𝓗 W₂ H₃)).filter
    (fun g : case2Left r₁ r₀ 𝓗 W₂ H₃ => (((g : Set (Fin n)) ∩ e).Nonempty))).image φ₁.labels

/-- The list of colours available for the edge `e` of
`𝓗₂^good ∪ 𝓗₁^good`: the extra colours `C₁ ∪ C₂` minus the colour set
`C_huge` of `φ₁` and minus the colours of the `φ₁`-neighbours of `e`. -/
def case2List (r₁ r₀ : ℕ) (𝓗 W₂ H₃ : Hypergraph (Fin n))
    [Fintype (case2Left r₁ r₀ 𝓗 W₂ H₃)]
    (φ₁ : (case2Left r₁ r₀ 𝓗 W₂ H₃).Coloring (Fin n)) (β : ℝ) (C₁ C₂ : Finset (Fin n))
    (e : Set (Fin n)) : Finset (Fin n) :=
  ((C₁ ∪ C₂) \ hugeColourSet 𝓗 (case2Left r₁ r₀ 𝓗 W₂ H₃) β φ₁) \
    case2Forb r₁ r₀ 𝓗 W₂ H₃ φ₁ e

theorem mem_case2Forb {n r₁ r₀ : ℕ} {𝓗 W₂ H₃ : Hypergraph (Fin n)}
    [Fintype (case2Left r₁ r₀ 𝓗 W₂ H₃)]
    {φ₁ : (case2Left r₁ r₀ 𝓗 W₂ H₃).Coloring (Fin n)} {e : Set (Fin n)} {c : Fin n} :
    c ∈ case2Forb r₁ r₀ 𝓗 W₂ H₃ φ₁ e ↔
      ∃ g : case2Left r₁ r₀ 𝓗 W₂ H₃, (((g : Set (Fin n)) ∩ e).Nonempty) ∧ φ₁.labels g = c := by
  rw [case2Forb]
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_case2List {n r₁ r₀ : ℕ} {𝓗 W₂ H₃ : Hypergraph (Fin n)}
    [Fintype (case2Left r₁ r₀ 𝓗 W₂ H₃)]
    {φ₁ : (case2Left r₁ r₀ 𝓗 W₂ H₃).Coloring (Fin n)} {β : ℝ} {C₁ C₂ : Finset (Fin n)}
    {e : Set (Fin n)} {c : Fin n} :
    c ∈ case2List r₁ r₀ 𝓗 W₂ H₃ φ₁ β C₁ C₂ e ↔
      (c ∈ C₁ ∪ C₂ ∧ c ∉ hugeColourSet 𝓗 (case2Left r₁ r₀ 𝓗 W₂ H₃) β φ₁) ∧
        c ∉ case2Forb r₁ r₀ 𝓗 W₂ H₃ φ₁ e := by
  simp only [case2List, Finset.mem_sdiff]

/-- **The list-size bound for the `φ₂` construction.**  The lists
`case2List` are large enough for Proposition 6.9 with `α₁ = σ/4`: the
forbidden colours number at most `|N_{𝓗₂^left}(e)|`, the colour set `C_huge`
has at most `32/β²` colours, and the forward-degree-sum hypothesis `hsum`
together with the slack `(σ/4)n ≥ 1 + 32/β²` absorbs everything. -/
theorem case2_list_bound {n r₁ r₀ : ℕ} {β σ : ℝ} {K : ℕ}
    {𝓗 W₂ H₃ Good₁ Good₂ : Hypergraph (Fin n)} [Fintype (case2Left r₁ r₀ 𝓗 W₂ H₃)]
    {C₁ C₂ : Finset (Fin n)} {φ₁ : (case2Left r₁ r₀ 𝓗 W₂ H₃).Coloring (Fin n)}
    (hβ : 0 < β) (hβc : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n) (hlin : 𝓗.IsLinear)
    (hC₁₂ : (C₁ ∪ C₂).card = K)
    (hK : (1 - 3 * σ / 2) * (n : ℝ) - 1 ≤ (K : ℝ))
    (hslack : 1 + 32 / β ^ 2 ≤ (σ / 4) * (n : ℝ))
    {kB : ℕ} (ord' : (case2Right r₁ r₀ 𝓗 Good₁ Good₂) ≃ Fin kB)
    (hsum : ∀ e : case2Right r₁ r₀ 𝓗 Good₁ Good₂,
      ((precedingDegree (case2Right r₁ r₀ 𝓗 Good₁ Good₂) ord' e : ℝ) +
        (Nat.card {g : case2Left r₁ r₀ 𝓗 W₂ H₃ //
          (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℝ)) ≤ (1 - 2 * σ) * (n : ℝ)) :
    ∀ e : case2Right r₁ r₀ 𝓗 Good₁ Good₂,
      ((precedingDegree (case2Right r₁ r₀ 𝓗 Good₁ Good₂) ord' e : ℝ) + (σ / 4) * (n : ℝ)) ≤
        ((case2List r₁ r₀ 𝓗 W₂ H₃ φ₁ β C₁ C₂ (e : Set (Fin n))).card : ℝ) := by
  classical
  intro e
  set N : ℕ := Nat.card {g : case2Left r₁ r₀ 𝓗 W₂ H₃ //
    (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} with hNdef
  -- the forbidden colours are at most the neighbours
  have hforb : (case2Forb r₁ r₀ 𝓗 W₂ H₃ φ₁ (e : Set (Fin n))).card ≤ N := by
    have h1 : (case2Forb r₁ r₀ 𝓗 W₂ H₃ φ₁ (e : Set (Fin n))).card ≤
        ((Finset.univ : Finset (case2Left r₁ r₀ 𝓗 W₂ H₃)).filter
          (fun g : case2Left r₁ r₀ 𝓗 W₂ H₃ =>
            (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty))).card := by
      rw [case2Forb]
      exact Finset.card_image_le
    rw [hNdef, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact h1
  -- the colours of huge edges are few
  have hchuge : ((hugeColourSet 𝓗 (case2Left r₁ r₀ 𝓗 W₂ H₃) β φ₁).card : ℝ) ≤ 32 / β ^ 2 :=
    card_hugeColours_le φ₁ hlin hβ hβc hn1
  -- the list-cardinality chain
  have hchain : (C₁ ∪ C₂).card ≤
      (case2List r₁ r₀ 𝓗 W₂ H₃ φ₁ β C₁ C₂ (e : Set (Fin n))).card +
        (hugeColourSet 𝓗 (case2Left r₁ r₀ 𝓗 W₂ H₃) β φ₁).card +
        (case2Forb r₁ r₀ 𝓗 W₂ H₃ φ₁ (e : Set (Fin n))).card := by
    have h1 := card_le_card_sdiff_add (C₁ ∪ C₂)
      (hugeColourSet 𝓗 (case2Left r₁ r₀ 𝓗 W₂ H₃) β φ₁)
    have h2 := card_le_card_sdiff_add
      ((C₁ ∪ C₂) \ hugeColourSet 𝓗 (case2Left r₁ r₀ 𝓗 W₂ H₃) β φ₁)
      (case2Forb r₁ r₀ 𝓗 W₂ H₃ φ₁ (e : Set (Fin n)))
    simp only [case2List]
    omega
  have hchain' : ((C₁ ∪ C₂).card : ℝ) ≤
      ((case2List r₁ r₀ 𝓗 W₂ H₃ φ₁ β C₁ C₂ (e : Set (Fin n))).card : ℝ) +
        ((hugeColourSet 𝓗 (case2Left r₁ r₀ 𝓗 W₂ H₃) β φ₁).card : ℝ) +
        ((case2Forb r₁ r₀ 𝓗 W₂ H₃ φ₁ (e : Set (Fin n))).card : ℝ) := by
    exact_mod_cast hchain
  have hcast : ((C₁ ∪ C₂).card : ℝ) = (K : ℝ) := by rw [hC₁₂]
  have hforb' : ((case2Forb r₁ r₀ 𝓗 W₂ H₃ φ₁ (e : Set (Fin n))).card : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hforb
  have hsum' := hsum e
  rw [hNdef] at hforb'
  linarith [hchain', hcast, hchuge, hforb', hsum', hK, hslack]



/-! ## Counting helpers for the forward-degree-sum bound -/

/-- Monotonicity of `Nat.card` of a subtype with respect to the property. -/
theorem natCard_subtype_mono {α : Type*} [Finite α] {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    Nat.card {a // P a} ≤ Nat.card {a // Q a} := by
  classical
  refine Nat.card_le_card_of_injective (fun x => (⟨x.1, h x.1 x.2⟩ : {a // Q a})) ?_
  intro a b hab
  exact Subtype.ext (congrArg (fun x : {a // Q a} => x.1) hab)

/-- Monotonicity of the neighbour count under enlarging the family (the
predicate may depend on the underlying edge). -/
theorem natCard_family_mono {n : ℕ} {𝓖' 𝓖 : Hypergraph (Fin n)} (hsub : 𝓖' ⊆ 𝓖)
    (P : Set (Fin n) → Prop) :
    Nat.card {f : 𝓖' // P (f : Set (Fin n))} ≤ Nat.card {f : 𝓖 // P (f : Set (Fin n))} :=
  Nat.card_le_card_of_injective
    (fun x => ⟨⟨(x.1 : Set (Fin n)), hsub x.1.2⟩, x.2⟩)
    (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun x : 𝓖 => (x : Set (Fin n)))
      (congrArg Subtype.val hab))))

/-- **The neighbour count of a disjoint cover is the sum of the parts'.**  For
`𝓖 = 𝓖₁ ⊔ 𝓖₂`, the edges of `𝓖` meeting `e` are the disjoint union of those of
`𝓖₁` and those of `𝓖₂`: the sum of the two counts is at most the whole. -/
theorem natCard_interFiber_add_le {n : ℕ} {𝓖 𝓖₁ 𝓖₂ : Hypergraph (Fin n)}
    (h₁ : 𝓖₁ ⊆ 𝓖) (h₂ : 𝓖₂ ⊆ 𝓖) (hdisj : Disjoint 𝓖₁ 𝓖₂) (e : Set (Fin n)) :
    Nat.card {f : 𝓖₁ // (((f : Set (Fin n)) ∩ e).Nonempty)} +
      Nat.card {f : 𝓖₂ // (((f : Set (Fin n)) ∩ e).Nonempty)} ≤
      Nat.card {f : 𝓖 // (((f : Set (Fin n)) ∩ e).Nonempty)} := by
  classical
  have hne : ∀ (f : 𝓖₁) (g : 𝓖₂),
      (⟨(f : Set (Fin n)), h₁ f.2⟩ : 𝓖) ≠ ⟨(g : Set (Fin n)), h₂ g.2⟩ := by
    intro f g hfg
    have h : (f : Set (Fin n)) = (g : Set (Fin n)) :=
      congrArg (fun x : 𝓖 => (x : Set (Fin n))) hfg
    exact (Set.disjoint_left.mp hdisj) (h ▸ f.2) g.2
  have hΦ : Function.Injective
      (fun z : {f : 𝓖₁ // (((f : Set (Fin n)) ∩ e).Nonempty)} ⊕
          {f : 𝓖₂ // (((f : Set (Fin n)) ∩ e).Nonempty)} =>
        match z with
        | Sum.inl f => (⟨⟨(f.1 : Set (Fin n)), h₁ f.1.2⟩, f.2⟩ :
            {g : 𝓖 // (((g : Set (Fin n)) ∩ e).Nonempty)})
        | Sum.inr f => (⟨⟨(f.1 : Set (Fin n)), h₂ f.1.2⟩, f.2⟩ :
            {g : 𝓖 // (((g : Set (Fin n)) ∩ e).Nonempty)})) := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (Subtype.ext (Subtype.ext
        (congrArg (fun x : 𝓖 => (x : Set (Fin n))) (congrArg Subtype.val hab))))
    · exact absurd (congrArg (fun x : {g : 𝓖 // _} => (x.1 : 𝓖)) hab) (hne a.1 b.1)
    · exact absurd (congrArg (fun x : {g : 𝓖 // _} => (x.1 : 𝓖)) hab).symm (hne b.1 a.1)
    · exact congrArg Sum.inr (Subtype.ext (Subtype.ext
        (congrArg (fun x : 𝓖 => (x : Set (Fin n))) (congrArg Subtype.val hab))))
  have h := Nat.card_le_card_of_injective _ hΦ
  rwa [Nat.card_sum] at h

/-- **Splitting the preceding degree along a segmented cover.**  If `𝓖₁` is an
initial segment of an ordering `ord` of `𝓖` (every edge of `𝓖₁` precedes every
edge of `𝓖₂`), then for `e ∈ 𝓖₂` the preceding degree of `e` in `𝓖` is at
least the number of its neighbours in `𝓖₁` plus the number of its preceding
neighbours inside `𝓖₂` — the counting behind the paper's
(reordering-goodness1)/(reordering-goodness2). -/

theorem precedingDegree_ge_fiber_add {n : ℕ} {𝓖 𝓖₁ 𝓖₂ : Hypergraph (Fin n)}
    {k : ℕ} (ord : 𝓖 ≃ Fin k) (h₁ : 𝓖₁ ⊆ 𝓖) (h₂ : 𝓖₂ ⊆ 𝓖)
    (hcover : ∀ e ∈ 𝓖, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂) (hdisj : Disjoint 𝓖₁ 𝓖₂)
    (hseg : ∀ f : 𝓖₁, ∀ u : 𝓖₂, (ord ⟨(f : Set (Fin n)), h₁ f.2⟩ : ℕ) ≤
      (ord ⟨(u : Set (Fin n)), h₂ u.2⟩ : ℕ))
    (e : 𝓖₂) :
    Nat.card {f : 𝓖₁ // (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} +
      Nat.card {f : 𝓖₂ // f ≠ e ∧
        (ord ⟨(f : Set (Fin n)), h₂ f.2⟩ : ℕ) ≤ (ord ⟨(e : Set (Fin n)), h₂ e.2⟩ : ℕ) ∧
        (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} ≤
      precedingDegree 𝓖 ord ⟨(e : Set (Fin n)), h₂ e.2⟩ := by
  classical
  let i₁ : 𝓖₁ → 𝓖 := fun f => ⟨(f : Set (Fin n)), h₁ f.2⟩
  let i₂ : 𝓖₂ → 𝓖 := fun f => ⟨(f : Set (Fin n)), h₂ f.2⟩
  have vi₁ : ∀ f : 𝓖₁, ((i₁ f : 𝓖) : Set (Fin n)) = (f : Set (Fin n)) := fun _ => rfl
  have vi₂ : ∀ f : 𝓖₂, ((i₂ f : 𝓖) : Set (Fin n)) = (f : Set (Fin n)) := fun _ => rfl
  have hval : ((⟨(e : Set (Fin n)), h₂ e.2⟩ : 𝓖) : Set (Fin n)) = ((i₂ e : 𝓖) : Set (Fin n)) :=
    rfl
  have hi₁ : Function.Injective i₁ := by
    intro a b hab
    have h : (a : Set (Fin n)) = (b : Set (Fin n)) := by
      have := congrArg (fun x : 𝓖 => (x : Set (Fin n))) hab
      simpa only [vi₁ a, vi₁ b] using this
    exact Subtype.ext h
  have hi₂ : Function.Injective i₂ := by
    intro a b hab
    have h : (a : Set (Fin n)) = (b : Set (Fin n)) := by
      have := congrArg (fun x : 𝓖 => (x : Set (Fin n))) hab
      simpa only [vi₂ a, vi₂ b] using this
    exact Subtype.ext h
  have hne : ∀ (f : 𝓖₁) (g : 𝓖₂), i₁ f ≠ i₂ g := by
    intro f g hfg
    have h : (f : Set (Fin n)) = (g : Set (Fin n)) := by
      have := congrArg (fun x : 𝓖 => (x : Set (Fin n))) hfg
      simpa only [vi₁ f, vi₂ g] using this
    exact (Set.disjoint_left.mp hdisj) (h ▸ f.2) g.2
  let Φ : {f : 𝓖₁ // (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} ⊕
      {f : 𝓖₂ // f ≠ e ∧
        (ord ⟨(f : Set (Fin n)), h₂ f.2⟩ : ℕ) ≤ (ord ⟨(e : Set (Fin n)), h₂ e.2⟩ : ℕ) ∧
        (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} →
      {g : 𝓖 // g ≠ i₂ e ∧ ord g ≤ ord (i₂ e) ∧
        (((g : Set (Fin n)) ∩ ((i₂ e : 𝓖) : Set (Fin n))).Nonempty)} :=
    fun z => match z with
      | Sum.inl f => ⟨i₁ f.1, fun hc => by
          have h : (f.1 : Set (Fin n)) = (e : Set (Fin n)) := by
            have := congrArg (fun x : 𝓖 => (x : Set (Fin n))) hc
            simpa only [vi₁ f.1, vi₂ e] using this
          exact (Set.disjoint_left.mp hdisj) (h ▸ f.1.2) e.2,
          hseg f.1 e, by simpa only [vi₁ f.1, vi₂ e] using f.2⟩
      | Sum.inr f => ⟨i₂ f.1, fun hc => f.2.1 (hi₂ hc), f.2.2.1,
          by simpa only [vi₂ f.1, vi₂ e] using f.2.2.2⟩
  have hΦ : Function.Injective Φ := by
    intro a b hab
    have hv : (Φ a : 𝓖) = (Φ b : 𝓖) := congrArg Subtype.val hab
    rcases a with a | a <;> rcases b with b | b
    · have h : i₁ a.1 = i₁ b.1 := hv
      exact congrArg Sum.inl (Subtype.ext (hi₁ h))
    · exact absurd hv (hne a.1 b.1)
    · exact absurd hv.symm (hne b.1 a.1)
    · have h : i₂ a.1 = i₂ b.1 := hv
      exact congrArg Sum.inr (Subtype.ext (hi₂ h))
  have h := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_sum] at h
  rw [precedingDegree_eq_natCard]
  exact h


/-- **Two order-equivalent filter counts agree.**  If two `ℕ`-valued rankings
of `α` have the same comparison relation, then the counts of the elements
below a fixed `x` (excluding `x`, and restricted by a predicate `P`) agree.
This is the `Nat.card` bridge needed when passing from a restricted ordering
back to the ordering it restricts. -/
theorem natCard_ord_filter_eq {α : Type*} [Finite α] {ρ ρ' : α → ℕ}
    (h : ∀ a b : α, ρ' a ≤ ρ' b ↔ ρ a ≤ ρ b) (x : α) (P : α → Prop) :
    Nat.card {a // a ≠ x ∧ ρ' a ≤ ρ' x ∧ P a} = Nat.card {a // a ≠ x ∧ ρ a ≤ ρ x ∧ P a} := by
  refine le_antisymm ?_ ?_
  · exact natCard_subtype_mono (fun a ha => ⟨ha.1, (h a x).mp ha.2.1, ha.2.2⟩)
  · exact natCard_subtype_mono (fun a ha => ⟨ha.1, (h a x).mpr ha.2.1, ha.2.2⟩)

/-- The number of neighbours of an edge `e` of `𝓗₂^good` that precede it
inside `𝓗₂^good`, counted with respect to the App-2 ordering `ord₂` of
`𝓗₁^left`. -/
def case2Pred₂ {n : ℕ} {Left₁ : Hypergraph (Fin n)} {k : ℕ} (ord₂ : Left₁ ≃ Fin k)
    (Good₂ : Hypergraph (Fin n)) (hG₂sub : Good₂ ⊆ Left₁) (e : Good₂) : ℕ :=
  Nat.card {f : Good₂ // f ≠ e ∧
    (ord₂ ⟨(f : Set (Fin n)), hG₂sub f.2⟩ : ℕ) ≤
      (ord₂ ⟨(e : Set (Fin n)), hG₂sub e.2⟩ : ℕ) ∧
    (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)}

/-- The preceding degree in a *restricted* ordering equals the
`ord₂`-count `case2Pred₂`: this is the conversion from the restricted App-2
ordering of `𝓗₂^good` back to the ordering `ord₂` of `𝓗₁^left` that the
forward-degree-sum bound needs. -/
theorem case2_pred₂_eq {n : ℕ} {Left₁ Good₂ : Hypergraph (Fin n)} {k₂ : ℕ}
    (ord₂ : Left₁ ≃ Fin k₂) (hG₂sub : Good₂ ⊆ Left₁) {k : ℕ} (ordG₂ : Good₂ ≃ Fin k)
    (hrank : ∀ a b : Good₂, (ordG₂ a : ℕ) ≤ (ordG₂ b : ℕ) ↔
      (ord₂ ⟨(a : Set (Fin n)), hG₂sub a.2⟩ : ℕ) ≤
        (ord₂ ⟨(b : Set (Fin n)), hG₂sub b.2⟩ : ℕ))
    (e : Good₂) :
    precedingDegree Good₂ ordG₂ e = case2Pred₂ ord₂ Good₂ hG₂sub e := by
  rw [precedingDegree_eq_natCard, case2Pred₂]
  exact natCard_ord_filter_eq hrank e _

/-- The same conversion for the App-1 ordering: the number of neighbours of
an edge `e` of `𝓗₁^good` preceding it inside `𝓗₁^good`, counted w.r.t. the
App-1 ordering `ord₁` of `𝓗' = 𝓗 ∖ 𝓗_huge`. -/
def case2Pred₁ {n : ℕ} {𝓗' : Hypergraph (Fin n)} {k : ℕ} (ord₁ : 𝓗' ≃ Fin k)
    (Good₁ : Hypergraph (Fin n)) (hG₁sub : Good₁ ⊆ 𝓗') (e : Good₁) : ℕ :=
  Nat.card {f : Good₁ // f ≠ e ∧
    (ord₁ ⟨(f : Set (Fin n)), hG₁sub f.2⟩ : ℕ) ≤
      (ord₁ ⟨(e : Set (Fin n)), hG₁sub e.2⟩ : ℕ) ∧
    (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)}

theorem case2_pred₁_eq {n : ℕ} {𝓗' Good₁ : Hypergraph (Fin n)} {k₁ : ℕ}
    (ord₁ : 𝓗' ≃ Fin k₁) (hG₁sub : Good₁ ⊆ 𝓗') {k : ℕ} (ordG₁ : Good₁ ≃ Fin k)
    (hrank : ∀ a b : Good₁, (ordG₁ a : ℕ) ≤ (ordG₁ b : ℕ) ↔
      (ord₁ ⟨(a : Set (Fin n)), hG₁sub a.2⟩ : ℕ) ≤
        (ord₁ ⟨(b : Set (Fin n)), hG₁sub b.2⟩ : ℕ))
    (e : Good₁) :
    precedingDegree Good₁ ordG₁ e = case2Pred₁ ord₁ Good₁ hG₁sub e := by
  rw [precedingDegree_eq_natCard, case2Pred₁]
  exact natCard_ord_filter_eq hrank e _


/-- **The forward-degree-sum bound on `𝓗₂^good ∖ 𝓗_med`.**  For an edge `e` of
the first block, the preceding degree in the concatenated ordering is at most
`case2Pred₂`, which together with the App-2 split
`|N_{Left₂}(e)| + d⫯_{𝓗₂^good}(e) ≤ d⫯_{𝓗₁^left}(e) ≤ (1−3σ)n`
(`precedingDegree_ge_fiber_add` + `hdeg₂`) and the neighbour-count split
`hNsplit` gives `d⫯(e) + |N_{𝓗₂^left}(e)| ≤ (1−2σ)n`. -/
theorem case2_fwddeg_good₂ {n r₁ r₀ : ℕ} {β γ₂ σ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)} {k₂ m₂ m₂' m₁' : ℕ}
    (ord₂ : Left₁ ≃ Fin k₂) (hG₂sub : Good₂ ⊆ Left₁) (ordG₂ : Good₂ ≃ Fin m₂)
    (hrankG₂ : ∀ a b : Good₂, (ordG₂ a : ℕ) ≤ (ordG₂ b : ℕ) ↔
      (ord₂ ⟨(a : Set (Fin n)), hG₂sub a.2⟩ : ℕ) ≤
        (ord₂ ⟨(b : Set (Fin n)), hG₂sub b.2⟩ : ℕ))
    (ordG₂m : case2Good₂med r₁ r₀ 𝓗 Good₂ ≃ Fin m₂')
    (hdegG₂m : ∀ e : case2Good₂med r₁ r₀ 𝓗 Good₂,
      precedingDegree (case2Good₂med r₁ r₀ 𝓗 Good₂) ordG₂m e ≤
        precedingDegree Good₂ ordG₂ ⟨(e : Set (Fin n)), e.2.1⟩)
    (ordG₁m : case2Good₁med r₁ r₀ 𝓗 Good₁ ≃ Fin m₁')
    (hcovR : case2Good₂med r₁ r₀ 𝓗 Good₂ ∪ case2Good₁med r₁ r₀ 𝓗 Good₁ =
      case2Right r₁ r₀ 𝓗 Good₁ Good₂)
    (hdisjR : Disjoint (case2Good₂med r₁ r₀ 𝓗 Good₂) (case2Good₁med r₁ r₀ 𝓗 Good₁))
    (hL₂sub : Left₂ ⊆ Left₁) (hpart₂ : Good₂ ∪ Left₂ = Left₁)
    (hdisj₂ : Disjoint Good₂ Left₂)
    (hseg₂ : ∀ f u : Left₁, (f : Set (Fin n)) ∈ Left₂ → (u : Set (Fin n)) ∈ Good₂ →
      (ord₂ f : ℕ) ≤ (ord₂ u : ℕ))
    (hdeg₂ : ∀ e : Left₁, (e : Set (Fin n)) ∈ Good₂ →
      (precedingDegree Left₁ ord₂ e : ℝ) ≤ (1 - 3 * σ) * (n : ℝ))
    (hNsplit : ∀ e : case2Right r₁ r₀ 𝓗 Good₁ Good₂,
      ((Nat.card {g : case2Left r₁ r₀ 𝓗 W₂ H₃ //
          (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) ≤
        (Nat.card {g : Left₂ // (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) +
          32 / β ^ 2)
    (hσn : 32 / β ^ 2 ≤ σ * (n : ℝ)) :
    ∀ (e : case2Right r₁ r₀ 𝓗 Good₁ Good₂)
      (he : (e : Set (Fin n)) ∈ case2Good₂med r₁ r₀ 𝓗 Good₂),
      ((precedingDegree (case2Right r₁ r₀ 𝓗 Good₁ Good₂)
          (concatOrderingS hcovR hdisjR ordG₂m ordG₁m) e : ℝ) +
        (Nat.card {g : case2Left r₁ r₀ 𝓗 W₂ H₃ //
          (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℝ)) ≤
        (1 - 2 * σ) * (n : ℝ) := by
  classical
  intro e he
  have he' : (e : Set (Fin n)) ∈ Good₂ \ 𝓗.medEdges r₁ r₀ := by
    simpa only [case2Good₂med] using he
  have heG₂ : (e : Set (Fin n)) ∈ Good₂ := he'.1
  have hd₁ : precedingDegree (case2Right r₁ r₀ 𝓗 Good₁ Good₂)
      (concatOrderingS hcovR hdisjR ordG₂m ordG₁m) e ≤
      precedingDegree (case2Good₂med r₁ r₀ 𝓗 Good₂) ordG₂m ⟨(e : Set (Fin n)), he⟩ :=
    precedingDegree_concatOrderingS_of_mem hcovR hdisjR ordG₂m ordG₁m he
  have hd₂ : precedingDegree (case2Good₂med r₁ r₀ 𝓗 Good₂) ordG₂m ⟨(e : Set (Fin n)), he⟩ ≤
      precedingDegree Good₂ ordG₂ ⟨(e : Set (Fin n)), heG₂⟩ := hdegG₂m _
  have hd₃ : (precedingDegree Good₂ ordG₂ ⟨(e : Set (Fin n)), heG₂⟩ : ℝ) ≤
      (case2Pred₂ ord₂ Good₂ hG₂sub ⟨(e : Set (Fin n)), heG₂⟩ : ℝ) := by
    rw [case2_pred₂_eq ord₂ hG₂sub ordG₂ hrankG₂]
  have hd₄ : (precedingDegree (case2Right r₁ r₀ 𝓗 Good₁ Good₂)
        (concatOrderingS hcovR hdisjR ordG₂m ordG₁m) e : ℝ) ≤
      (case2Pred₂ ord₂ Good₂ hG₂sub ⟨(e : Set (Fin n)), heG₂⟩ : ℝ) :=
    le_trans (by exact_mod_cast le_trans hd₁ hd₂) hd₃
  have hfib := precedingDegree_ge_fiber_add (𝓖 := Left₁) ord₂ hL₂sub hG₂sub
    (by
      intro x hx
      have hx' : x ∈ Good₂ ∨ x ∈ Left₂ := by
        have h := hpart₂ ▸ hx
        simpa only [Set.mem_union] using h
      exact hx'.symm)
    hdisj₂.symm
    (by
      intro f u
      exact hseg₂ ⟨(f : Set (Fin n)), hL₂sub f.2⟩ ⟨(u : Set (Fin n)), hG₂sub u.2⟩ f.2 u.2)
    ⟨(e : Set (Fin n)), heG₂⟩
  have hfib' : ((Nat.card {f : Left₂ // (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) +
      (case2Pred₂ ord₂ Good₂ hG₂sub ⟨(e : Set (Fin n)), heG₂⟩ : ℝ) ≤
      (precedingDegree Left₁ ord₂ ⟨(e : Set (Fin n)), hG₂sub heG₂⟩ : ℝ) := by
    exact_mod_cast hfib
  have hdeg₂' : (precedingDegree Left₁ ord₂ ⟨(e : Set (Fin n)), hG₂sub heG₂⟩ : ℝ) ≤
      (1 - 3 * σ) * (n : ℝ) := hdeg₂ _ heG₂
  have hN := hNsplit e
  linarith [hd₄, hfib', hdeg₂', hN, hσn]


/-- **The forward-degree-sum bound on `𝓗₁^good ∖ 𝓗_med`** (the mirror of
`case2_fwddeg_good₂`).  For an edge `e` of the second block, the preceding
degree in the concatenated ordering is at most
`|N_{𝓗₂^good}(e)| + case2Pred₁`, and with the App-1 split
`|N_{𝓗₁^left}(e)| + d⫯_{𝓗₁^good}(e) ≤ d⫯_{𝓗'}(e) ≤ γ₂n/3`
(`precedingDegree_ge_fiber_add` + `hdeg₁`), the additivity
`|N_{𝓗₂^good}(e)| + |N_{Left₂}(e)| ≤ |N_{𝓗₁^left}(e)|`
(`natCard_interFiber_add_le`) and the neighbour-count split `hNsplit`, we get
`d⫯(e) + |N_{𝓗₂^left}(e)| ≤ (1−2σ)n`. -/
theorem case2_fwddeg_good₁ {n r₁ r₀ : ℕ} {β γ₂ σ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)} {k₁ m₁ m₁' m₂' : ℕ}
    (ord₁ : nonHuge 𝓗 β ≃ Fin k₁) (hG₁sub : Good₁ ⊆ nonHuge 𝓗 β) (ordG₁ : Good₁ ≃ Fin m₁)
    (hrankG₁ : ∀ a b : Good₁, (ordG₁ a : ℕ) ≤ (ordG₁ b : ℕ) ↔
      (ord₁ ⟨(a : Set (Fin n)), hG₁sub a.2⟩ : ℕ) ≤
        (ord₁ ⟨(b : Set (Fin n)), hG₁sub b.2⟩ : ℕ))
    (ordG₁m : case2Good₁med r₁ r₀ 𝓗 Good₁ ≃ Fin m₁')
    (hdegG₁m : ∀ e : case2Good₁med r₁ r₀ 𝓗 Good₁,
      precedingDegree (case2Good₁med r₁ r₀ 𝓗 Good₁) ordG₁m e ≤
        precedingDegree Good₁ ordG₁ ⟨(e : Set (Fin n)), e.2.1⟩)
    (ordG₂m : case2Good₂med r₁ r₀ 𝓗 Good₂ ≃ Fin m₂')
    (hcovR : case2Good₂med r₁ r₀ 𝓗 Good₂ ∪ case2Good₁med r₁ r₀ 𝓗 Good₁ =
      case2Right r₁ r₀ 𝓗 Good₁ Good₂)
    (hdisjR : Disjoint (case2Good₂med r₁ r₀ 𝓗 Good₂) (case2Good₁med r₁ r₀ 𝓗 Good₁))
    (hL₁sub : Left₁ ⊆ nonHuge 𝓗 β) (hpart₁ : Good₁ ∪ Left₁ = nonHuge 𝓗 β)
    (hdisj₁ : Disjoint Good₁ Left₁)
    (hG₂sub : Good₂ ⊆ Left₁) (hL₂sub : Left₂ ⊆ Left₁)
    (hdisj₂ : Disjoint Good₂ Left₂)
    (hseg₁ : ∀ f u : nonHuge 𝓗 β, (f : Set (Fin n)) ∈ Left₁ → (u : Set (Fin n)) ∈ Good₁ →
      (ord₁ f : ℕ) ≤ (ord₁ u : ℕ))
    (hdeg₁ : ∀ e : nonHuge 𝓗 β, (e : Set (Fin n)) ∈ Good₁ →
      (precedingDegree (nonHuge 𝓗 β) ord₁ e : ℝ) ≤ (γ₂ / 3) * (n : ℝ))
    (hNsplit : ∀ e : case2Right r₁ r₀ 𝓗 Good₁ Good₂,
      ((Nat.card {g : case2Left r₁ r₀ 𝓗 W₂ H₃ //
          (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) ≤
        (Nat.card {g : Left₂ // (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) +
          32 / β ^ 2)
    (hγm : (γ₂ / 3) * (n : ℝ) + 32 / β ^ 2 ≤ (1 - 2 * σ) * (n : ℝ)) :
    ∀ (e : case2Right r₁ r₀ 𝓗 Good₁ Good₂)
      (he : (e : Set (Fin n)) ∈ case2Good₁med r₁ r₀ 𝓗 Good₁),
      ((precedingDegree (case2Right r₁ r₀ 𝓗 Good₁ Good₂)
          (concatOrderingS hcovR hdisjR ordG₂m ordG₁m) e : ℝ) +
        (Nat.card {g : case2Left r₁ r₀ 𝓗 W₂ H₃ //
          (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℝ)) ≤
        (1 - 2 * σ) * (n : ℝ) := by
  classical
  intro e he
  have he' : (e : Set (Fin n)) ∈ Good₁ \ 𝓗.medEdges r₁ r₀ := by
    simpa only [case2Good₁med] using he
  have heG₁ : (e : Set (Fin n)) ∈ Good₁ := he'.1
  have hnot₂ : (e : Set (Fin n)) ∉ case2Good₂med r₁ r₀ 𝓗 Good₂ :=
    fun h => (Set.disjoint_left.mp hdisjR) h he
  have hd₁ := precedingDegree_concatOrderingS_of_notMem hcovR hdisjR ordG₂m ordG₁m hnot₂
  have hd₂ : Nat.card {f : case2Good₂med r₁ r₀ 𝓗 Good₂ //
        (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} ≤
      Nat.card {f : Good₂ // (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} :=
    natCard_family_mono (𝓖' := case2Good₂med r₁ r₀ 𝓗 Good₂) (𝓖 := Good₂) Set.sdiff_subset
      (fun f : Set (Fin n) => (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty))
  have hd₃ : precedingDegree (case2Good₁med r₁ r₀ 𝓗 Good₁) ordG₁m
        ⟨(e : Set (Fin n)), mem_right_of_cover hcovR e.2 hnot₂⟩ ≤
      precedingDegree Good₁ ordG₁ ⟨(e : Set (Fin n)), heG₁⟩ := hdegG₁m _
  have hd₄ : (precedingDegree Good₁ ordG₁ ⟨(e : Set (Fin n)), heG₁⟩ : ℝ) ≤
      (case2Pred₁ ord₁ Good₁ hG₁sub ⟨(e : Set (Fin n)), heG₁⟩ : ℝ) := by
    rw [case2_pred₁_eq ord₁ hG₁sub ordG₁ hrankG₁]
  have hr : (precedingDegree (case2Right r₁ r₀ 𝓗 Good₁ Good₂)
      (concatOrderingS hcovR hdisjR ordG₂m ordG₁m) e : ℝ) ≤
      (Nat.card {f : Good₂ // (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℝ) +
      (case2Pred₁ ord₁ Good₁ hG₁sub ⟨(e : Set (Fin n)), heG₁⟩ : ℝ) := by
    have h : precedingDegree (case2Right r₁ r₀ 𝓗 Good₁ Good₂)
        (concatOrderingS hcovR hdisjR ordG₂m ordG₁m) e ≤
        Nat.card {f : Good₂ // (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} +
          precedingDegree Good₁ ordG₁ ⟨(e : Set (Fin n)), heG₁⟩ :=
      le_trans hd₁ (add_le_add (le_trans hd₂ le_rfl) (le_trans hd₃ le_rfl))
    have hR : (precedingDegree (case2Right r₁ r₀ 𝓗 Good₁ Good₂)
        (concatOrderingS hcovR hdisjR ordG₂m ordG₁m) e : ℝ) ≤
        (Nat.card {f : Good₂ // (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℝ) +
        (precedingDegree Good₁ ordG₁ ⟨(e : Set (Fin n)), heG₁⟩ : ℝ) := by
      exact_mod_cast h
    exact le_trans hR (add_le_add le_rfl hd₄)
  have hfib := precedingDegree_ge_fiber_add (𝓖 := nonHuge 𝓗 β) ord₁ hL₁sub hG₁sub
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
    ⟨(e : Set (Fin n)), heG₁⟩
  have hfib' : ((Nat.card {f : Left₁ // (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) +
      (case2Pred₁ ord₁ Good₁ hG₁sub ⟨(e : Set (Fin n)), heG₁⟩ : ℝ) ≤
      (precedingDegree (nonHuge 𝓗 β) ord₁ ⟨(e : Set (Fin n)), hG₁sub heG₁⟩ : ℝ) := by
    exact_mod_cast hfib
  have hdeg₁' : (precedingDegree (nonHuge 𝓗 β) ord₁ ⟨(e : Set (Fin n)), hG₁sub heG₁⟩ : ℝ) ≤
      (γ₂ / 3) * (n : ℝ) := hdeg₁ _ heG₁
  have hadd := natCard_interFiber_add_le hG₂sub hL₂sub hdisj₂ (e : Set (Fin n))
  have hadd' : ((Nat.card {f : Good₂ // (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) +
      ((Nat.card {f : Left₂ // (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) ≤
      (Nat.card {f : Left₁ // (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) := by
    exact_mod_cast hadd
  have hN := hNsplit e
  linarith [hr, hfib', hdeg₁', hadd', hN, hγm]


/-- **The forward-degree-sum bound for Case 2.1.**  Concatenating the
restricted App-2 ordering of `𝓗₂^good ∖ 𝓗_med` with the restricted App-1
ordering of `𝓗₁^good ∖ 𝓗_med` (via `exists_ordering_of_disjoint_cover`'s
`concatOrderingS`) yields an ordering of `case2Right` in which
`d⫯(e) + |N_{𝓗₂^left}(e)| ≤ (1−2σ)n` for every edge — the hypothesis of
`case2_large_colouring`.  The two blocks are handled by
`case2_fwddeg_good₂` and `case2_fwddeg_good₁`. -/
theorem case2_fwddeg_sum {n r₁ r₀ : ℕ} {β γ₂ σ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)} {k₁ k₂ : ℕ}
    (ord₁ : nonHuge 𝓗 β ≃ Fin k₁) (ord₂ : Left₁ ≃ Fin k₂)
    (hG₂sub : Good₂ ⊆ Left₁) (hL₂sub : Left₂ ⊆ Left₁) (hpart₂ : Good₂ ∪ Left₂ = Left₁)
    (hdisj₂ : Disjoint Good₂ Left₂) (hG₁sub : Good₁ ⊆ nonHuge 𝓗 β)
    (hL₁sub : Left₁ ⊆ nonHuge 𝓗 β) (hpart₁ : Good₁ ∪ Left₁ = nonHuge 𝓗 β)
    (hdisj₁ : Disjoint Good₁ Left₁)
    (hseg₂ : ∀ f u : Left₁, (f : Set (Fin n)) ∈ Left₂ → (u : Set (Fin n)) ∈ Good₂ →
      (ord₂ f : ℕ) ≤ (ord₂ u : ℕ))
    (hseg₁ : ∀ f u : nonHuge 𝓗 β, (f : Set (Fin n)) ∈ Left₁ → (u : Set (Fin n)) ∈ Good₁ →
      (ord₁ f : ℕ) ≤ (ord₁ u : ℕ))
    (hdeg₂ : ∀ e : Left₁, (e : Set (Fin n)) ∈ Good₂ →
      (precedingDegree Left₁ ord₂ e : ℝ) ≤ (1 - 3 * σ) * (n : ℝ))
    (hdeg₁ : ∀ e : nonHuge 𝓗 β, (e : Set (Fin n)) ∈ Good₁ →
      (precedingDegree (nonHuge 𝓗 β) ord₁ e : ℝ) ≤ (γ₂ / 3) * (n : ℝ))
    (hNsplit : ∀ e : case2Right r₁ r₀ 𝓗 Good₁ Good₂,
      ((Nat.card {g : case2Left r₁ r₀ 𝓗 W₂ H₃ //
          (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) ≤
        (Nat.card {g : Left₂ // (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) +
          32 / β ^ 2)
    (hσn : 32 / β ^ 2 ≤ σ * (n : ℝ))
    (hγm : (γ₂ / 3) * (n : ℝ) + 32 / β ^ 2 ≤ (1 - 2 * σ) * (n : ℝ)) :
    ∃ (kB : ℕ) (ord' : (case2Right r₁ r₀ 𝓗 Good₁ Good₂) ≃ Fin kB),
      ∀ e : case2Right r₁ r₀ 𝓗 Good₁ Good₂,
        ((precedingDegree (case2Right r₁ r₀ 𝓗 Good₁ Good₂) ord' e : ℝ) +
          (Nat.card {g : case2Left r₁ r₀ 𝓗 W₂ H₃ //
            (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℝ)) ≤
          (1 - 2 * σ) * (n : ℝ) := by
  classical
  obtain ⟨m₂, ordG₂, hrankG₂, hdegG₂⟩ :=
    exists_restricted_ordering (𝓖 := Left₁) ord₂ hG₂sub
  obtain ⟨m₂', ordG₂m, hrankG₂m, hdegG₂m⟩ :=
    exists_restricted_ordering (𝓖 := Good₂) ordG₂
      (show case2Good₂med r₁ r₀ 𝓗 Good₂ ⊆ Good₂ from Set.sdiff_subset)
  obtain ⟨m₁, ordG₁, hrankG₁, hdegG₁⟩ :=
    exists_restricted_ordering (𝓖 := nonHuge 𝓗 β) ord₁ hG₁sub
  obtain ⟨m₁', ordG₁m, hrankG₁m, hdegG₁m⟩ :=
    exists_restricted_ordering (𝓖 := Good₁) ordG₁
      (show case2Good₁med r₁ r₀ 𝓗 Good₁ ⊆ Good₁ from Set.sdiff_subset)
  have hcovR : case2Good₂med r₁ r₀ 𝓗 Good₂ ∪ case2Good₁med r₁ r₀ 𝓗 Good₁ =
      case2Right r₁ r₀ 𝓗 Good₁ Good₂ := by
    rw [case2Good₂med, case2Good₁med, case2Right, ← Set.union_diff_distrib]
  have hdisjR : Disjoint (case2Good₂med r₁ r₀ 𝓗 Good₂) (case2Good₁med r₁ r₀ 𝓗 Good₁) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact (Set.disjoint_left.mp hdisj₁) hx'.1 (hG₂sub hx.1)
  refine ⟨m₂' + m₁', concatOrderingS hcovR hdisjR ordG₂m ordG₁m, ?_⟩
  intro e
  have hu : (e : Set (Fin n)) ∈
      case2Good₂med r₁ r₀ 𝓗 Good₂ ∪ case2Good₁med r₁ r₀ 𝓗 Good₁ := by
    rw [hcovR]; exact e.2
  simp only [Set.mem_union] at hu
  rcases hu with he₂ | he₁
  · exact case2_fwddeg_good₂ (γ₂ := γ₂) ord₂ hG₂sub ordG₂ hrankG₂ ordG₂m hdegG₂m ordG₁m
      hcovR hdisjR hL₂sub hpart₂ hdisj₂ hseg₂ hdeg₂ hNsplit hσn e he₂
  · exact case2_fwddeg_good₁ (γ₂ := γ₂) ord₁ hG₁sub ordG₁ hrankG₁ ordG₁m hdegG₁m ordG₂m
      hcovR hdisjR hL₁sub hpart₁ hdisj₁ hG₂sub hL₂sub hdisj₂ hseg₁ hdeg₁ hNsplit hγm e he₁


/-! ## The assembly of Case 2.1 -/

/-- **The neighbour-count split for Case 2.1.**  `𝓗₂^left ∖ 𝓗_med` consists of
huge edges and edges of `𝓗₂^left ∩ 𝓗₁^left` (by the cover
`𝓗 = 𝓗₃ ∪ W₂ ∪ 𝓗₂^good ∪ 𝓗₁^good` and the disjointness of `𝓗₃` from
`𝓗₂^good ∪ 𝓗₁^good`), and there are at most `32/β²` huge edges
(`natCard_hugeEdges_le`); hence
`|N_{𝓗₂^left}(e)| ≤ |N_{𝓗₂^left ∩ 𝓗₁^left}(e)| + 32/β²`. -/
theorem case2_Nsplit {n r₁ r₀ : ℕ} {β γ₂ σ δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂} {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hlin : 𝓗.IsLinear) (hβ : 0 < β) (hβc : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n) :
    ∀ e : case2Right r₁ r₀ 𝓗 Good₁ Good₂,
      ((Nat.card {g : case2Left r₁ r₀ 𝓗 W₂ H₃ //
          (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) ≤
        (Nat.card {g : Left₂ // (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) +
          32 / β ^ 2 := by
  classical
  intro e
  -- `𝓗₂^left ⊆ 𝓗_huge ∪ 𝓗₂^left ∩ 𝓗₁^left`
  have hsub : case2Left r₁ r₀ 𝓗 W₂ H₃ ⊆ case2HugeLeft₂ β 𝓗 Left₂ := by
    intro x hx
    have hx' : x ∈ (H₃ ∪ W₂) \ 𝓗.medEdges r₁ r₀ := by simpa only [case2Left] using hx
    have hxHW : x ∈ H₃ ∪ W₂ := hx'.1
    rw [Set.mem_union] at hxHW
    rcases hxHW with hxH | hxW
    · by_cases hh : β * (n : ℝ) / 4 ≤ (edgeSize x : ℝ)
      · exact Or.inl ((mem_hugeEdges 𝓗 β x).mpr ⟨hB.hH₃sub hxH, hh⟩)
      · have hnh : x ∈ nonHuge 𝓗 β := ⟨hB.hH₃sub hxH, hh⟩
        have h1 : x ∈ Good₁ ∪ Left₁ := by rw [hB.hpart₁]; exact hnh
        rw [Set.mem_union] at h1
        rcases h1 with hg | hl
        · exact absurd hg ((Set.disjoint_left.mp hB.hdisjH₃G₁) hxH)
        · have h2 : x ∈ Good₂ ∪ Left₂ := by rw [hB.hpart₂]; exact hl
          rw [Set.mem_union] at h2
          rcases h2 with hg | hl2
          · exact absurd hg ((Set.disjoint_left.mp hB.hdisjH₃G₂) hxH)
          · exact Or.inr hl2
    · exact Or.inr (hB.hW₂sub hxW)
  have hdisj : Disjoint (𝓗.hugeEdges β) Left₂ := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact (Set.disjoint_left.mp (disjoint_hugeEdges_nonHuge 𝓗 β)) hx (hB.hL₁sub (hB.hL₂sub hx'))
  -- the three counting steps
  have h1 : Nat.card {g : case2Left r₁ r₀ 𝓗 W₂ H₃ //
        (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} ≤
      Nat.card {g : case2HugeLeft₂ β 𝓗 Left₂ //
        (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} :=
    natCard_family_mono hsub (fun f : Set (Fin n) =>
      (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty))
  have h2 : Nat.card {g : case2HugeLeft₂ β 𝓗 Left₂ //
        (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} ≤
      Nat.card {g : 𝓗.hugeEdges β // (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} +
        Nat.card {g : Left₂ // (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} :=
    natCard_interFiber_le_add rfl hdisj (e : Set (Fin n))
  have h3 : (Nat.card {g : 𝓗.hugeEdges β //
        (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℝ) ≤ 32 / β ^ 2 := by
    have hle : Nat.card {g : 𝓗.hugeEdges β //
          (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} ≤
        Nat.card (𝓗.hugeEdges β) :=
      Nat.card_le_card_of_injective (fun x => x.1) (fun a b hab => Subtype.ext hab)
    exact le_trans (by exact_mod_cast hle) (natCard_hugeEdges_le (𝓗 := 𝓗) hlin hβ hβc hn1)
  have h12 : ((Nat.card {g : case2Left r₁ r₀ 𝓗 W₂ H₃ //
        (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) ≤
      ((Nat.card {g : 𝓗.hugeEdges β //
        (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) +
      ((Nat.card {g : Left₂ // (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℕ) : ℝ) := by
    exact_mod_cast le_trans h1 h2
  linarith [h12, h3]


/-- **The Case-2.1 data** (first glue step): `case2_colouring_left` produces
`φ₁` on `𝓗₂^left ∖ 𝓗_med` with its colour set `C₁`, and `case2_fwddeg_sum`
(with the `hNsplit` plumbing `case2_Nsplit`) produces the ordering `ord'` of
`𝓗₂^good ∪ 𝓗₁^good ∖ 𝓗_med` together with the forward-degree-sum bound —
exactly the two inputs of `case2_large_colouring`. -/
theorem case2_data {Δ₀ : ℝ → ℝ}
    (hMRe : ∀ (ζ' : ℝ), 0 < ζ' → ζ' ≤ 1 → ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ), Δ₀ ζ' ≤ Δ →
        (G.maxDegree : ℝ) ≤ Δ →
        (∀ v : V, (nbrEdges G v : ℝ) ≤ (1 - ζ') * Δ ^ 2 / 2) →
        ∃ k : ℕ, (k : ℝ) ≤ (1 - ζ' / Real.exp 6) * Δ ∧ G.Colorable k)
    {n r₁ r₀ : ℕ} {β γ₂ σ δ γ₁ ζ : ℝ} {B₀ : ℕ} {Δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂} {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hW₂ne : W₂ ≠ ∅) (hlin : 𝓗.IsLinear) (h2n : 2 ≤ n) (hβ : 0 < β) (hσ0 : 0 < σ)
    (hσ32 : 3 * σ / 2 ≤ 1) (hr₀ : 1 ≤ r₀) (h2r₀ : 2 ≤ r₀) (h2r₁ : 2 ≤ r₁)
    (hR : (100000000 : ℝ) ≤ (r₁ : ℝ))
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 256) (hδV : δ ≤ volBound app3tau app3K)
    (hm : Corollary65Margins Δ₀ ζ r₃ B₀ n Δ)
    (hB₀ : sizeFactor (3 * σ) 1 * (r₃ : ℝ) ≤ (B₀ : ℝ))
    (hmarginA : ((2 : ℝ) / ((β / 5) / 2) + 1) *
      ((n : ℝ) / (((β / 5) / 2 : ℝ) * (r₀ : ℝ))) ≤ ζ * (n : ℝ) / 1000)
    (h69m : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < ((1 / 6000 : ℝ) * (n : ℝ)) / 4)
    (h69b : (((bigFinset (β / 5) (case2H3med r₁ r₀ 𝓗 H₃)).card : ℕ) : ℝ) <
      ((1 / 6000 : ℝ) * (n : ℝ)) / 2)
    (h2βn : (2 : ℝ) ≤ (β / 5) * (n : ℝ))
    (hζdef : ζ = 1 - (r₃ : ℝ) / Real.sqrt (n : ℝ)) (hζpos : 0 < ζ)
    (hk2 : 2 * δ ^ 2 ≤ ζ / 1000 - 2 * σ)
    (hnbig : 16 / Real.sqrt δ ≤ (n : ℝ))
    (hσsmall : (2 : ℝ) * σ + 1 / (n : ℝ) ≤ 1 / 12000)
    (hsize₃ : ∀ e : case2H3med r₁ r₀ 𝓗 H₃, r₃ ≤ edgeSize (e : Set (Fin n)))
    {Cmed : Finset (Fin n)}
    (hroom1 : ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ ≤ (Finset.univ \ Cmed).card)
    (hroom2 : ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ + ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ ≤
      (Finset.univ \ Cmed).card)
    (hbudget0 : ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ + ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ ≤
      ⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊)
    (hβc : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n)
    (hσn : 32 / β ^ 2 ≤ σ * (n : ℝ))
    (hγm : (γ₂ / 3) * (n : ℝ) + 32 / β ^ 2 ≤ (1 - 2 * σ) * (n : ℝ)) :
    ∃ (C₁ : Finset (Fin n)) (φ₁ : (case2Left r₁ r₀ 𝓗 W₂ H₃).Coloring (Fin n))
      (kB : ℕ) (ord' : (case2Right r₁ r₀ 𝓗 Good₁ Good₂) ≃ Fin kB),
      φ₁.UsesColourSet C₁ ∧ φ₁.AlphaBounded (β / 5) ∧
      (C₁.card : ℝ) ≤ (1 - 3 * σ / 2) * (n : ℝ) ∧
      C₁.card ≤ ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ + ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ ∧
      Disjoint C₁ Cmed ∧
      (∀ e : case2Right r₁ r₀ 𝓗 Good₁ Good₂,
        ((precedingDegree (case2Right r₁ r₀ 𝓗 Good₁ Good₂) ord' e : ℝ) +
          (Nat.card {g : case2Left r₁ r₀ 𝓗 W₂ H₃ //
            (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℝ)) ≤
          (1 - 2 * σ) * (n : ℝ)) := by
  classical
  obtain ⟨C₁, φ₁, hφ₁C, hφ₁b, hC₁, hC₁size, hdisj₁M⟩ :=
    case2_colouring_left (Δ₀ := Δ₀) hMRe hB hW₂ne hlin h2n hβ hσ0 hσ32 h2βn hr₀ h2r₀ h2r₁ hR hsize
      hδ0 hδ1 hδV hm hB₀ hmarginA h69m h69b
      (hζdef := hζdef) (hζpos := hζpos) (hk2 := hk2) (hnbig := hnbig)
      (hσsmall := hσsmall) (hsize₃ := hsize₃)
      hroom1 hroom2 hbudget0
  obtain ⟨kB, ord', hsum⟩ :=
    case2_fwddeg_sum ord₁ ord₂ hB.hG₂sub hB.hL₂sub hB.hpart₂ hB.hdisj₂ hB.hG₁sub hB.hL₁sub
      hB.hpart₁ hB.hdisj₁ hB.hseg₂ hB.hseg₁ hB.hdeg₂ hB.hdeg₁
      (case2_Nsplit hB hlin hβ hβc hn1) hσn hγm
  exact ⟨C₁, φ₁, kB, ord', hφ₁C, hφ₁b, hC₁, hC₁size, hdisj₁M, hsum⟩


/-- **The Case-2.1 colouring of `𝓗_large`.**  Given `φ₁` on
`𝓗₂^left ∖ 𝓗_med`, the extra colour set `C₂` (disjoint from `C₁ ∪ Cmed`, of
size `⌊(1−3σ/2)n⌋ − |C₁|`), the colour set `C_huge` of the colours `φ₁`
assigns to huge edges and the lists `case2List`, Proposition 6.9 produces
`φ₂` on `𝓗₂^good ∪ 𝓗₁^good ∖ 𝓗_med` avoiding the colours of the `φ₁`
neighbours; `φ₁` and `φ₂` combine by `coloringUnionCross` into a colouring
`φL` of `𝓗_large` with at most `(1−σ)n − |Cmed|` colours whose huge colour
classes are singletons and whose other classes cover at most `βn` vertices —
exactly the input of `largeEdge_nonExtremal_of_largeColouring`. -/
theorem case2_large_colouring {n r₁ r₀ : ℕ} {β γ₂ σ δ γ₁ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂} {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hlin : 𝓗.IsLinear) (h2n : 2 ≤ n) (hβ : 0 < β) (h2r₀ : 2 ≤ r₀) (hσ32 : 3 * σ / 2 ≤ 1)
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ))
    {C₁ : Finset (Fin n)} {φ₁ : (case2Left r₁ r₀ 𝓗 W₂ H₃).Coloring (Fin n)}
    (hφ₁C : φ₁.UsesColourSet C₁) (hφ₁b : φ₁.AlphaBounded (β / 5))
    (hC₁ : (C₁.card : ℝ) ≤ (1 - 3 * σ / 2) * (n : ℝ))
    {Cmed : Finset (Fin n)} (hdisj₁M : Disjoint C₁ Cmed)
    {kB : ℕ} (ord' : (case2Right r₁ r₀ 𝓗 Good₁ Good₂) ≃ Fin kB)
    (hsum : ∀ e : case2Right r₁ r₀ 𝓗 Good₁ Good₂,
      ((precedingDegree (case2Right r₁ r₀ 𝓗 Good₁ Good₂) ord' e : ℝ) +
        (Nat.card {g : case2Left r₁ r₀ 𝓗 W₂ H₃ //
          (((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)} : ℝ)) ≤ (1 - 2 * σ) * (n : ℝ))
    (h69m : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < ((σ / 4) * (n : ℝ)) / 4)
    (h69b : (((bigFinset (β / 5) (case2Right r₁ r₀ 𝓗 Good₁ Good₂)).card : ℕ) : ℝ) <
      ((σ / 4) * (n : ℝ)) / 2)
    (hKroom : ⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ + Cmed.card ≤ n)
    (hC₁K : C₁.card ≤ ⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊)
    (hslack : 1 + 32 / β ^ 2 ≤ (σ / 4) * (n : ℝ))
    (hβc : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n) (hγ₁σ : γ₁ ≤ σ / 2)
    (hγ₁n : (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ)) :
    ∃ (C_large : Finset (Fin n)) (φL : (𝓗.largeEdges r₀).Coloring (Fin n)),
      φL.UsesColourSet C_large ∧
      (C_large.card : ℝ) + (Cmed.card : ℝ) ≤ (1 - σ) * (n : ℝ) ∧
      Disjoint C_large Cmed ∧
      (∀ c : Fin n, (∃ e : 𝓗.largeEdges r₀, e ∈ φL.colorClass c ∧
          β * (n : ℝ) / 4 ≤ (edgeSize (e : Set (Fin n)) : ℝ)) →
        ∃ e₀ : 𝓗.largeEdges r₀, φL.colorClass c = {e₀}) ∧
      (∀ c : Fin n, c ∉ Cmed →
        (¬ ∃ e : 𝓗.largeEdges r₀, e ∈ φL.colorClass c ∧
          β * (n : ℝ) / 4 ≤ (edgeSize (e : Set (Fin n)) : ℝ)) →
        (φL.classVertexCount c : ℝ) ≤ β * (n : ℝ)) := by
  classical
  haveI hfinA : Fintype (case2Left r₁ r₀ 𝓗 W₂ H₃) := Fintype.ofFinite _
  have hsizeN : ∀ e : 𝓗, r₁ < edgeSize (e : Set (Fin n)) := fun e => by
    have h := hsize e
    exact_mod_cast h
  obtain ⟨hcovAB, hdisjAB, hsizeB, hnonHugeB⟩ := case2_parts (r₀ := r₀) hB hsizeN
  have hsubA : case2Left r₁ r₀ 𝓗 W₂ H₃ ⊆ 𝓗.largeEdges r₀ := by
    rw [← hcovAB]; exact Set.subset_union_left
  have hsubB : case2Right r₁ r₀ 𝓗 Good₁ Good₂ ⊆ 𝓗.largeEdges r₀ := by
    rw [← hcovAB]; exact Set.subset_union_right
  have hcov' : ∀ e ∈ 𝓗.largeEdges r₀,
      e ∈ case2Left r₁ r₀ 𝓗 W₂ H₃ ∨ e ∈ case2Right r₁ r₀ 𝓗 Good₁ Good₂ := by
    intro e he
    rw [← hcovAB] at he
    simpa only [Set.mem_union] using he
  -- the extra colour set `C₂`
  set K : ℕ := ⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ with hKdef
  have hroom : K - C₁.card ≤ (Finset.univ \ (C₁ ∪ Cmed)).card := by
    have h1 : (Finset.univ \ (C₁ ∪ Cmed)).card = n - (C₁ ∪ Cmed).card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    have h2 : (C₁ ∪ Cmed).card = C₁.card + Cmed.card := Finset.card_union_of_disjoint hdisj₁M
    rw [h1, h2]
    omega
  obtain ⟨C₂, hC₂sub, hC₂card⟩ := Finset.exists_subset_card_eq hroom
  have hC₂disj₁ : Disjoint C₁ C₂ := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp (hC₂sub hx')).2 (Finset.mem_union.mpr (Or.inl hx))
  have hC₂disjM : Disjoint C₂ Cmed := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp (hC₂sub hx)).2 (Finset.mem_union.mpr (Or.inr hx'))
  have hC₁₂card : (C₁ ∪ C₂).card = K := by
    rw [Finset.card_union_of_disjoint hC₂disj₁, hC₂card]
    omega
  have hK' : (1 - 3 * σ / 2) * (n : ℝ) - 1 ≤ (K : ℝ) := by
    have := Nat.lt_floor_add_one ((1 - 3 * σ / 2) * (n : ℝ))
    rw [hKdef]
    linarith
  have hfloor : (K : ℝ) ≤ (1 - 3 * σ / 2) * (n : ℝ) := by
    rw [hKdef]
    refine Nat.floor_le ?_
    nlinarith [hσ32, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  -- Proposition 6.9 on `𝓗₂^good ∪ 𝓗₁^good ∖ 𝓗_med`
  have hlinB : (case2Right r₁ r₀ 𝓗 Good₁ Good₂).IsLinear :=
    IsLinear.mono hsubB (IsLinear.mono (largeEdges_subset 𝓗 r₀) hlin)
  obtain ⟨φ₂, hφ₂b, hφ₂list⟩ :=
    prop69_colouring (n := n) (r := r₀) (k := kB) (α₁ := σ / 4) (α₂ := β / 5)
      (𝓗 := case2Right r₁ r₀ 𝓗 Good₁ Good₂) h2n h2r₀ (by linarith) h69m h69b hlinB hsizeB
      ord' (fun e => case2List r₁ r₀ 𝓗 W₂ H₃ φ₁ β C₁ C₂ (e : Set (Fin n)))
      (fun e => case2_list_bound hβ hβc hn1 hlin hC₁₂card hK' hslack ord' hsum e)
  -- the cross-condition
  have hcross : ∀ (e₁ : case2Left r₁ r₀ 𝓗 W₂ H₃) (e₂ : case2Right r₁ r₀ 𝓗 Good₁ Good₂),
      (((e₁ : Set (Fin n)) ∩ (e₂ : Set (Fin n))).Nonempty) → φ₁.labels e₁ ≠ φ₂.labels e₂ := by
    intro e₁ e₂ hne hEq
    have hm : φ₁.labels e₁ ∈ case2Forb r₁ r₀ 𝓗 W₂ H₃ φ₁ (e₂ : Set (Fin n)) :=
      mem_case2Forb.mpr ⟨e₁, hne, rfl⟩
    have h2 : φ₂.labels e₂ ∈ case2List r₁ r₀ 𝓗 W₂ H₃ φ₁ β C₁ C₂ (e₂ : Set (Fin n)) :=
      hφ₂list e₂
    exact (mem_case2List.mp h2).2 (hEq ▸ hm)
  refine ⟨C₁ ∪ C₂, coloringUnionCross hsubA hsubB hcov' hdisjAB φ₁ φ₂ hcross,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- the combined colouring uses `C₁ ∪ C₂`
    intro e
    by_cases he : (e : Set (Fin n)) ∈ case2Left r₁ r₀ 𝓗 W₂ H₃
    · have hlab : (coloringUnionCross hsubA hsubB hcov' hdisjAB φ₁ φ₂ hcross).labels e =
          φ₁.labels ⟨(e : Set (Fin n)), he⟩ := by
        simp only [coloringUnionCross, unionLabelCross, dif_pos he]
      rw [hlab]
      exact Finset.mem_union_left _ (hφ₁C _)
    · have hlab : (coloringUnionCross hsubA hsubB hcov' hdisjAB φ₁ φ₂ hcross).labels e =
          φ₂.labels ⟨(e : Set (Fin n)), (hcov' (e : Set (Fin n)) e.2).resolve_left he⟩ := by
        simp only [coloringUnionCross, unionLabelCross, dif_neg he]
      rw [hlab]
      exact (mem_case2List.mp (hφ₂list _)).1.1
  · -- the colour budget
    rw [hC₁₂card]
    nlinarith [hfloor, hγ₁n, hγ₁σ, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  · -- disjointness from `Cmed`
    rw [Finset.disjoint_left]
    intro x hx hxM
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.disjoint_left.mp hdisj₁M) hx hxM
    · exact (Finset.disjoint_left.mp hC₂disjM) hx hxM
  · -- colours of huge edges are singletons
    intro c hc
    obtain ⟨f, hfcl, hfb⟩ := hc
    have hfm :=
      (mem_colorClass_coloringUnionCross (h₁ := hsubA) (h₂ := hsubB) (hcover := hcov')
        (hdisjG := hdisjAB) (φ₁ := φ₁) (φ₂ := φ₂) (hcross := hcross) f c).mp hfcl
    have hf_notB : (f : Set (Fin n)) ∉ case2Right r₁ r₀ 𝓗 Good₁ Good₂ :=
      fun h => (hnonHugeB h.1).2 hfb
    have hfA : (f : Set (Fin n)) ∈ case2Left r₁ r₀ 𝓗 W₂ H₃ := by
      rcases hfm with ⟨h1, -⟩ | ⟨h2, -⟩
      · exact h1
      · exact absurd h2 hf_notB
    have hf₁ : (⟨(f : Set (Fin n)), hfA⟩ : case2Left r₁ r₀ 𝓗 W₂ H₃) ∈ φ₁.colorClass c := by
      rcases hfm with ⟨h1, hcl1⟩ | ⟨h2, hcl2⟩
      · exact hcl1
      · exact absurd h2 hf_notB
    have hcChuge : c ∈ hugeColourSet 𝓗 (case2Left r₁ r₀ 𝓗 W₂ H₃) β φ₁ := by
      refine mem_hugeColourSet.mpr ⟨⟨(f : Set (Fin n)), hfA⟩, ?_, ?_⟩
      · exact (mem_hugeEdges 𝓗 β (f : Set (Fin n))).mpr ⟨largeEdges_subset 𝓗 r₀ f.2, hfb⟩
      · have hlab : (coloringUnionCross hsubA hsubB hcov' hdisjAB φ₁ φ₂ hcross).labels f =
            φ₁.labels ⟨(f : Set (Fin n)), hfA⟩ := by
          simp only [coloringUnionCross, unionLabelCross, dif_pos hfA]
        rw [mem_colorClass] at hfcl
        exact hlab.symm.trans hfcl
    have hφ₂empty : φ₂.colorClass c = ∅ := by
      ext g
      constructor
      · intro hg
        rw [mem_colorClass] at hg
        have hc' : φ₂.labels g ∈ hugeColourSet 𝓗 (case2Left r₁ r₀ 𝓗 W₂ H₃) β φ₁ := by
          rw [hg]; exact hcChuge
        exact (mem_case2List.mp (hφ₂list g)).1.2 hc'
      · intro hg
        exact absurd hg (Set.notMem_empty g)
    have hncard₁ : (φ₁.colorClass c).ncard ≤ 1 := by
      rcases (AlphaBounded_iff_classVertexCount (β / 5) φ₁).mp hφ₁b c with h1 | h1
      · exact h1
      · exfalso
        have hle : ((edgeSize (f : Set (Fin n)) : ℕ) : ℝ) ≤ (φ₁.classVertexCount c : ℝ) := by
          exact_mod_cast edgeSize_le_classVertexCount_of_mem_colorClass φ₁ hf₁
        have hbig : (β / 5) * (n : ℝ) < (edgeSize (f : Set (Fin n)) : ℝ) := by
          nlinarith [hfb, hβ, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
        linarith [h1, hle, hbig]
    obtain ⟨e₀, hsing₁⟩ := exists_colorClass_eq_singleton_of_ncard_le_one φ₁ hncard₁ hf₁
    refine ⟨⟨(e₀ : Set (Fin n)), hsubA e₀.2⟩, ?_⟩
    ext e
    rw [mem_colorClass_coloringUnionCross (h₁ := hsubA) (h₂ := hsubB) (hcover := hcov')
        (hdisjG := hdisjAB) (φ₁ := φ₁) (φ₂ := φ₂) (hcross := hcross) e c,
      Set.mem_singleton_iff]
    constructor
    · rintro (⟨he, hcl⟩ | ⟨he, hcl⟩)
      · have hEq : (⟨(e : Set (Fin n)), he⟩ : case2Left r₁ r₀ 𝓗 W₂ H₃) = e₀ := by
          rw [hsing₁] at hcl
          simpa using hcl
        exact Subtype.ext (congrArg (fun x : case2Left r₁ r₀ 𝓗 W₂ H₃ =>
          (x : Set (Fin n))) hEq)
      · exfalso
        have hg : (⟨(e : Set (Fin n)), he⟩ : case2Right r₁ r₀ 𝓗 Good₁ Good₂) ∈ φ₂.colorClass c :=
          hcl
        rw [hφ₂empty] at hg
        exact hg
    · intro he
      have hmem₀ : e₀ ∈ φ₁.colorClass c := by rw [hsing₁]; exact rfl
      have hv : (e : Set (Fin n)) = (e₀ : Set (Fin n)) :=
        congrArg (fun x : 𝓗.largeEdges r₀ => (x : Set (Fin n))) he
      have h1mem : (e : Set (Fin n)) ∈ case2Left r₁ r₀ 𝓗 W₂ H₃ := by
        rw [hv]; exact e₀.2
      refine Or.inl ⟨h1mem, ?_⟩
      have hEq : (⟨(e : Set (Fin n)), h1mem⟩ : case2Left r₁ r₀ 𝓗 W₂ H₃) = e₀ :=
        Subtype.ext hv
      rw [hEq]
      exact hmem₀
  · -- all other colour classes cover at most `βn` vertices
    intro c hcM hnoHuge
    have hvc := classVertexCount_coloringUnionCross_le (h₁ := hsubA) (h₂ := hsubB)
      (hcover := hcov') (hdisjG := hdisjAB) (φ₁ := φ₁) (φ₂ := φ₂) (hcross := hcross) c
    have h₁ : (φ₁.classVertexCount c : ℝ) ≤ β * (n : ℝ) / 4 := by
      have hM : ∀ e : case2Left r₁ r₀ 𝓗 W₂ H₃, e ∈ φ₁.colorClass c →
          (edgeSize (e : Set (Fin n)) : ℝ) ≤ β * (n : ℝ) / 4 := by
        intro e he
        by_contra hcon
        have hbig : β * (n : ℝ) / 4 ≤ (edgeSize (e : Set (Fin n)) : ℝ) := by linarith
        have heL : (⟨(e : Set (Fin n)), hsubA e.2⟩ : 𝓗.largeEdges r₀) ∈
            (coloringUnionCross hsubA hsubB hcov' hdisjAB φ₁ φ₂ hcross).colorClass c := by
          refine (mem_colorClass_coloringUnionCross (h₁ := hsubA) (h₂ := hsubB)
            (hcover := hcov') (hdisjG := hdisjAB) (φ₁ := φ₁) (φ₂ := φ₂)
            (hcross := hcross) _ c).mpr (Or.inl ⟨e.2, ?_⟩)
          have hEq : (⟨(e : Set (Fin n)), e.2⟩ : case2Left r₁ r₀ 𝓗 W₂ H₃) = e :=
            Subtype.ext rfl
          rw [hEq]; exact he
        exact hnoHuge ⟨⟨(e : Set (Fin n)), hsubA e.2⟩, heL, hbig⟩
      have hmax := classVertexCount_le_of_alphaBounded φ₁ hφ₁b
        (by positivity : (0 : ℝ) ≤ (β / 5) * (n : ℝ)) hM
      have hle : max ((β / 5) * (n : ℝ)) (β * (n : ℝ) / 4) = β * (n : ℝ) / 4 :=
        max_eq_right (by nlinarith [hβ, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])
      linarith [hmax, hle.symm.le, hle.ge]
    have h₂ : (φ₂.classVertexCount c : ℝ) ≤ β * (n : ℝ) / 4 := by
      have hM : ∀ e : case2Right r₁ r₀ 𝓗 Good₁ Good₂, e ∈ φ₂.colorClass c →
          (edgeSize (e : Set (Fin n)) : ℝ) ≤ β * (n : ℝ) / 4 := by
        intro e _
        have hnh := hnonHugeB e.2.1
        have : (edgeSize (e : Set (Fin n)) : ℝ) < β * (n : ℝ) / 4 := not_le.mp hnh.2
        linarith
      have hmax := classVertexCount_le_of_alphaBounded φ₂ hφ₂b
        (by positivity : (0 : ℝ) ≤ (β / 5) * (n : ℝ)) hM
      have hle : max ((β / 5) * (n : ℝ)) (β * (n : ℝ) / 4) = β * (n : ℝ) / 4 :=
        max_eq_right (by nlinarith [hβ, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])
      linarith [hmax, hle.symm.le, hle.ge]
    have hvc' : ((coloringUnionCross hsubA hsubB hcov' hdisjAB φ₁ φ₂ hcross).classVertexCount c : ℝ) ≤
        (φ₁.classVertexCount c : ℝ) + (φ₂.classVertexCount c : ℝ) := by
      exact_mod_cast hvc
    linarith [hvc', h₁, h₂, hβ, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]



/-- **Case 2.1 of Theorem 6.1 is complete**: the non-extremal alternative,
from the App-1/App-2 block decomposition with `W₂ ≠ ∅`.  The glue:
`case2_data` (φ₁ and `ord'` with the forward-degree-sum bound, including the
exact colour count `⌈(1−ζ/1000)n⌉₊ + ⌈(1/1500)n⌉₊` of `C₁`),
`case2_large_colouring` (the colouring `φL` of `𝓗_large` and its two
properties) and `largeEdge_nonExtremal_of_largeColouring` (with the
Proposition 6.10 colouring `φ_med` of `𝓗_med`). -/
theorem case2_nonExtremal {Δ₀ : ℝ → ℝ}
    (hMRe : ∀ (ζ' : ℝ), 0 < ζ' → ζ' ≤ 1 → ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ), Δ₀ ζ' ≤ Δ →
        (G.maxDegree : ℝ) ≤ Δ →
        (∀ v : V, (nbrEdges G v : ℝ) ≤ (1 - ζ') * Δ ^ 2 / 2) →
        ∃ k : ℕ, (k : ℝ) ≤ (1 - ζ' / Real.exp 6) * Δ ∧ G.Colorable k)
    {n r₁ r₀ : ℕ} {β γ₂ σ δ γ₁ ζ : ℝ} {B₀ : ℕ} {Δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂} {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hW₂ne : W₂ ≠ ∅) (hlin : 𝓗.IsLinear) (hn : 0 < n) (h2n : 2 ≤ n) (hβ : 0 < β)
    (hσ0 : 0 < σ) (hγ₁σ : γ₁ ≤ σ / 2) (hσ32 : 3 * σ / 2 ≤ 1) (hr₀ : 1 ≤ r₀) (h2r₀ : 2 ≤ r₀)
    (h2r₁ : 2 ≤ r₁) (hR : (100000000 : ℝ) ≤ (r₁ : ℝ))
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 256) (hδV : δ ≤ volBound app3tau app3K)
    (hm : Corollary65Margins Δ₀ ζ r₃ B₀ n Δ)
    (hB₀ : sizeFactor (3 * σ) 1 * (r₃ : ℝ) ≤ (B₀ : ℝ))
    (hmarginA : ((2 : ℝ) / ((β / 5) / 2) + 1) *
      ((n : ℝ) / (((β / 5) / 2 : ℝ) * (r₀ : ℝ))) ≤ ζ * (n : ℝ) / 1000)
    (h69m : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < ((1 / 6000 : ℝ) * (n : ℝ)) / 4)
    (h69b : (((bigFinset (β / 5) (case2H3med r₁ r₀ 𝓗 H₃)).card : ℕ) : ℝ) <
      ((1 / 6000 : ℝ) * (n : ℝ)) / 2)
    (hζdef : ζ = 1 - (r₃ : ℝ) / Real.sqrt (n : ℝ)) (hζpos : 0 < ζ)
    (hk2 : 2 * δ ^ 2 ≤ ζ / 1000 - 2 * σ)
    (hnbig : 16 / Real.sqrt δ ≤ (n : ℝ))
    (hσsmall : (2 : ℝ) * σ + 1 / (n : ℝ) ≤ 1 / 12000)
    (hsize₃ : ∀ e : case2H3med r₁ r₀ 𝓗 H₃, r₃ ≤ edgeSize (e : Set (Fin n)))
    (h69mσ : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < ((σ / 4) * (n : ℝ)) / 4)
    (h69bσ : (((bigFinset (β / 5) (case2Right r₁ r₀ 𝓗 Good₁ Good₂)).card : ℕ) : ℝ) <
      ((σ / 4) * (n : ℝ)) / 2)
    (h2βn : (2 : ℝ) ≤ (β / 5) * (n : ℝ))
    {Cmed : Finset (Fin n)} (hCmed : (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ))
    (hroom1 : ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ ≤ (Finset.univ \ Cmed).card)
    (hroom2 : ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ + ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ ≤
      (Finset.univ \ Cmed).card)
    (hbudget0 : ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ + ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ ≤
      ⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊)
    (hβc : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n)
    (hσn : 32 / β ^ 2 ≤ σ * (n : ℝ))
    (hγm : (γ₂ / 3) * (n : ℝ) + 32 / β ^ 2 ≤ (1 - 2 * σ) * (n : ℝ))
    (hKroom : ⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ + Cmed.card ≤ n)
    (hslack : 1 + 32 / β ^ 2 ≤ (σ / 4) * (n : ℝ))
    (hβn : (r₀ : ℝ) < β * (n : ℝ) / 4)
    {φmed : (𝓗.medEdges r₁ r₀).Coloring (Fin n)} (hφmed : φmed.UsesColourSet Cmed)
    (hmedb : ∀ c : Fin n, (φmed.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ)) :
    LargeEdgeNonExtremal n σ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 := by
  classical
  obtain ⟨C₁, φ₁, kB, ord', hφ₁C, hφ₁b, hC₁, hC₁size, hdisj₁M, hsum⟩ :=
    case2_data (Δ₀ := Δ₀) (γ₁ := γ₁) hMRe hB hW₂ne hlin h2n hβ hσ0 hσ32 hr₀ h2r₀ h2r₁ hR hsize hδ0 hδ1 hδV hm
      hB₀ hmarginA h69m h69b h2βn (hζdef := hζdef) (hζpos := hζpos) (hk2 := hk2)
      (hnbig := hnbig) (hσsmall := hσsmall) (hsize₃ := hsize₃)
      hroom1 hroom2 hbudget0 hβc hn1 hσn hγm
  obtain ⟨C_large, φL, hφLC, hbudgetL, hdisjCL, hsingL, hsmallL⟩ :=
    case2_large_colouring (δ := δ) hB hlin h2n hβ h2r₀ hσ32 hsize hφ₁C hφ₁b hC₁ hdisj₁M
      ord' hsum h69mσ h69bσ hKroom (le_trans hC₁size hbudget0) hslack hβc hn1 hγ₁σ hCmed
  refine largeEdge_nonExtremal_of_largeColouring hn ?_ hβ hγ₁σ hβn hdisjCL hbudgetL hφLC
    hsingL hsmallL hφmed hmedb hCmed
  intro e
  exact_mod_cast hsize e

end

end ErdosFaberLovaszConjecture
