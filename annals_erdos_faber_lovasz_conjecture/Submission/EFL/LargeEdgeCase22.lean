import Submission.EFL.LargeEdgeCases
import Submission.EFL.Nearfull.LinearNearfullColouring

/-!
# Case 2.2 of Theorem 6.1 (`large-edge-thm`): the FPP-extremal alternative

This module starts the proof of the extremal alternative
`LargeEdgeExtremal` in Case 2.2 of Figure 3 (`W₂ ≠ ∅` and
`r₃ ≥ (1−δ)√n`).  The paper's argument (arXiv:2101.04698v3, §7) is:

* the set `W₂` of the App-2 volume witness consists of FPP-extremal edges
  (`r₃ ≥ (1−δ)√n` is the lower bound; the upper bound uses
  `(W₂1)` and `eqn:d3-upper-bound` `r₃ ≤ √(n/(1−4σ))`), and `vol(W₂) ≥ 1−δ³`
  by `(W₂2)`, so the first conjunct of `LargeEdgeExtremal` holds with
  `W := W₂`;
* no edge of `𝓗` has size `≥ δn/2`: an edge outside `W₂` has
  `vol(e) ≤ vol(𝓗∖W₂) ≤ δ³`, and an edge inside `W₂` is FPP-extremal;
* Lemma 5.1 (`linear_nearfull_colouring`, the paper's `extremal-case-lemma`)
  colours `𝓗₂^left` with at most `n` colours, each on at most two edges;
  every such colour class covers at most `δn` vertices, and colour classes
  assigned to a huge edge cover at most `δn` vertices as well;
* the remaining two blocks `𝓗₂^good` and `𝓗₁^good` are coloured by
  Proposition 6.9 with the list assignments of the paper's Claims
  `claim:bounded-colouring-extension2` and
  `claim:bounded-colouring-extension3`, avoiding the colours already used
  on their neighbourhoods; the three colourings are glued with
  `coloringUnionCross`.

What is proved here: the volume/size facts about `W₂` and the construction
of the Lemma-5.1 colouring of the left block.  The remaining two Proposition
6.9 firings and the glue are the next steps.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The volume of the singleton family `{e}`. -/
lemma volume_singleton (e : Set (Fin n)) :
    volume n ({e} : Hypergraph (Fin n))
      = (((edgeSize e * (edgeSize e - 1) : ℕ) : ℝ)) / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
  rw [volume_eq_canon]
  congr 1
  have hcanon : canonFinset ({e} : Hypergraph (Fin n)) = {e} := by
    ext x
    simp [canonFinset]
  rw [hcanon, Finset.sum_singleton]

/-- **From a volume bound to a size bound.**  If `m(m−1) ≤ δ³n²` and `n` is
large enough then `m ≤ δn/2`. -/
lemma edgeSize_le_half_mul_of_volume {δ : ℝ} {m n : ℕ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 16) (hn1 : 1 ≤ n) (hnδ : 8 ≤ δ ^ 2 * (n : ℝ))
    (hvol : (m : ℝ) * ((m : ℝ) - 1) ≤ δ ^ 3 * (n : ℝ) ^ 2) :
    (m : ℝ) ≤ δ * (n : ℝ) / 2 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have : (0 : ℝ) ≤ δ * (n : ℝ) / 2 := by positivity
    simpa using this
  · have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    -- `(m−1)² ≤ m(m−1) ≤ δ³n²`
    have hsq1 : ((m : ℝ) - 1) ^ 2 ≤ (m : ℝ) * ((m : ℝ) - 1) := by nlinarith
    have hsq2 : ((m : ℝ) - 1) ^ 2 ≤ δ ^ 3 * (n : ℝ) ^ 2 := le_trans hsq1 hvol
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    -- `δ³n² ≤ (δn/4)²` because `δ ≤ 1/16`
    have hcomp : δ ^ 3 * (n : ℝ) ^ 2 ≤ (δ * (n : ℝ) / 4) ^ 2 := by nlinarith
    have hbound : (m : ℝ) - 1 ≤ δ * (n : ℝ) / 4 := by
      have h1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by linarith
      have h2 : (0 : ℝ) ≤ δ * (n : ℝ) / 4 := by positivity
      nlinarith [hsq2, hcomp]
    -- `1 ≤ δ²n/8 ≤ δn/8`
    have h1 : (1 : ℝ) ≤ δ ^ 2 * (n : ℝ) / 8 := by linarith
    have h2 : δ ^ 2 * (n : ℝ) / 8 ≤ δ * (n : ℝ) / 8 := by nlinarith
    linarith

/-- **The size bound coming from `(W₂2)`.**  An edge of `𝓗` outside the
volume set `W` has `vol({e}) ≤ vol(𝓗∖W) ≤ 1 − vol(W) ≤ δ³`. -/
lemma volume_singleton_le_of_notMem {𝓗 W : Hypergraph (Fin n)} {δ : ℝ}
    (hlin : 𝓗.IsLinear) (hWsub : W ⊆ 𝓗) (hWvol : 1 - δ ^ 3 ≤ volume n W)
    {e : Set (Fin n)} (he : e ∈ 𝓗) (hne : e ∉ W) :
    volume n ({e} : Hypergraph (Fin n)) ≤ δ ^ 3 := by
  classical
  have hdisj : Disjoint (W : Hypergraph (Fin n)) (𝓗 \ W) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx'.2 hx
  have hunion : W ∪ (𝓗 \ W) = 𝓗 := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hWsub hx
      · exact hx.1
    · intro hx
      by_cases h : x ∈ W
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
  have hadd : volume n W + volume n (𝓗 \ W) ≤ 1 := by
    rw [← volume_subfamily_union hdisj, hunion]
    exact volume_le_one_of_linear hlin
  have hsingle : ({e} : Hypergraph (Fin n)) ⊆ 𝓗 \ W := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨he, hne⟩
  have hmono := volume_subfamily_mono hsingle
  linarith

/-- **The size bound for `W₂`-members and non-members.**  Combining the three
estimates of Case 2.2: members of `W₂` have size `≤ (1+δ)√n`, non-members have
`vol ≤ δ³`, and with `n` large neither exceeds `δn/2`. -/
lemma edgeSize_le_half_mul_of_blocks {𝓗 W : Hypergraph (Fin n)} {δ : ℝ}
    (hlin : 𝓗.IsLinear) (hWsub : W ⊆ 𝓗) (hWvol : 1 - δ ^ 3 ≤ volume n W)
    (hWsize : ∀ e : Set (Fin n), e ∈ W → (edgeSize e : ℝ) ≤ (1 + δ) * Real.sqrt n)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 16) (hn1 : 1 ≤ n)
    (hnδ : 8 ≤ δ ^ 2 * (n : ℝ))
    (hsmall : (1 + δ) * Real.sqrt n ≤ δ * (n : ℝ) / 2)
    (hden : 0 < (n : ℝ) * ((n - 1 : ℕ) : ℝ)) :
    ∀ e : Set (Fin n), e ∈ 𝓗 → (edgeSize e : ℝ) ≤ δ * (n : ℝ) / 2 := by
  intro e he
  by_cases hmem : e ∈ W
  · have h := hWsize e hmem
    linarith
  · have hvol := volume_singleton_le_of_notMem hlin hWsub hWvol he hmem
    rw [volume_singleton] at hvol
    have hnum : (((edgeSize e * (edgeSize e - 1) : ℕ)) : ℝ) ≤ δ ^ 3 * (n : ℝ) ^ 2 := by
      have hdiv := (div_le_iff₀ hden).mp hvol
      have hnle : ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) ≤ (n : ℝ) ^ 2 := by
        have hnsub : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (Nat.sub_le n 1)
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
      nlinarith
    have hmain : (edgeSize e : ℝ) * ((edgeSize e : ℝ) - 1) ≤ δ ^ 3 * (n : ℝ) ^ 2 := by
      rwa [← cast_edgeTerm (edgeSize e)] at hnum
    have := edgeSize_le_half_mul_of_volume (δ := δ) (m := edgeSize e) (n := n) hδ0 hδ1 hn1 hnδ hmain
    linarith

/-- **The FPP-extremal witness of Case 2.2.**  With `(1−δ)√n ≤ r₃`, the
App-2 volume set `W₂` consists of FPP-extremal edges and has volume `≥ 1−δ`,
so it is the set required by the first conjunct of `LargeEdgeExtremal`. -/
theorem extremal_witness_of_blocks {n : ℕ} {β γ₂ σ δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂}
    {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hW₂ne : W₂ ≠ ∅) (hr₃lo : (1 - δ) * Real.sqrt (n : ℝ) ≤ (r₃ : ℝ))
    (hr₃up : (r₃ : ℝ) ≤ Real.sqrt ((n : ℝ) / (1 - 4 * σ)))
    (hfac : sizeFactor (3 * σ) 1 * Real.sqrt ((n : ℝ) / (1 - 4 * σ)) ≤
      (1 + δ) * Real.sqrt (n : ℝ))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ W : Hypergraph (Fin n), W ⊆ 𝓗 ∧ (∀ e : Set (Fin n), e ∈ W → edgeExtremal δ n e) ∧
      1 - δ ≤ volume n W := by
  classical
  refine ⟨W₂, ?_, ?_, ?_⟩
  · intro e he
    exact nonHuge_subset 𝓗 β (hB.hL₁sub (hB.hL₂sub (hB.hW₂sub he)))
  · intro e he
    refine ⟨?_, ?_⟩
    · have h1 : (r₃ : ℝ) ≤ (edgeSize e : ℝ) := by exact_mod_cast hB.hW₂size e he
      linarith
    · have h1 := hB.hW₂size_le e he
      have h3 : sizeFactor (3 * σ) 1 * (r₃ : ℝ) ≤
          sizeFactor (3 * σ) 1 * Real.sqrt ((n : ℝ) / (1 - 4 * σ)) :=
        mul_le_mul_of_nonneg_left hr₃up (le_of_lt (sizeFactor_pos (3 * σ) 1))
      linarith
  · rcases hB.hW₂vol with hemp | hvol
    · exact absurd hemp hW₂ne
    · have hδ : δ ^ 3 ≤ δ := by
        have hδ0' : (0 : ℝ) ≤ δ := le_of_lt hδ0
        have hsq : δ ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hsq hδ0']
      linarith

end

end ErdosFaberLovaszConjecture

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The sum of the edge sizes of a finite family, bounded by the number of
members times a common bound. -/
theorem sumEdgeSizes_le_of_card_le {s : Finset (Set (Fin n))} {m : ℕ} (hcard : s.card ≤ m)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ e : Set (Fin n), e ∈ s → (edgeSize e : ℝ) ≤ M) :
    (sumEdgeSizes s : ℝ) ≤ (m : ℝ) * M := by
  classical
  have h1 : (sumEdgeSizes s : ℝ) = s.sum (fun e : Set (Fin n) => (edgeSize e : ℝ)) := by
    simp [sumEdgeSizes, Nat.cast_sum]
  rw [h1]
  have h2 : s.sum (fun e : Set (Fin n) => (edgeSize e : ℝ)) ≤ s.card * M := by
    have := Finset.sum_le_card_nsmul s (fun e : Set (Fin n) => (edgeSize e : ℝ)) M hM
    rwa [nsmul_eq_mul] at this
  have h3 : (s.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hcard
  nlinarith

/-- The edge family of a colour class has at most as many members as the class. -/
theorem card_EdgeSetFamily_colorClass_le {𝓗 : Hypergraph (Fin n)}
    (φ : 𝓗.Coloring (Fin n)) (c : Fin n) :
    (EdgeSetFamily (φ.colorClass c)).card ≤ (φ.colorClass c).ncard := by
  classical
  have himg : EdgeSetFamily (φ.colorClass c)
      = ((Finset.univ : Finset 𝓗).filter (fun e : 𝓗 => e ∈ φ.colorClass c)).image
        (fun e : 𝓗 => (e : Set (Fin n))) := rfl
  rw [himg]
  refine (Finset.card_image_le).trans ?_
  have hfin : ((Finset.univ : Finset 𝓗).filter (fun e : 𝓗 => e ∈ φ.colorClass c)).card
      = (φ.colorClass c).ncard := by
    rw [Set.ncard_eq_toFinset_card (φ.colorClass c)]
    congr 1
    ext e
    simp [Set.Finite.mem_toFinset]
  rw [hfin]

/-- **A colour class with at most `m` edges of size at most `M` covers at most
`m·M` vertices.** -/
theorem classVertexCount_le_of_ncard_le {𝓗 : Hypergraph (Fin n)}
    (φ : 𝓗.Coloring (Fin n)) (c : Fin n) {m : ℕ} (hcard : (φ.colorClass c).ncard ≤ m)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ e : 𝓗, e ∈ φ.colorClass c → (edgeSize (e : Set (Fin n)) : ℝ) ≤ M) :
    (φ.classVertexCount c : ℝ) ≤ (m : ℝ) * M := by
  classical
  have h1 : φ.classVertexCount c
      = FamilyVertexCount (EdgeSetFamily (φ.colorClass c)) :=
    classVertexCount_eq_FamilyVertexCount φ c
  have h2 : FamilyVertexCount (EdgeSetFamily (φ.colorClass c))
      ≤ sumEdgeSizes (EdgeSetFamily (φ.colorClass c)) :=
    FamilyVertexCount_le_sumEdgeSizes _
  have h3 : (sumEdgeSizes (EdgeSetFamily (φ.colorClass c)) : ℝ) ≤ (m : ℝ) * M := by
    refine sumEdgeSizes_le_of_card_le ?_ hM0 ?_
    · exact le_trans (card_EdgeSetFamily_colorClass_le φ c) hcard
    · intro e he
      rcases (mem_EdgeSetFamily (φ.colorClass c) e).1 he with ⟨x, hx, rfl⟩
      exact hM x hx
  have : (φ.classVertexCount c : ℝ)
      ≤ (sumEdgeSizes (EdgeSetFamily (φ.colorClass c)) : ℝ) := by
    rw [h1]
    exact_mod_cast h2
  linarith

/-- **Lemma 5.1 (the paper's `extremal-case-lemma`), in the colouring API.**
For `δ` small there is `n₀` such that every linear hypergraph on `n ≥ n₀`
vertices whose edges all have size `≥ (1−δ)√n` has a proper edge-colouring
with at most `n` colours in which every colour class contains at most two
edges. -/
def NearfullColouring (δ₀ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ 𝓖 : Hypergraph (Fin n), 𝓖.IsLinear →
      (∀ e : Set (Fin n), e ∈ 𝓖 → (1 - δ) * Real.sqrt (n : ℝ) ≤ (edgeSize e : ℝ)) →
      ∃ φ : 𝓖.Coloring (Fin n), ∀ c : Fin n, (φ.colorClass c).ncard ≤ 2

/-- Lemma 5.1 restated in the colouring API, obtained from the commons
statement `Commons.Combinatorics.Hypergraph.linear_nearfull_colouring`. -/
theorem nearfullColouring_exists :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ NearfullColouring δ₀ := by
  obtain ⟨δ₀, hδ₀pos, hmain⟩ := Commons.Combinatorics.Hypergraph.linear_nearfull_colouring
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro δ hδ0 hδδ₀
  obtain ⟨n₀, hn₀⟩ := hmain δ hδ0 hδδ₀
  refine ⟨n₀, ?_⟩
  intro n hn 𝓖 hlin hsize
  have hlin' : ∀ e₁ ∈ 𝓖, ∀ e₂ ∈ 𝓖, e₁ ≠ e₂ → (e₁ ∩ e₂).Subsingleton := by
    intro e₁ he₁ e₂ he₂ hne
    exact hlin he₁ he₂ hne
  have hsize' : ∀ e ∈ 𝓖, (1 - δ) * Real.sqrt (n : ℝ) ≤ (e.ncard : ℝ) := by
    intro e he
    rw [← edgeSize_eq_ncard]
    exact hsize e he
  obtain ⟨φ, hproper, hcls⟩ := hn₀ n hn 𝓖 hlin' hsize'
  let ψ : 𝓖.Coloring (Fin n) := ⟨φ, fun e₁ e₂ hne h' => hproper e₁ e₂ hne h'⟩
  refine ⟨ψ, ?_⟩
  intro c
  haveI : Fintype 𝓖 := Fintype.ofFinite 𝓖
  have hfilter : ((Finset.univ : Finset 𝓖).filter (fun e : 𝓖 => φ e = c)).card ≤ 2 := by
    have h := hcls c
    rw [Nat.card_eq_fintype_card] at h
    simpa [Fintype.card_subtype] using h
  have hfs : (ψ.colorClass c).toFinite.toFinset
      = (Finset.univ : Finset 𝓖).filter (fun e : 𝓖 => ψ.labels e = c) := by
    ext e
    simp [Set.Finite.mem_toFinset, Hypergraph.Coloring.colorClass]
  rw [Set.ncard_eq_toFinset_card, hfs]
  simpa [ψ] using hfilter

/-- The `n₀`-indexed form of Lemma 5.1 (the output of `NearfullColouring`
with its threshold `n₀` extracted), as used in Case 2.2. -/
theorem nearfull_colouring_of {δ : ℝ} {n₀ : ℕ}
    (hLN : ∀ m : ℕ, n₀ ≤ m → ∀ 𝓖 : Hypergraph (Fin m), 𝓖.IsLinear →
      (∀ e : Set (Fin m), e ∈ 𝓖 → (1 - δ) * Real.sqrt (m : ℝ) ≤ (edgeSize e : ℝ)) →
      ∃ φ : 𝓖.Coloring (Fin m), ∀ c : Fin m, (φ.colorClass c).ncard ≤ 2)
    (hn : n₀ ≤ n) {𝓖 : Hypergraph (Fin n)} (hlin : 𝓖.IsLinear)
    (hsize : ∀ e : Set (Fin n), e ∈ 𝓖 → (1 - δ) * Real.sqrt (n : ℝ) ≤ (edgeSize e : ℝ)) :
    ∃ φ : 𝓖.Coloring (Fin n), ∀ c : Fin n, (φ.colorClass c).ncard ≤ 2 :=
  hLN n hn 𝓖 hlin hsize

/-- **Every class of a Lemma-5.1 colouring covers at most `2M` vertices**, when
all edges of the block have size at most `M`. -/
theorem classVertexCount_le_two_mul {𝓖 : Hypergraph (Fin n)} (φ : 𝓖.Coloring (Fin n))
    (hcls : ∀ c : Fin n, (φ.colorClass c).ncard ≤ 2) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ e : 𝓖, (edgeSize (e : Set (Fin n)) : ℝ) ≤ M) :
    ∀ c : Fin n, (φ.classVertexCount c : ℝ) ≤ 2 * M := by
  intro c
  exact classVertexCount_le_of_ncard_le φ c (hcls c) hM0 (fun e _ => hM e)

/-- **The classes of the left-block colouring that miss the huge edges cover at
most `(β/2)n` vertices**, since every edge of the block is small. -/
theorem case22_left_classes_le {𝓖 : Hypergraph (Fin n)} {β δ : ℝ}
    (φ : 𝓖.Coloring (Fin n)) (hcls : ∀ c : Fin n, (φ.colorClass c).ncard ≤ 2)
    (hsmall : ∀ e : 𝓖, (edgeSize (e : Set (Fin n)) : ℝ) ≤ δ * (n : ℝ) / 2)
    (hδ0 : 0 < δ) (hδβ : δ ≤ β / 2) :
    ∀ c : Fin n, (φ.classVertexCount c : ℝ) ≤ (β / 2) * (n : ℝ) := by
  intro c
  have hM0 : (0 : ℝ) ≤ δ * (n : ℝ) / 2 := by positivity
  have h := classVertexCount_le_two_mul φ hcls hM0 hsmall c
  nlinarith [h, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

/-- **The left block `𝓗₂^left = 𝓗_huge ∪ 𝓗₂^left` is coloured by Lemma 5.1**
(Claim of the paper: "there is a proper edge-colouring `φ₁` of `𝓗₂^left` using
a set `C` of at most `n` colours such that every colour is assigned to at most
two edges"). -/
theorem case22_left_colouring {δ : ℝ} {n₀ : ℕ}
    (hLN : ∀ m : ℕ, n₀ ≤ m → ∀ 𝓖 : Hypergraph (Fin m), 𝓖.IsLinear →
      (∀ e : Set (Fin m), e ∈ 𝓖 → (1 - δ) * Real.sqrt (m : ℝ) ≤ (edgeSize e : ℝ)) →
      ∃ φ : 𝓖.Coloring (Fin m), ∀ c : Fin m, (φ.colorClass c).ncard ≤ 2)
    (hn₀ : n₀ ≤ n) {𝓗 Left₂ : Hypergraph (Fin n)} {β : ℝ} {r₃ : ℕ}
    (hlin : 𝓗.IsLinear) (hL₂sub : Left₂ ⊆ 𝓗)
    (hsize₂ : ∀ e : Set (Fin n), e ∈ Left₂ → r₃ ≤ edgeSize e)
    (hr₃ : (1 - δ) * Real.sqrt (n : ℝ) ≤ (r₃ : ℝ))
    (hhuge : (1 - δ) * Real.sqrt (n : ℝ) ≤ β * (n : ℝ) / 4) :
    ∃ φ : (case2HugeLeft₂ β 𝓗 Left₂).Coloring (Fin n),
      ∀ c : Fin n, (φ.colorClass c).ncard ≤ 2 := by
  refine nearfull_colouring_of hLN hn₀ (hlin.mono ?_) ?_
  · intro e he
    rw [case2HugeLeft₂, Set.mem_union] at he
    rcases he with h | h
    · exact ((mem_hugeEdges 𝓗 β e).mp h).1
    · exact hL₂sub h
  · intro e he
    rw [case2HugeLeft₂, Set.mem_union] at he
    rcases he with h | h
    · have h1 := ((mem_hugeEdges 𝓗 β e).mp h).2
      linarith
    · have h1 : (r₃ : ℝ) ≤ (edgeSize e : ℝ) := by exact_mod_cast hsize₂ e h
      linarith

/-- **Class coverage of a Lemma-5.1 colouring of the left block**: at most
`δn` vertices per colour (the paper's `extremal-huge-edge`). -/
theorem case22_classVertexCount_le {𝓖 : Hypergraph (Fin n)} {δ : ℝ}
    (φ : 𝓖.Coloring (Fin n)) (hcls : ∀ c : Fin n, (φ.colorClass c).ncard ≤ 2)
    (hδ0 : 0 < δ)
    (hsmall : ∀ e : 𝓖, (edgeSize (e : Set (Fin n)) : ℝ) ≤ δ * (n : ℝ) / 2) :
    ∀ c : Fin n, (φ.classVertexCount c : ℝ) ≤ δ * (n : ℝ) := by
  intro c
  have hM0 : (0 : ℝ) ≤ δ * (n : ℝ) / 2 := by positivity
  have h := classVertexCount_le_two_mul φ hcls hM0 hsmall c
  linarith

/-- **`r₂ ≥ 2r₀` in Case 2.2** (paper: `W₁ ∩ W₂ ≠ ∅` gives `r₂ ≥ γ₂^{10} r₃`,
and `r₃ ≥ (1−δ)√n ≫ r₀`). -/
theorem r₀_lt_r₂_of_blocks {n r₀ : ℕ} {β γ₂ σ δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂}
    {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hr₂r₃ : γ₂ ^ 10 * (r₃ : ℝ) ≤ (r₂ : ℝ))
    (hr₀ : 2 * (r₀ : ℝ) ≤ γ₂ ^ 10 * (1 - δ) * Real.sqrt (n : ℝ))
    (hγ₂ : 0 < γ₂) (h2r₀ : 2 ≤ r₀) (hr₃ : (1 - δ) * Real.sqrt (n : ℝ) ≤ (r₃ : ℝ)) :
    r₀ < r₂ := by
  have hγ10 : 0 < γ₂ ^ 10 := by positivity
  have hstep : γ₂ ^ 10 * ((1 - δ) * Real.sqrt (n : ℝ)) ≤ γ₂ ^ 10 * (r₃ : ℝ) :=
    mul_le_mul_of_nonneg_left hr₃ (le_of_lt hγ10)
  rw [mul_assoc] at hr₀
  have h1 : 2 * (r₀ : ℝ) ≤ (r₂ : ℝ) := le_trans hr₀ (le_trans hstep hr₂r₃)
  have h2 : (r₀ : ℝ) < (r₂ : ℝ) := by
    have hr0 : (1 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast (by omega : 1 ≤ r₀)
    linarith
  exact_mod_cast h2

/-- **In Case 2.2 the medium edges lie in `𝓗₁^good`** (paper: `𝓗_med ∩
𝓗₁^left = ∅` by `(d2)` and `r₂ ≥ 2r₀`, so `𝓗_med ⊆ 𝓗₁^good`). -/
theorem medEdges_subset_good₁ {n r₁ r₀ : ℕ} {β γ₂ σ δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂}
    {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hβn : (r₀ : ℝ) < β * (n : ℝ) / 4) (hr₀r₂ : r₀ < r₂) :
    𝓗.medEdges r₁ r₀ ⊆ Good₁ := by
  intro e he
  obtain ⟨he𝓗, -, hle⟩ := he
  have hnr : ¬ (β * (n : ℝ) / 4 ≤ (edgeSize e : ℝ)) := by
    intro hc
    have h2 : (edgeSize e : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hle
    linarith
  have hnh : e ∈ nonHuge 𝓗 β := ⟨he𝓗, hnr⟩
  have hcov : e ∈ Good₁ ∪ Left₁ := by
    rw [hB.hpart₁]
    exact hnh
  rw [Set.mem_union] at hcov
  rcases hcov with h | h
  · exact h
  · exfalso
    have hge := hB.hsize₁ ⟨e, hnh⟩ h
    have h2 : (r₂ : ℝ) ≤ (edgeSize e : ℝ) := by exact_mod_cast hge
    have h3 : (edgeSize e : ℝ) ≤ (r₂ : ℝ) := by
      have : (edgeSize e : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hle
      have : (r₀ : ℝ) < (r₂ : ℝ) := by exact_mod_cast hr₀r₂
      linarith
    have : (r₂ : ℝ) < (r₂ : ℝ) := by linarith
    exact lt_irrefl _ this

end

end ErdosFaberLovaszConjecture
