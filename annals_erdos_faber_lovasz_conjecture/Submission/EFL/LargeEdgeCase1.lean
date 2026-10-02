import Submission.EFL.ColourUnion
import Submission.EFL.MedEdges
import Submission.EFL.GreedyListColouring
import Submission.EFL.Counting

/-!
# Theorem 6.1, Case 1: the non-extremal alternative from a good ordering

This module formalises the first case of the proof of the paper's
`large-edge-thm` (Theorem 6.1), namely the passage

> a linear hypergraph `𝓗` all of whose edges have size `> r₁`, together with
> an ordering of `𝓗_large` (the edges of size `> r₀`) whose *preceding
> degrees* are all at most `(1−2σ)n`,

⟹ the *non-extremal* alternative `LargeEdgeNonExtremal n σ γ₁ β r₁ r₀ 𝓗`:

* the large edges are coloured by Proposition 6.9 (greedy list colouring
  along the ordering, `prop69_colouring`), with `r₀, σ/2, β/5` playing
  the roles of `r, α₁, α₂`, using colours from a set `C_large` of size
  at most `(1−3σ/2)n` disjoint from `Cmed`;
* the medium edges are coloured by Proposition 6.10
  (`medEdges_colouring_of_chi`) with a `γ₁`-bounded colouring using at most
  `γ₁n` colours from a set `Cmed`;
* the two colourings are combined with `coloringUnionOfCover`.

The mathematical content is the verification of properties (6.1:a)(i)–(iii)
of the paper, whose formal counterparts are the conjuncts of
`LargeEdgeNonExtremal`: hueg colour classes are singletons, medium edges get
colours from `Cmed` (each covering few vertices), and every other colour
class not assigned to a huge edge covers at most `βn` vertices.

The parameter hypotheses are the explicit `≪`-hierarchy instances the paper
leaves implicit: `r₀ < βn/4` (huge edges are large), `γ₁ ≤ σ/2`, the two
Proposition 6.9 margins, and the colour budget `|Cmed| + 1 ≤ σn/2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Elementary colour-class lemmas -/

/-- Linearity is inherited by sub-hypergraphs. -/
theorem IsLinear.mono {V : Type*} {𝓖 𝓗 : Hypergraph V} (hsub : 𝓖 ⊆ 𝓗)
    (hlin : 𝓗.IsLinear) : 𝓖.IsLinear :=
  Set.Pairwise.mono hsub hlin

/-- A finite set of cardinality at most one is empty or a singleton. -/
theorem eq_empty_or_singleton_of_ncard_le_one {α : Type*} {s : Set α} (hs : s.Finite)
    (h : s.ncard ≤ 1) : s = ∅ ∨ ∃ a, s = {a} :=
  (Set.ncard_le_one_iff_eq hs).mp h

/-- The colour class of `c` is a single edge exactly when the class covers
exactly the vertices of that edge. -/
theorem classVertices_eq_of_colorClass_eq_singleton {𝓗 : Hypergraph (Fin n)}
    (φ : 𝓗.Coloring (Fin n)) {c : Fin n} {e : 𝓗} (h : φ.colorClass c = {e}) :
    φ.classVertices c = (e : Set (Fin n)) := by
  ext v
  rw [mem_classVertices, h]
  simp

/-- An empty colour class covers no vertices. -/
theorem classVertices_eq_empty_of_colorClass_eq_empty {𝓗 : Hypergraph (Fin n)}
    (φ : 𝓗.Coloring (Fin n)) {c : Fin n} (h : φ.colorClass c = ∅) :
    φ.classVertices c = ∅ := by
  ext v
  rw [mem_classVertices, h]
  simp

/-- A colour class whose colour is outside the colour set used by a colouring
is empty. -/
theorem classVertices_eq_empty_of_notMem_usesColourSet {𝓗 : Hypergraph (Fin n)}
    {φ : 𝓗.Coloring (Fin n)} {C : Finset (Fin n)} (hφ : φ.UsesColourSet C)
    {c : Fin n} (hc : c ∉ C) : φ.classVertices c = ∅ := by
  ext v
  rw [mem_classVertices]
  constructor
  · rintro ⟨e, hcl, _hv⟩
    exact absurd (hcl ▸ hφ e) hc
  · intro hv
    exact absurd hv (Set.notMem_empty v)

/-- If `e` is in the colour class `c`, then the class covers at least the
vertices of `e`. -/
theorem edgeSize_le_classVertexCount_of_mem_colorClass {𝓗 : Hypergraph (Fin n)}
    (φ : 𝓗.Coloring (Fin n)) {c : Fin n} {e : 𝓗} (he : e ∈ φ.colorClass c) :
    edgeSize (e : Set (Fin n)) ≤ φ.classVertexCount c := by
  have hsub : (e : Set (Fin n)) ⊆ φ.classVertices c := by
    intro v hv
    rw [mem_classVertices]
    exact ⟨e, he, hv⟩
  have h := Set.ncard_le_ncard hsub
  show edgeSize (e : Set (Fin n)) ≤ (φ.classVertices c).ncard
  rwa [edgeSize_eq_ncard]

/-- The class vertex count is invariant under equality of the covered vertex
sets. -/
theorem classVertexCount_eq_of_classVertices_eq {𝓗 : Hypergraph (Fin n)}
    (φ : 𝓗.Coloring (Fin n)) {c : Fin n} {S : Set (Fin n)}
    (h : φ.classVertices c = S) : φ.classVertexCount c = S.ncard := by
  rw [Hypergraph.Coloring.classVertexCount, h]

/-- A singleton colour class covers exactly the vertices of its edge. -/
theorem classVertexCount_eq_edgeSize_of_singleton {𝓗 : Hypergraph (Fin n)}
    (φ : 𝓗.Coloring (Fin n)) {c : Fin n} {e : 𝓗} (h : φ.colorClass c = {e}) :
    φ.classVertexCount c = edgeSize (e : Set (Fin n)) := by
  rw [Hypergraph.Coloring.classVertexCount,
    classVertices_eq_of_colorClass_eq_singleton φ h, edgeSize_eq_ncard]

/-- An empty colour class covers no vertices. -/
theorem classVertexCount_eq_zero_of_classVertices_eq_empty {𝓗 : Hypergraph (Fin n)}
    (φ : 𝓗.Coloring (Fin n)) {c : Fin n} (h : φ.classVertices c = ∅) :
    φ.classVertexCount c = 0 := by
  rw [Hypergraph.Coloring.classVertexCount, h]; simp

/-- A non-empty colour class of cardinality at most one is a singleton. -/
theorem exists_colorClass_eq_singleton_of_ncard_le_one {𝓗 : Hypergraph (Fin n)}
    (φ : 𝓗.Coloring (Fin n)) {c : Fin n} (h1 : (φ.colorClass c).ncard ≤ 1) {e : 𝓗}
    (he : e ∈ φ.colorClass c) : ∃ e₀ : 𝓗, φ.colorClass c = {e₀} := by
  have hfin : (φ.colorClass c).Finite := Set.toFinite _
  rcases eq_empty_or_singleton_of_ncard_le_one hfin h1 with h | h
  · rw [h] at he; exact absurd he (Set.notMem_empty e)
  · exact h

/-- A finset of `Fin n` of prescribed cardinality disjoint from a given one. -/
theorem exists_finset_disjoint_card {n : ℕ} (T : Finset (Fin n)) (k : ℕ)
    (h : T.card + k ≤ n) : ∃ C : Finset (Fin n), Disjoint C T ∧ C.card = k := by
  classical
  have hle : k ≤ (Finset.univ \ T).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hle
  refine ⟨C, ?_, hCcard⟩
  rw [Finset.disjoint_left]
  intro x hx hxT
  have := hCsub hx
  exact (Finset.mem_sdiff.mp this).2 hxT

/-! ## Covering `𝓗` by its large and medium edges -/

/-- Under the standing hypothesis `|e| > r₁` for every edge, the large and
medium edge classes cover `𝓗`. -/
theorem cover_large_med_edges {r₁ r₀ : ℕ} {𝓗 : Hypergraph (Fin n)}
    (hsize : ∀ e : 𝓗, r₁ < edgeSize (e : Set (Fin n))) :
    ∀ e ∈ 𝓗, e ∈ 𝓗.largeEdges r₀ ∨ e ∈ 𝓗.medEdges r₁ r₀ := by
  intro e he
  by_cases h : r₀ < edgeSize e
  · exact Or.inl (by rw [mem_largeEdges]; exact ⟨he, h⟩)
  · exact Or.inr (by rw [mem_medEdges]; exact ⟨he, hsize ⟨e, he⟩, not_lt.mp h⟩)

/-- the large and medium edge classes are disjoint -/
theorem disjoint_large_med_edges (𝓗 : Hypergraph (Fin n)) (r₁ r₀ : ℕ) :
    Disjoint (𝓗.largeEdges r₀) (𝓗.medEdges r₁ r₀) := by
  rw [Set.disjoint_left]
  intro e hl hm
  have h1 : r₀ < edgeSize e := ((mem_largeEdges 𝓗 r₀ e).mp hl).2
  have h2 : edgeSize e ≤ r₀ := ((mem_medEdges 𝓗 r₁ r₀ e).mp hm).2.2
  exact absurd h2 (not_le.mpr h1)

/-- The paper's `edgeMedium` at natural thresholds is membership in
`𝓗.medEdges`. -/
theorem edgeMedium_iff_mem_medEdges {r₁ r₀ : ℕ} {𝓗 : Hypergraph (Fin n)}
    {e : Set (Fin n)} (he : e ∈ 𝓗) :
    edgeMedium (r₁ : ℝ) (r₀ : ℝ) e ↔ e ∈ 𝓗.medEdges r₁ r₀ := by
  rw [mem_medEdges]
  exact ⟨fun h => ⟨he, Nat.cast_lt.mp h.1, Nat.cast_le.mp h.2⟩,
    fun h => ⟨Nat.cast_lt.mpr h.2.1, Nat.cast_le.mpr h.2.2⟩⟩

/-! ## Step 1: the colouring of the large edges by Proposition 6.9 -/

/-- **Proposition 6.9 applied to the large edges.**  For a linear `𝓗`, an
ordering of `𝓗_large` whose preceding degrees are all at most `(1−2σ)n`, and
a colour set `C` of size at least `(1−3σ/2)n`, the greedy list colouring
engine produces a proper edge-colouring of `𝓗_large` with colours from `C`
which is `β/5`-bounded (paper: Proposition 6.9 with `r₀, σ/2, β/5` in the
roles of `r, α₁, α₂`). -/
theorem largeEdges_colouring_of_prop69 {n r r₀ : ℕ} {σ β : ℝ} {𝓗 : Hypergraph (Fin n)}
    (hlin : 𝓗.IsLinear) (h2n : 2 ≤ n) (h2r : 2 ≤ r) (hσ : 0 < σ) (hβ : 0 < β)
    (hmargin : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((r : ℝ) - 1)) <
      ((σ / 2) * (n : ℝ)) / 4)
    (hbig : ((bigFinset (β / 5) (𝓗.largeEdges r₀)).card : ℝ) < ((σ / 2) * (n : ℝ)) / 2)
    (hsize : ∀ e : 𝓗.largeEdges r₀, r ≤ edgeSize (e : Set (Fin n)))
    {k : ℕ} (ord : (𝓗.largeEdges r₀) ≃ Fin k)
    (hgood : ∀ e : 𝓗.largeEdges r₀,
      (precedingDegree (𝓗.largeEdges r₀) ord e : ℝ) ≤ (1 - 2 * σ) * (n : ℝ))
    (C : Finset (Fin n)) (hC : (1 - 3 * σ / 2) * (n : ℝ) ≤ (C.card : ℝ)) :
    ∃ φ : (𝓗.largeEdges r₀).Coloring (Fin n), φ.UsesColourSet C ∧ φ.AlphaBounded (β / 5) := by
  classical
  have hlinL : (𝓗.largeEdges r₀).IsLinear := IsLinear.mono (largeEdges_subset 𝓗 r₀) hlin
  have hlist : ∀ e : 𝓗.largeEdges r₀,
      ((precedingDegree (𝓗.largeEdges r₀) ord e : ℝ) + (σ / 2) * (n : ℝ)) ≤
        ((fun _ : 𝓗.largeEdges r₀ => C) e).card := by
    intro e
    have h1 := hgood e
    have h3 : (1 - 3 * σ / 2) * (n : ℝ) ≤ ((fun _ : 𝓗.largeEdges r₀ => C) e).card := hC
    have h2 : (1 - 3 * σ / 2) * (n : ℝ) =
        (1 - 2 * σ) * (n : ℝ) + (σ / 2) * (n : ℝ) := by ring
    linarith
  obtain ⟨φ, hb, hmem⟩ :=
    prop69_colouring (n := n) (r := r) (k := k) (α₁ := σ / 2) (α₂ := β / 5)
      (𝓗 := 𝓗.largeEdges r₀) h2n h2r (by linarith) hmargin hbig hlinL hsize ord
      (fun _ => C) hlist
  exact ⟨φ, hmem, hb⟩

/-! ## Step 2: the assembly of the non-extremal alternative

Given the two colourings (large edges with `C_large`, medium edges with
`Cmed`) we combine them and verify (6.1:a)(i)–(iii). -/

/-- **The assembly of the non-extremal alternative.** -/
theorem largeEdge_nonExtremal_of_colourings {n r₁ r₀ : ℕ} {σ γ₁ β : ℝ}
    {𝓗 : Hypergraph (Fin n)}
    (hn : 0 < n) (hsize : ∀ e : 𝓗, r₁ < edgeSize (e : Set (Fin n)))
    (hβ : 0 < β) (hγ₁σ : γ₁ ≤ σ / 2)
    (hβn : (r₀ : ℝ) < β * (n : ℝ) / 4)
    {C_large Cmed : Finset (Fin n)} (hdisjCL : Disjoint C_large Cmed)
    (hbudgetL : (C_large.card : ℝ) + (Cmed.card : ℝ) ≤ (1 - σ) * (n : ℝ))
    {φL : (𝓗.largeEdges r₀).Coloring (Fin n)} (hφL : φL.UsesColourSet C_large)
    (hαL : φL.AlphaBounded (β / 5))
    {φmed : (𝓗.medEdges r₁ r₀).Coloring (Fin n)} (hφmed : φmed.UsesColourSet Cmed)
    (hmedb : ∀ c : Fin n, (φmed.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ))
    (hCmed : (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ)) :
    LargeEdgeNonExtremal n σ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 := by
  classical
  have hsubL : 𝓗.largeEdges r₀ ⊆ 𝓗 := largeEdges_subset 𝓗 r₀
  have hsubM : 𝓗.medEdges r₁ r₀ ⊆ 𝓗 := medEdges_subset 𝓗 r₁ r₀
  have hcover : ∀ e ∈ 𝓗, e ∈ 𝓗.largeEdges r₀ ∨ e ∈ 𝓗.medEdges r₁ r₀ :=
    cover_large_med_edges hsize
  have hdisjG : Disjoint (𝓗.largeEdges r₀) (𝓗.medEdges r₁ r₀) :=
    disjoint_large_med_edges 𝓗 r₁ r₀
  let φ : 𝓗.Coloring (Fin n) :=
    coloringUnionOfCover hsubL hsubM hcover hdisjG hdisjCL φL φmed hφL hφmed
  have hφdef : φ = coloringUnionOfCover hsubL hsubM hcover hdisjG hdisjCL φL φmed hφL hφmed :=
    rfl
  have hφlabel : ∀ e : 𝓗, φ.labels e = unionLabel hsubL hsubM hcover φL φmed e := by
    intro e
    rw [hφdef]
    rfl
  -- class-vertex transport
  have hcvL : ∀ c : Fin n, c ∈ C_large → φ.classVertices c = φL.classVertices c := by
    intro c hc
    rw [hφdef]
    exact classVertices_coloringUnionOfCover_left hφL hφmed hc
  have hcvM : ∀ c : Fin n, c ∉ C_large → φ.classVertices c = φmed.classVertices c := by
    intro c hc
    rw [hφdef]
    exact classVertices_coloringUnionOfCover_right hφL hφmed hc
  have hclassL : ∀ c : Fin n, c ∈ C_large → ∀ e₀ : 𝓗.largeEdges r₀,
      φL.colorClass c = {e₀} →
      φ.colorClass c = {⟨(e₀ : Set (Fin n)), hsubL e₀.2⟩} := by
    intro c hc e₀ hs
    rw [hφdef]
    exact colorClass_coloringUnionOfCover_left hφL hφmed hc hs
  -- (i) huge colour classes are singletons
  have hsing : φ.SingletonClassesForHuge β := by
    intro c hc
    obtain ⟨e, hcli, hbig⟩ := hc
    have heL : (e : Set (Fin n)) ∈ 𝓗.largeEdges r₀ := by
      rw [mem_largeEdges]
      refine ⟨e.2, ?_⟩
      exact_mod_cast (lt_of_lt_of_le hβn hbig :
        (r₀ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ))
    have hlab : φ.labels e = φL.labels ⟨(e : Set (Fin n)), heL⟩ := by
      rw [hφlabel, unionLabel_of_mem heL]
    have hmemL : (⟨(e : Set (Fin n)), heL⟩ : 𝓗.largeEdges r₀) ∈ φL.colorClass c := by
      rw [mem_colorClass]
      exact hlab.symm.trans hcli
    have hcL : c ∈ C_large := by
      have hEq : φL.labels ⟨(e : Set (Fin n)), heL⟩ = c := hlab.symm.trans hcli
      rw [← hEq]
      exact hφL _
    have hncard : (φL.colorClass c).ncard ≤ 1 := by
      rcases (AlphaBounded_iff_classVertexCount (β / 5) φL).mp hαL c with h1 | h2
      · exact h1
      · exfalso
        have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hb5 : β * (n : ℝ) / 4 = (5 / 4) * ((β / 5) * (n : ℝ)) := by ring
        have h3 : ((β / 5) * (n : ℝ)) < (edgeSize (e : Set (Fin n)) : ℝ) := by
          nlinarith [hbig, hb5, hβ, hnn]
        have h4 : (edgeSize (e : Set (Fin n)) : ℝ) ≤ (φL.classVertexCount c : ℝ) := by
          exact_mod_cast edgeSize_le_classVertexCount_of_mem_colorClass φL hmemL
        linarith
    obtain ⟨e₀, hs⟩ := exists_colorClass_eq_singleton_of_ncard_le_one φL hncard hmemL
    exact ⟨⟨(e₀ : Set (Fin n)), hsubL e₀.2⟩, hclassL c hcL e₀ hs⟩
  -- (ii) medium edges' colours cover few vertices
  have hclassMed : ∀ c ∈ Cmed, (φ.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ) := by
    intro c hc
    have hcL : c ∉ C_large := fun h => Finset.disjoint_left.mp hdisjCL h hc
    have h2 : (φ.classVertexCount c : ℝ) = (φmed.classVertexCount c : ℝ) := by
      rw [classVertexCount_eq_of_classVertices_eq φ (hcvM c hcL)]
      rfl
    rw [h2]
    exact hmedb c
  -- (iii) colour classes outside `Cmed` not assigned to huge edges cover `≤ βn`
  have hclassOther : ∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c →
      (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ) := by
    intro c _hcM hnot
    rcases Decidable.em (c ∈ C_large) with hcL | hcL
    · rcases (AlphaBounded_iff_classVertexCount (β / 5) φL).mp hαL c with h1 | h2
      · have hfin : (φL.colorClass c).Finite := Set.toFinite _
        rcases eq_empty_or_singleton_of_ncard_le_one hfin h1 with hem | ⟨e₀, hs⟩
        · have hz : φ.classVertexCount c = 0 := by
            rw [classVertexCount_eq_of_classVertices_eq φ
              (by rw [hcvL c hcL, classVertices_eq_empty_of_colorClass_eq_empty φL hem])]
            simp
          rw [hz]
          simp only [Nat.cast_zero]
          have : (0 : ℝ) ≤ β * (n : ℝ) := by positivity
          linarith
        · have hcl : φ.colorClass c = {⟨(e₀ : Set (Fin n)), hsubL e₀.2⟩} :=
            hclassL c hcL e₀ hs
          have hlt : (edgeSize (e₀ : Set (Fin n)) : ℝ) < β * (n : ℝ) / 4 := by
            by_contra hcon
            exact hnot ⟨_, hcl.symm ▸ Set.mem_singleton _, not_lt.mp hcon⟩
          have hcv2 : (φ.classVertexCount c : ℝ) = (edgeSize (e₀ : Set (Fin n)) : ℝ) := by
            rw [classVertexCount_eq_edgeSize_of_singleton φ hcl]
          rw [hcv2]
          have : (0 : ℝ) < β * (n : ℝ) := by positivity
          linarith
      · have h3 : (φ.classVertexCount c : ℝ) ≤ (β / 5) * (n : ℝ) := by
          rw [classVertexCount_eq_of_classVertices_eq φ (hcvL c hcL)]
          exact h2
        have : (0 : ℝ) ≤ (n : ℝ) := by positivity
        nlinarith [h3, hβ, this]
    · have hz : φ.classVertexCount c = 0 := by
        rw [classVertexCount_eq_of_classVertices_eq φ
          (by rw [hcvM c hcL, classVertices_eq_empty_of_notMem_usesColourSet hφmed ‹_›])]
        simp
      rw [hz]
      simp only [Nat.cast_zero]
      have : (0 : ℝ) ≤ β * (n : ℝ) := by positivity
      linarith
  have huses : φ.UsesColourSet (C_large ∪ Cmed) := by
    have h := coloringUnionOfCover_usesColourSet (h₁ := hsubL) (h₂ := hsubM)
      (hcover := hcover) (hdisjG := hdisjG) (hdisj := hdisjCL) hφL hφmed
    rwa [← hφdef] at h
  have hcardUnion : ((C_large ∪ Cmed).card : ℝ) ≤ (1 - σ) * (n : ℝ) := by
    have hcu : (C_large ∪ Cmed).card = C_large.card + Cmed.card :=
      Finset.card_union_of_disjoint hdisjCL
    rw [hcu]
    exact_mod_cast hbudgetL
  refine ⟨φ, C_large ∪ Cmed, Cmed, huses, hcardUnion, Finset.subset_union_right, hCmed,
    ?_, hclassMed, hsing, hclassOther⟩
  intro e he
  have heM : (e : Set (Fin n)) ∈ 𝓗.medEdges r₁ r₀ :=
    (edgeMedium_iff_mem_medEdges e.2).mp he
  have heNotL : (e : Set (Fin n)) ∉ 𝓗.largeEdges r₀ :=
    fun h => (Set.disjoint_left.mp hdisjG) h heM
  have hlab : φ.labels e = φmed.labels ⟨(e : Set (Fin n)), heM⟩ := by
    rw [hφlabel, unionLabel_of_notMem heNotL]
  rw [hlab]
  exact hφmed _


/-! ## Theorem 6.1, Case 1 -/

/-- **Theorem 6.1, Case 1: the non-extremal alternative from a good ordering
of the large edges.**  This is the first case of the proof of the paper's
`large-edge-thm`: if the ordering of the large edges produced by the
Figure-3 reordering is *good* (all preceding degrees at most `(1−2σ)n`),
then the non-extremal alternative `LargeEdgeNonExtremal` holds. -/
theorem largeEdge_case1 {n r₁ r₀ : ℕ} {σ γ₁ β : ℝ} {𝓗 : Hypergraph (Fin n)}
    (hlin : 𝓗.IsLinear) (h2n : 2 ≤ n) (hr₀ : 1 ≤ r₀) (hσ : 0 < σ) (hσ23 : σ ≤ 2 / 3)
    (hsize : ∀ e : 𝓗, r₁ < edgeSize (e : Set (Fin n)))
    (hβ : 0 < β) (hγ₁σ : γ₁ ≤ σ / 2)
    (hβn : (r₀ : ℝ) < β * (n : ℝ) / 4)
    (hmargin : (2 : ℝ) * (n : ℝ) / ((β / 5) * (r₀ : ℝ)) < ((σ / 2) * (n : ℝ)) / 4)
    (hbig : ((bigFinset (β / 5) (𝓗.largeEdges r₀)).card : ℝ) < ((σ / 2) * (n : ℝ)) / 2)
    {k : ℕ} (ord : (𝓗.largeEdges r₀) ≃ Fin k)
    (hgood : ∀ e : 𝓗.largeEdges r₀,
      (precedingDegree (𝓗.largeEdges r₀) ord e : ℝ) ≤ (1 - 2 * σ) * (n : ℝ))
    {φmed : (𝓗.medEdges r₁ r₀).Coloring (Fin n)} {Cmed : Finset (Fin n)}
    (hφmed : φmed.UsesColourSet Cmed) (hCmed : (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ))
    (hmedb : ∀ c : Fin n, (φmed.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ))
    (hbudget : (Cmed.card : ℝ) + 1 ≤ (σ / 2) * (n : ℝ)) :
    LargeEdgeNonExtremal n σ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 := by
  classical
  set kL : ℕ := Nat.ceil ((1 - 3 * σ / 2) * (n : ℝ)) with hkLdef
  have hkl1 : (1 - 3 * σ / 2) * (n : ℝ) ≤ (kL : ℝ) := Nat.le_ceil _
  have hnonneg : (0 : ℝ) ≤ (1 - 3 * σ / 2) * (n : ℝ) :=
    mul_nonneg (by linarith) (Nat.cast_nonneg n)
  have hkl2 : (kL : ℝ) < (1 - 3 * σ / 2) * (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one hnonneg
  have hbudget' : Cmed.card + kL ≤ n := by
    have hsum : ((Cmed.card + kL : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      nlinarith [hbudget, hkl2]
    exact_mod_cast hsum
  obtain ⟨C_large, hdisjCL, hcardCL⟩ := exists_finset_disjoint_card Cmed kL hbudget'
  have hbudgetL : (C_large.card : ℝ) + (Cmed.card : ℝ) ≤ (1 - σ) * (n : ℝ) := by
    rw [hcardCL]
    nlinarith [hbudget, hkl2]
  have hsizeL : ∀ e : 𝓗.largeEdges r₀, r₀ + 1 ≤ edgeSize (e : Set (Fin n)) := by
    intro e
    have := ((mem_largeEdges 𝓗 r₀ e).mp e.2).2
    omega
  have hCml : (C_large.card : ℝ) = (kL : ℝ) := by rw [hcardCL]
  have hmargin' : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((↑(r₀ + 1) : ℝ) - 1)) <
      ((σ / 2) * (n : ℝ)) / 4 := by
    have h : ((↑(r₀ + 1) : ℝ) - 1) = (r₀ : ℝ) := by push_cast; ring
    rw [h]; exact hmargin
  obtain ⟨φL, hφL, hαL⟩ :=
    largeEdges_colouring_of_prop69 (r := r₀ + 1) (r₀ := r₀) hlin h2n (by omega) hσ hβ
      hmargin' hbig hsizeL ord hgood C_large (by rw [hCml]; exact hkl1)
  exact largeEdge_nonExtremal_of_colourings (by omega) hsize hβ hγ₁σ hβn hdisjCL hbudgetL
    hφL hαL hφmed hmedb hCmed


/-! ## Counting the huge edges -/

/-- **The number of huge edges is `O(1/β²)`.**  In a linear hypergraph on
`Fin n`, at most `32/β²` edges have size at least `βn/4` (for `βn ≥ 8`).
This is the formal counterpart of (a) in the proof of Theorem 6.1
(`e(𝓗_huge) ≤ 8/β`), in the pair-counting form used by the development:
`∑_e |e|(|e|−1) ≤ n(n−1)`. -/
theorem card_huge_le {n : ℕ} {β : ℝ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) (hβ : 0 < β) (hβn : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n) :
    (((Finset.univ : Finset 𝓗).filter (fun e : 𝓗 =>
        β * (n : ℝ) / 4 ≤ (edgeSize (e : Set (Fin n)) : ℝ))).card : ℝ) ≤ 32 / β ^ 2 := by
  classical
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h : (0 : ℝ) < β * (n : ℝ) := lt_of_lt_of_le (by norm_num) hβn
    exact (mul_pos_iff_of_pos_left hβ).mp h
  have hs2 : 2 ≤ ⌈β * (n : ℝ) / 4⌉₊ := by
    have h2 : (2 : ℝ) ≤ β * (n : ℝ) / 4 := by linarith
    calc (2 : ℕ) = ⌈(2 : ℝ)⌉₊ := by simp
      _ ≤ ⌈β * (n : ℝ) / 4⌉₊ := Nat.ceil_mono h2
  set s : ℕ := ⌈β * (n : ℝ) / 4⌉₊ with hsdef
  have hs1 : 1 ≤ s := by omega
  have hsub : (Finset.univ.filter (fun e : 𝓗 =>
        β * (n : ℝ) / 4 ≤ (edgeSize (e : Set (Fin n)) : ℝ)))
      ⊆ (Finset.univ.filter (fun e : 𝓗 => s ≤ edgeSize (e : Set (Fin n)))) := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    rw [hsdef]
    exact Nat.ceil_le.mpr he
  have hcard := Finset.card_le_card hsub
  have hcount := card_edges_size_ge_le (𝓗 := 𝓗) hlin hs2
  rw [hsdef] at hcount
  have hcast1 : (((Finset.univ.filter (fun e : 𝓗 =>
        s ≤ edgeSize (e : Set (Fin n)))).card : ℕ) : ℝ) ≤
      ((n * (n - 1) / (s * (s - 1)) : ℕ) : ℝ) := by
    exact_mod_cast hcount
  have hcast2 : ((n * (n - 1) / (s * (s - 1)) : ℕ) : ℝ) ≤
      (n : ℝ) * ((n : ℝ) - 1) / ((s : ℝ) * ((s : ℝ) - 1)) := by
    refine le_trans Nat.cast_div_le ?_
    have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn1]; norm_num
    have h2 : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
      rw [Nat.cast_sub hs1]; norm_num
    rw [Nat.cast_mul, Nat.cast_mul, h1, h2]
  have hsge : β * (n : ℝ) / 4 ≤ (s : ℝ) := by rw [hsdef]; exact Nat.le_ceil _
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  have hbb : β ^ 2 * (n : ℝ) ^ 2 / 32 ≤ (s : ℝ) * ((s : ℝ) - 1) := by
    have h1 : (s : ℝ) / 2 ≤ (s : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs2
      linarith
    have h2 : (s : ℝ) * ((s : ℝ) / 2) ≤ (s : ℝ) * ((s : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hspos)
    have h3 : (β * (n : ℝ) / 4) * (β * (n : ℝ) / 4) ≤ (s : ℝ) * (s : ℝ) :=
      mul_self_le_mul_self (by positivity) hsge
    nlinarith [h2, h3]
  have hden : (0 : ℝ) < (s : ℝ) * ((s : ℝ) - 1) := by
    have : (0 : ℝ) < (s : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs2
      linarith
    positivity
  have hnum : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) ^ 2 := by nlinarith [hnpos]
  have hb2 : (0 : ℝ) < β ^ 2 := by positivity
  have h4 : β ^ 2 * ((n : ℝ) * ((n : ℝ) - 1)) ≤ β ^ 2 * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hnum (le_of_lt hb2)
  have hbb' : β ^ 2 * (n : ℝ) ^ 2 ≤ 32 * ((s : ℝ) * ((s : ℝ) - 1)) := by linarith [hbb]
  have hfinal : (n : ℝ) * ((n : ℝ) - 1) / ((s : ℝ) * ((s : ℝ) - 1)) ≤ 32 / β ^ 2 := by
    rw [div_le_div_iff₀ hden hb2]
    nlinarith [hbb', h4]
  have hcard' : (((Finset.univ.filter (fun e : 𝓗 =>
        β * (n : ℝ) / 4 ≤ (edgeSize (e : Set (Fin n)) : ℝ))).card : ℕ) : ℝ) ≤
      (((Finset.univ.filter (fun e : 𝓗 => s ≤ edgeSize (e : Set (Fin n)))).card : ℕ) : ℝ) := by
    exact_mod_cast hcard
  linarith [hcard', hcast1, hcast2, hfinal]


/-- The huge-edge count in subfamily form: a linear hypergraph on `Fin n` has
at most `32/β²` edges of size `≥ βn/4`. -/
theorem natCard_hugeEdges_le {n : ℕ} {β : ℝ} {𝓗 : Hypergraph (Fin n)}
    (hlin : 𝓗.IsLinear) (hβ : 0 < β) (hβn : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n) :
    (Nat.card (𝓗.hugeEdges β) : ℝ) ≤ 32 / β ^ 2 := by
  classical
  letI : Fintype 𝓗 := Fintype.ofFinite 𝓗
  let F : Finset 𝓗 := (Finset.univ : Finset 𝓗).filter (fun e : 𝓗 =>
    β * (n : ℝ) / 4 ≤ (edgeSize (e : Set (Fin n)) : ℝ))
  have hF : (F.card : ℝ) ≤ 32 / β ^ 2 := card_huge_le (𝓗 := 𝓗) hlin hβ hβn hn1
  have hle : Nat.card (𝓗.hugeEdges β) ≤ F.card := by
    have h1 : Nat.card (𝓗.hugeEdges β) ≤ Nat.card ↥F := by
      refine Nat.card_le_card_of_injective
        (fun x : 𝓗.hugeEdges β =>
          (⟨⟨(x : Set (Fin n)), x.2.1⟩, ?_⟩ : ↥F)) ?_
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, x.2.2⟩
      · intro a b hab
        exact Subtype.ext (congrArg (fun x : 𝓗 => (x : Set (Fin n))) (Subtype.ext_iff.mp hab))
    have h2 : Nat.card ↥F = F.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    rwa [h2] at h1
  have hle' : ((Nat.card (𝓗.hugeEdges β) : ℕ) : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hle
  linarith [hF]

end

end ErdosFaberLovaszConjecture
