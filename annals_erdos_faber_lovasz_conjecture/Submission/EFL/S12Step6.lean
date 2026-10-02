import Submission.EFL.S12Step5
import Submission.EFL.Nibble
import Submission.EFL.S12Step6Aux
import Submission.EFL.MainThm2
import Submission.Work.EGJ.large_edges_at_vertex

import Submission.EFL.NibbleFixed
/-!
# §12, Step 6 (`step:step6`): the nibble applied to `C_main`

This module formalises **Step 6** of the proof of Theorem 1.1 (the paper's
`step:step6`).

From the regularising lemma (Lemma 11.3) applied to `𝓗`, `R_res` and `β/2` we
obtain a linear multi-hypergraph `𝓗'` with `𝓗'.edges = 𝓗_small ∖ R_res` and
`d_{𝓗'}(w) = (1-ρ)(n-1) ± βn/2`.  Removing the (at most one) matching of
`𝓜_diff` we obtain `𝓗* := 𝓗' ∖ ⋃ 𝓜_diff`, whose degrees are `(1 ± 2β)D`; then
`NibbleStatement` (Lemma `lem:nibble2`) applied with `𝓗_reg`, `𝓗*`, `C_main`,
`R₂`, `S₂`, `r₁`, `ρ_abs`, `2β` and `2γ` yields edge-disjoint matchings
`N_c ⊇ φ⁻¹(c)` for `c ∈ C_main` with

* **(N1)** `N_c ∖ φ⁻¹(c) ⊆ 𝓗* ∪ R₂`;
* **(N2)** `|E_{R₂}(w) ∩ ⋃_c N_c| ≤ 2γD` and `|E_{𝓗*}(w) ∖ ⋃_c N_c| ≤ 2γD`;
* **(N3)** perfect coverage of `U` if `|U| ≤ (1-2ε)n`, nearly-perfect coverage
  with defects in `S₂` otherwise.

Deleting the singleton edges from `N_c` gives the matchings `M_c` of `𝓗`
(the paper's `𝓜_main`), and the conclusions of the step are the paper's MA1,
MA2 (in the starred form used by Steps 7–9), together with the absorber
`R₃ = R₂ ∖ ⋃_c N_c` (equation `(eq:R3abs)`, a `(ρ_abs, 4γ, ξ, ε)`-absorber)
and the defect bound `(eq:boundS3)`
(`|S₂ ∖ ⋃_c (U ∖ V(N_c))| ≥ 4εn` when `|U| > (1-10ε)n`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## The union of a family of matchings indexed by a finset of colours -/

/-- The union of a family of matchings indexed by a set `C` of colours. -/
def famUnionFinset {𝓗 : Hypergraph (Fin n)} (M : Fin n → Set 𝓗) (C : Finset (Fin n)) :
    Hypergraph (Fin n) :=
  {e | ∃ c ∈ C, e ∈ famOf (M c)}

theorem mem_famUnionFinset {𝓗 : Hypergraph (Fin n)} {M : Fin n → Set 𝓗}
    {C : Finset (Fin n)} {e : Set (Fin n)} :
    e ∈ famUnionFinset M C ↔ ∃ c ∈ C, e ∈ famOf (M c) := Iff.rfl

theorem famUnionFinset_mono {𝓗 : Hypergraph (Fin n)} {M M' : Fin n → Set 𝓗}
    {C C' : Finset (Fin n)} (hM : ∀ c, M c ⊆ M' c) (hC : C ⊆ C') :
    famUnionFinset M C ⊆ famUnionFinset M' C' := by
  rintro e ⟨c, hc, he⟩
  exact ⟨c, hC hc, famOf_mono (hM c) he⟩

theorem famUnionFinset_mono_idx {𝓗 : Hypergraph (Fin n)} {M : Fin n → Set 𝓗}
    {C C' : Finset (Fin n)} (hC : C ⊆ C') :
    famUnionFinset M C ⊆ famUnionFinset M C' :=
  famUnionFinset_mono (fun _ => subset_rfl) hC

theorem famUnionFinset_empty {𝓗 : Hypergraph (Fin n)} (M : Fin n → Set 𝓗) :
    famUnionFinset M ∅ = ∅ := by
  ext e
  simp [mem_famUnionFinset]

theorem famUnionFinset_insert {𝓗 : Hypergraph (Fin n)} (M : Fin n → Set 𝓗)
    (c : Fin n) (C : Finset (Fin n)) :
    famUnionFinset M (insert c C) = famOf (M c) ∪ famUnionFinset M C := by
  ext e
  simp only [famUnionFinset, famOf, Finset.mem_insert, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c', hc', e', he', heq⟩
    rcases hc' with rfl | hc'
    · exact Or.inl ⟨e', he', heq⟩
    · exact Or.inr ⟨c', hc', e', he', heq⟩
  · rintro (⟨e', he', heq⟩ | ⟨c', hc', e', he', heq⟩)
    · exact ⟨c, Or.inl rfl, e', he', heq⟩
    · exact ⟨c', Or.inr hc', e', he', heq⟩

theorem famUnionFinset_singleton {𝓗 : Hypergraph (Fin n)} (M : Fin n → Set 𝓗)
    (c : Fin n) : famUnionFinset M {c} = famOf (M c) := by
  rw [show ({c} : Finset (Fin n)) = insert c ∅ from rfl, famUnionFinset_insert,
    famUnionFinset_empty, Set.union_empty]

/-! ## Basics about `MultiHypergraph` order and matchings -/

namespace MultiHypergraph

-- `MultiHypergraph.edgeSet_mono` is *not* declared here: the `Work/Deep/Nibble`
-- chapter (`Submission/Work/Deep/Nibble/Glue.lean`) declares the same result, and the cone now
-- imports it (through `Submission.EFL.NibbleFixed`), so a second declaration would clash.

/-- A matching of a smaller multi-hypergraph is a matching of a larger one. -/
theorem IsMatching.mono {𝓜 𝓝 : MultiHypergraph n} (h : 𝓜 ≤ 𝓝) {N : Set (Set (Fin n))}
    (hN : IsMatching 𝓜 N) : IsMatching 𝓝 N :=
  ⟨hN.1.trans (edgeSet_mono h), hN.2⟩

theorem ofHypergraph_le_regHypergraph (𝓗 : Hypergraph (Fin n)) :
    ofHypergraph 𝓗 ≤ regHypergraph 𝓗 :=
  ⟨subset_rfl, fun _ => Nat.zero_le _⟩

end MultiHypergraph

/-- A family of edges of `𝓗` is a matching of `𝓗_reg`. -/
theorem isMatching_famOf_reg {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗}
    (hM : IsMatching 𝓗 M) :
    MultiHypergraph.IsMatching (MultiHypergraph.regHypergraph 𝓗) (famOf M) :=
  (MultiHypergraph.isMatching_famOf hM).mono (MultiHypergraph.ofHypergraph_le_regHypergraph 𝓗)

/-! ## The bridges `𝓗_reg^{(2)} = 𝓗^{(2)}` -/

theorem VplusTwo_pow2_reg (𝓗 : Hypergraph (Fin n)) (x : ℝ) :
    VplusTwo (MultiHypergraph.pow2 (MultiHypergraph.regHypergraph 𝓗)) x = Vplus 𝓗 x := by
  ext v
  simp only [VplusTwo, Vplus, degAt, MultiHypergraph.pow2, MultiHypergraph.edges_regHypergraph,
    Hypergraph.powFam]

theorem incidentTwo_pow2_reg (𝓗 : Hypergraph (Fin n)) (U : Set (Fin n)) :
    incidentTwo (MultiHypergraph.pow2 (MultiHypergraph.regHypergraph 𝓗)) U = incidentTwo 𝓗 U := by
  ext e
  simp only [incidentTwo, MultiHypergraph.pow2, MultiHypergraph.edges_regHypergraph,
    Hypergraph.powFam]
  constructor <;> intro h
  · exact ⟨h.1.1, h.2⟩
  · exact ⟨⟨h.1, h.1.2⟩, h.2⟩


/-! ## The union of matchings indexed by a set of at most one colour -/

/-- If the family `M` is supported on a set `C` of at most one colour and every
`M c` is a matching, then the union has degree at most one at every vertex. -/
theorem hdeg_famUnionFinset_le_one {𝓗 : Hypergraph (Fin n)} {M : Fin n → Set 𝓗}
    {C : Finset (Fin n)} (hmat : ∀ c, IsMatching 𝓗 (M c)) (hcard : C.card ≤ 1) :
    ∀ w, MultiHypergraph.hdeg (famUnionFinset M C) w ≤ 1 := by
  intro w
  rcases C.eq_empty_or_nonempty with h | ⟨c₀, hc₀⟩
  · have hE : famUnionFinset M C = ∅ := by
      rw [h]
      exact famUnionFinset_empty M
    rw [hE, MultiHypergraph.hdeg]
    simp
  · have hC : C = {c₀} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hc₀, fun b hb => Finset.card_le_one.mp hcard b hb c₀ hc₀⟩
    rw [hC, famUnionFinset_singleton]
    exact MultiHypergraph.hdeg_famOf_le_one (hmat c₀) w

/-! ## Step-6 estimates for the colours of `C_main` -/

/-- Every edge of `φ⁻¹(c)` for `c ∈ C_main` is a *large* edge. -/
theorem IsS12Colours.large_of_mem_cmain {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {r₀ β γ ρ : ℝ}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (h : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    {c : Fin n} (hc : c ∈ Cmain) (e : ↥(medLarge 𝓗 r₁)) (hlab : φ.labels e = c) :
    r₀ < (edgeSize (e : Set (Fin n)) : ℝ) := by
  have hnotin : c ∉ (Cmed ∪ Cdiff) ∪ Chuge := Finset.mem_compl.mp (h.hCmain_sub hc)
  by_contra hle
  rw [not_lt] at hle
  have hmed : edgeMedium r₁ r₀ (e : Set (Fin n)) := ⟨e.2.2, hle⟩
  have hcm := h.hCmed_med e hmed
  rw [hlab] at hcm
  exact hnotin (Finset.mem_union_left Chuge (Finset.mem_union_left Cdiff hcm))

/-- The colour classes of `C_main` cover at most `βn` vertices. -/
theorem IsS12Colours.classVertexCount_le_of_mem_cmain {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {r₀ β γ ρ : ℝ}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (h : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    (hvert : ∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c →
      (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ))
    {c : Fin n} (hc : c ∈ Cmain) : (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ) := by
  have hnotin : c ∉ (Cmed ∪ Cdiff) ∪ Chuge := Finset.mem_compl.mp (h.hCmain_sub hc)
  refine hvert c ?_ ?_
  · intro hcm
    exact hnotin (Finset.mem_union_left Chuge (Finset.mem_union_left Cdiff hcm))
  · intro hass
    have hIn : c ∈ φ.hugeColourSet β := Hypergraph.Coloring.mem_hugeColourSet.mpr hass
    have hmem : c ∈ Chuge ∪ (Cmed ∪ Cdiff) := by
      rw [h.hChuge_eq, Finset.mem_union]
      by_cases hcm : c ∈ Cmed ∪ Cdiff
      · exact Or.inr hcm
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨hIn, hcm⟩)
    rcases Finset.mem_union.mp hmem with h1 | h1
    · exact hnotin (Finset.mem_union_right (Cmed ∪ Cdiff) h1)
    · rcases Finset.mem_union.mp h1 with h2 | h2
      · exact hnotin (Finset.mem_union_left Chuge (Finset.mem_union_left Cdiff h2))
      · exact hnotin (Finset.mem_union_left Chuge (Finset.mem_union_right Cmed h2))

/-- **Step 6, C4 (overlap).**  For an edge `e` of `𝓗` of size at most `r₁`, the
number of colours of `C_main` whose class meets `e` is at most
`r₁n/(r₀-1)` (Claim 12.1 (EP2)). -/
theorem card_cmain_meeting_le {𝓗 : Hypergraph (Fin n)} {r₁ r₀ : ℕ} (hr₀ : 2 ≤ r₀)
    (hn : 0 < n) (hlin : 𝓗.IsLinear) {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)}
    {U : Set (Fin n)} {β γ ρ : ℝ} {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (h : IsS12Colours n 𝓗 (r₁ : ℝ) φ U (r₀ : ℝ) β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff
      Cfinal)
    {e : Set (Fin n)} (he : e ∈ 𝓗) (hsize : edgeSize e ≤ r₁) :
    (({i : Fin Cmain.card |
        (e ∩ famVert (famOf (colourFam φ (colourEnum Cmain i)))).Nonempty} :
        Set (Fin Cmain.card)).ncard : ℝ)
      ≤ (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) := by
  classical
  set S : Set (Fin Cmain.card) :=
    {i | (e ∩ famVert (famOf (colourFam φ (colourEnum Cmain i)))).Nonempty} with hS
  have hchoose : ∀ i ∈ S, ∃ f : ↥(medLarge 𝓗 (r₁ : ℝ)),
      φ.labels f = colourEnum Cmain i ∧ r₀ < (edgeSize (f : Set (Fin n)) : ℝ) ∧
        ((f : Set (Fin n)) ∩ e).Nonempty := by
    intro i hi
    rw [hS] at hi
    simp only [Set.mem_ofPred_eq] at hi
    obtain ⟨v, hve, hvV⟩ := hi
    rw [famVert_famOf, matchVert_colourFam, mem_classVertices] at hvV
    obtain ⟨f, hfc, hvf⟩ := hvV
    exact ⟨f, hfc, IsS12Colours.large_of_mem_cmain h (colourEnum_mem Cmain i) f hfc,
      ⟨v, hvf, hve⟩⟩
  let pick : (i : {i : Fin Cmain.card // i ∈ S}) → ↥(medLarge 𝓗 (r₁ : ℝ)) :=
    fun i => Classical.choose (hchoose i.1 i.2)
  have pick_lab : ∀ i : {i : Fin Cmain.card // i ∈ S},
      φ.labels (pick i) = colourEnum Cmain i.1 :=
    fun i => (Classical.choose_spec (hchoose i.1 i.2)).1
  have pick_large : ∀ i : {i : Fin Cmain.card // i ∈ S},
      r₀ < (edgeSize (pick i : Set (Fin n)) : ℝ) :=
    fun i => (Classical.choose_spec (hchoose i.1 i.2)).2.1
  have pick_largeN : ∀ i : {i : Fin Cmain.card // i ∈ S},
      r₀ < edgeSize (pick i : Set (Fin n)) := fun i => by
    exact_mod_cast pick_large i
  have pick_meet : ∀ i : {i : Fin Cmain.card // i ∈ S},
      (((pick i : Set (Fin n)) ∩ e)).Nonempty :=
    fun i => (Classical.choose_spec (hchoose i.1 i.2)).2.2
  let g : {i : Fin Cmain.card // i ∈ S} →
      {f : 𝓗.largeEdges r₀ // ((f : Set (Fin n)) ∩ e).Nonempty} :=
    fun i => ⟨⟨(pick i : Set (Fin n)),
        (mem_largeEdges 𝓗 r₀ _).mpr ⟨(pick i).2.1, pick_largeN i⟩⟩, pick_meet i⟩
  have hg_inj : Function.Injective g := by
    intro i j hij
    have h1 : ((pick i : Set (Fin n))) = ((pick j : Set (Fin n))) :=
      congrArg (fun x : {f : 𝓗.largeEdges r₀ // ((f : Set (Fin n)) ∩ e).Nonempty} =>
        (x.1 : Set (Fin n))) hij
    have hcol : colourEnum Cmain i.1 = colourEnum Cmain j.1 := by
      rw [← pick_lab i, ← pick_lab j]
      exact congrArg φ.labels (Subtype.ext h1)
    exact Subtype.ext (colourEnum_injective Cmain hcol)
  have hcard := Nat.card_le_card_of_injective g hg_inj
  have hSncard : S.ncard = Nat.card {i : Fin Cmain.card // i ∈ S} := rfl
  have hEP2 := card_largeEdges_meeting_le hlin hr₀ hn he hsize
  rw [hSncard]
  calc ((Nat.card {i : Fin Cmain.card // i ∈ S} : ℕ) : ℝ)
      ≤ (Nat.card {f : 𝓗.largeEdges r₀ // ((f : Set (Fin n)) ∩ e).Nonempty} : ℝ) := by
        exact_mod_cast hcard
    _ ≤ (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) := hEP2


/-! ## The family of colour classes of `C_main` -/

/-- The family of vertex sets of the colour class of the `i`-th colour of
`C_main`: the `M_i` of Step 6. -/
def cmainFam {n : ℕ} {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (Cmain : Finset (Fin n))
    (i : Fin Cmain.card) : Set (Set (Fin n)) :=
  famOf (colourFam φ (colourEnum Cmain i))

theorem cmainFam_lt_edgeSize {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {Cmain : Finset (Fin n)} {i : Fin Cmain.card}
    {e : Set (Fin n)} (he : e ∈ cmainFam φ Cmain i) : r₁ < (edgeSize e : ℝ) := by
  obtain ⟨e', he', rfl⟩ := he
  exact (mem_colourFam.mp he').1.2

/-- **The singleton case of the Nibble Lemma's C4 interaction bound in §12.**

The paper verifies, immediately after applying `lem:nibble2` (efl.tex:2542), the condition
`|{c ∈ C_main : e ∩ V(φ⁻¹(c)) ≠ ∅}| ≤ 2r₁n/r₀ ≤ 2βD` for *every* edge `e ∈ 𝓗*`, where `𝓗*` is
the multi-hypergraph fed as `𝓗'` to the Nibble Lemma and *does* contain singleton copies.
For a proper edge this is `card_cmain_meeting_le` (Claim 12.1 (EP2)) together with §12's numeric
hypothesis `r₁n/(r₀-1) ≤ 2βD`; the singleton `e = {w}` is not covered by (EP2)'s argument (the
large edges through `w` all share the point `w`, so linearity gives no injectivity between them),
and the right bound is instead the elementary `#{large edges through w} ≤ (n-1)/r₀`, i.e.
`Work.EGJ.large_edges_at_vertex`.

Each main colour `c` with `w ∈ V(φ⁻¹(c))` contains a *large* edge through `w`
(`IsS12Colours.large_of_mem_cmain`), and distinct colours give distinct edges (the labels are a
function and `colourEnum` is injective), so the number of main colours at `w` is at most the
number of large edges through `w`; the numeric hypothesis `hnum` (which in §12 follows from
`hEP2num : r₁n/(r₀-1) ≤ 2βD` with `1 ≤ r₁`) converts that into `2β·|C_main|` (note
`|C_main| = Dparam n ρ`, `IsS12Colours.hCmain_card`). -/
theorem card_cmain_vertex_le {𝓗 : Hypergraph (Fin n)} {r₁ r₀ : ℕ} (hr₀ : 2 ≤ r₀)
    (hn : 0 < n) (hlin : 𝓗.IsLinear) {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)}
    {U : Set (Fin n)} {β γ ρ : ℝ} {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (h : IsS12Colours n 𝓗 (r₁ : ℝ) φ U (r₀ : ℝ) β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff
      Cfinal)
    (hnum : (n : ℝ) / ((r₀ : ℝ) - 1) ≤ 2 * β * ((Dparam n ρ : ℕ) : ℝ))
    (w : Fin n) :
    (({i : Fin Cmain.card | w ∈ famVert (cmainFam φ Cmain i)} : Set (Fin Cmain.card)).ncard : ℝ)
      ≤ (2 * β) * ((Cmain.card : ℕ) : ℝ) := by
  classical
  -- The indices of `C_main` whose colour class covers `w`.
  set S : Set (Fin Cmain.card) := {i | w ∈ famVert (cmainFam φ Cmain i)} with hSdef
  -- The large edges of `𝓗` through `w`.
  set E : Set (Set (Fin n)) := {e ∈ 𝓗 | w ∈ e ∧ r₀ < e.ncard} with hEdef
  have hr₀1 : 1 ≤ r₀ := by omega
  -- Every index of `S` admits a large edge through `w` whose colour is the corresponding one.
  have hchoose : ∀ i ∈ S, ∃ f : ↥(medLarge 𝓗 (r₁ : ℝ)),
      φ.labels f = colourEnum Cmain i ∧ w ∈ (f : Set (Fin n)) := by
    intro i hi
    rw [hSdef] at hi
    simp only [Set.mem_ofPred_eq] at hi
    rw [cmainFam, famVert_famOf, matchVert_colourFam, mem_classVertices] at hi
    obtain ⟨f, hfc, hvf⟩ := hi
    exact ⟨f, (mem_colorClass φ (colourEnum Cmain i) f).mp hfc, hvf⟩
  let pick : (i : {i : Fin Cmain.card // i ∈ S}) → ↥(medLarge 𝓗 (r₁ : ℝ)) :=
    fun i => Classical.choose (hchoose i.1 i.2)
  have pick_lab : ∀ i : {i : Fin Cmain.card // i ∈ S},
      φ.labels (pick i) = colourEnum Cmain i.1 :=
    fun i => (Classical.choose_spec (hchoose i.1 i.2)).1
  have pick_w : ∀ i : {i : Fin Cmain.card // i ∈ S}, w ∈ ((pick i : Set (Fin n))) :=
    fun i => (Classical.choose_spec (hchoose i.1 i.2)).2
  have pick_large : ∀ i : {i : Fin Cmain.card // i ∈ S},
      r₀ < edgeSize ((pick i : Set (Fin n))) := fun i => by
    have hlt := IsS12Colours.large_of_mem_cmain h (colourEnum_mem Cmain i.1) (pick i)
      (pick_lab i)
    exact_mod_cast hlt
  -- The injection from `S` into the large edges through `w`.
  let g : {i : Fin Cmain.card // i ∈ S} → ↥E := fun i =>
    ⟨((pick i : Set (Fin n))), by
      rw [hEdef]
      exact Set.mem_sep (pick i).2.1 ⟨pick_w i,
        by rw [← edgeSize_eq_ncard]; exact pick_large i⟩⟩
  have hg_inj : Function.Injective g := by
    intro i j hij
    have h1 : ((pick i : Set (Fin n))) = ((pick j : Set (Fin n))) :=
      congrArg (fun x : ↥E => (x : Set (Fin n))) hij
    have hcol : colourEnum Cmain i.1 = colourEnum Cmain j.1 := by
      rw [← pick_lab i, ← pick_lab j]
      exact congrArg φ.labels (Subtype.ext h1)
    exact Subtype.ext (colourEnum_injective Cmain hcol)
  have hcard : Nat.card {i : Fin Cmain.card // i ∈ S} ≤ Nat.card ↥E :=
    Nat.card_le_card_of_injective g hg_inj
  have hSncard : S.ncard = Nat.card {i : Fin Cmain.card // i ∈ S} := rfl
  have hEncard : Nat.card ↥E = E.ncard := rfl
  -- `Work.EGJ.large_edges_at_vertex`: at most `(n-1)/r₀` large edges pass through `w`.
  have hEGJ0 := Work.EGJ.large_edges_at_vertex (𝓗 : Set (Set (Fin n))) hlin hr₀1 w
  rw [← hEdef] at hEGJ0
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hr₀R1 : (0 : ℝ) < (r₀ : ℝ) := by
    have : (2 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr₀
    linarith
  have hr₀R2 : (0 : ℝ) < (r₀ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr₀
    linarith
  have hEbound : ((E.ncard : ℕ) : ℝ) ≤ (((n : ℝ) - 1) / (r₀ : ℝ)) := by
    rw [le_div_iff₀ hr₀R1]
    exact hEGJ0
  have hdiv : (((n : ℝ) - 1) / (r₀ : ℝ)) ≤ ((n : ℝ) / ((r₀ : ℝ) - 1)) := by
    rw [div_le_div_iff₀ hr₀R1 hr₀R2]
    have hring : ((n : ℝ) - 1) * ((r₀ : ℝ) - 1) =
        (n : ℝ) * (r₀ : ℝ) - (n : ℝ) - (r₀ : ℝ) + 1 := by ring
    rw [hring]
    linarith
  rw [hSncard]
  calc (Nat.card {i : Fin Cmain.card // i ∈ S} : ℝ)
      ≤ (E.ncard : ℝ) := by
        rw [← hEncard]
        exact_mod_cast hcard
    _ ≤ ((n : ℝ) - 1) / (r₀ : ℝ) := hEbound
    _ ≤ (n : ℝ) / ((r₀ : ℝ) - 1) := hdiv
    _ ≤ 2 * β * ((Dparam n ρ : ℕ) : ℝ) := hnum
    _ = 2 * β * ((Cmain.card : ℕ) : ℝ) := by rw [h.hCmain_card]


/-! ## Step 6 -/

/-- **§12, Step 6 (`step:step6`), the output.**  The nibble produces the
matchings `N_c` (starred, in `𝓗_reg`) and `M_c` (the actual matchings of `𝓗`),
together with the properties N1--N3 and MA1--MA2 of the paper and the absorber
`R₃ = R₂ ∖ ⋃_c N_c` and defect set `S₃ = S₂ ∖ ⋃_c (U ∖ V(N_c))`. -/
def S12Step6Result {n : ℕ} (𝓗 : Hypergraph (Fin n)) (r₁ : ℕ)
    (φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)) (U S₂ : Set (Fin n))
    (Cmain Cdiff : Finset (Fin n)) (Mdiff : Fin n → Set 𝓗)
    (R_res R₂ R_abs : Hypergraph (Fin n)) (𝓥 : Set (Set (Fin n)))
    (β γ ρ ρ_abs ξ ε : ℝ) : Prop :=
  ∃ (𝓗' 𝓗star : MultiHypergraph n) (N : Fin Cmain.card → Set (Set (Fin n)))
    (Mmain : Fin n → Set 𝓗),
    (𝓗'.edges = 𝓗.smallEdges r₁ \ R_res) ∧
    (∀ w : Fin n, |((𝓗'.deg w : ℝ)) - (1 - ρ) * ((n : ℝ) - 1)| ≤ 2 / 3 * (β / 2) * (n : ℝ)) ∧
    (𝓗star.edges = 𝓗'.edges \ famUnionFinset Mdiff Cdiff) ∧
    (∀ i, MultiHypergraph.IsMatching (MultiHypergraph.regHypergraph 𝓗) (N i)) ∧
    (∀ i j, i ≠ j → EdgeDisjointFam (N i) (N j)) ∧
    (∀ i, cmainFam φ Cmain i ⊆ N i) ∧
    (∀ i, ∀ e ∈ N i, e ∉ cmainFam φ Cmain i → e ∈ 𝓗star.edgeSet ∪ R₂) ∧
    (∀ w : Fin n, ((({e ∈ R₂ | w ∈ e} : Set (Set (Fin n))) ∩
        (⋃ i : Fin Cmain.card, N i)).ncard : ℝ) ≤ 2 * γ * ((Cmain.card : ℕ) : ℝ)) ∧
    (∀ w : Fin n, ((({e ∈ 𝓗star.edgeSet | w ∈ e} : Set (Set (Fin n))) \
        (⋃ i : Fin Cmain.card, N i)).ncard : ℝ) ≤ 2 * γ * ((Cmain.card : ℕ) : ℝ)) ∧
    (((U.ncard : ℝ) ≤ (1 - 2 * ε) * (n : ℝ)) → ∀ i, U ⊆ famVert (N i)) ∧
    (((1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ)) → NearlyPerfectCoverageFam N U S₂) ∧
    (∀ c ∈ Cmain, colourFam φ c ⊆ Mmain c) ∧
    (∀ c ∉ Cmain, Mmain c = ∅) ∧
    (∀ c, IsMatching 𝓗 (Mmain c)) ∧
    (∀ c ∈ Cmain, ∀ e ∈ Mmain c, e ∉ colourFam φ c →
      (e : Set (Fin n)) ∈ (𝓗.smallEdges r₁ \ (R_res ∪ famUnionFinset Mdiff Cdiff)) ∪ R₂) ∧
    (∀ w : Fin n, (({e ∈ R_abs | w ∈ e} ∩ (⋃ i : Fin Cmain.card, N i)).ncard : ℝ)
      ≤ 2 * γ * ((Cmain.card : ℕ) : ℝ)) ∧
    (∀ w : Fin n, (MultiHypergraph.hdeg (𝓗.smallEdges r₁ \
      (R_res ∪ famUnionFinset Mdiff Cdiff ∪ (⋃ i : Fin Cmain.card, N i))) w : ℝ)
      ≤ 2 * γ * ((Cmain.card : ℕ) : ℝ)) ∧
    IsAbsorber (incidentTwo 𝓗 U) (R₂ \ (⋃ i : Fin Cmain.card, N i)) 𝓥 ρ_abs (4 * γ) ξ ∧
    (∀ c ∈ Cmain, ∀ e ∈ Mmain c, (e : Set (Fin n)) ∈ (⋃ i : Fin Cmain.card, N i)) ∧
    (∀ c ∈ Cmain, ∀ c' ∈ Cmain, c ≠ c' → Disjoint (Mmain c) (Mmain c')) ∧
    (∀ i : Fin Cmain.card, Mmain (colourEnum Cmain i) = toFam (𝓗 := 𝓗) (N i)) ∧
    (((1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ)) →
      4 * ε * (n : ℝ) ≤ (S₂ \ (⋃ i : Fin Cmain.card, (U \ famVert (N i)))).ncard) ∧
    -- NB1, singleton bookkeeping: the singleton edge `{w}` occurs in at most
    -- `n - 3 - d_𝓗(w)` of the matchings `N i`.
    (∀ w : Fin n, (({i : Fin Cmain.card | ({w} : Set (Fin n)) ∈ N i} :
      Set (Fin Cmain.card)).ncard) ≤ n - 3 - MultiHypergraph.hdeg 𝓗 w)


/-! ## Step 6: the theorem -/

theorem s12_step6 {n : ℕ} {𝓗 : Hypergraph (Fin n)} {r₁ r₀ : ℕ} {β γ ρ ρ_abs ξ ε : ℝ}
    (hlin : 𝓗.IsLinear) (hbig : ∀ f ∈ 𝓗, 2 ≤ edgeSize f)
    (hm : DegreeMargins n ρ ξ ε (β / 2) r₁)
    (hn1 : 1 ≤ n) (hnpos : 0 < n) (hr₀ : 2 ≤ r₀)
    (hNib : NibblePointwise r₁ (2 * β) (2 * γ) ε ρ_abs ξ n)
    (hnib : NibbleMarginsStrong n ((Dparam n ρ : ℕ) : ℝ) r₁ (2 * β) (2 * γ) ε ρ_abs ξ)
    {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)} {U S₂ : Set (Fin n)}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (hS12 : IsS12Colours n 𝓗 (r₁ : ℝ) φ U (r₀ : ℝ) β γ ρ Cmed Cdiff Chuge Clarge Cmain
      Cbuff Cfinal)
    (hvert : ∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c →
      (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ))
    {𝓥 : Set (Set (Fin n))} {R_res : Hypergraph (Fin n)}
    (hres : IsReservoirTypeA1 𝓗 R_res 𝓥 ρ ξ ε ∨ IsReservoirTypeA2 𝓗 R_res 𝓥 ρ ξ ε ∨
      (IsReservoirTypeB 𝓗 R_res 𝓥 ρ ξ ε ∧ 2 * ρ * ((n : ℝ) - 1) + 1 ≤ ε * (n : ℝ)))
    (hVuniv : (Set.univ : Set (Fin n)) ∈ 𝓥) (hU𝓥 : U ∈ 𝓥)
    {Mdiff : Fin n → Set 𝓗} (hMdiff_empty : ∀ c ∉ Cdiff, Mdiff c = ∅)
    (hMdiff_mat : ∀ c, IsMatching 𝓗 (Mdiff c))
    {R₂ R_abs : Hypergraph (Fin n)}
    (hR₂abs : IsAbsorber (incidentTwo 𝓗 U) R₂ 𝓥 ρ_abs (2 * γ) ξ)
    (hRabs_sub : R_abs ⊆ R_res)
    (hRabs_pow2 : R_abs ⊆ 𝓗.pow2)
    (hS₂U : S₂ ⊆ U)
    (hR₂sub : R₂ ⊆ R_res)
    (hU : U = Vplus 𝓗 (1 - ε))
    (hS₂big : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      (Dparam n ρ : ℝ) + 4 * ε * (n : ℝ) ≤ (S₂.ncard : ℝ))
    (hγ0 : 0 ≤ γ) (hγε : γ ≤ 2 * ε)
    (hnum1 : 2 / 3 * β * (n : ℝ) + 2 ≤ 2 * β * (Dparam n ρ : ℝ))
    (hnD : (n : ℝ) ≤ 2 * (Dparam n ρ : ℝ))
    (hEP2num : (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) ≤ 2 * β * (Dparam n ρ : ℝ)) :
    S12Step6Result 𝓗 r₁ φ U S₂ Cmain Cdiff Mdiff R_res R₂ R_abs 𝓥 β γ ρ ρ_abs ξ ε := by
  classical
  -- ### 1. The regularised multi-hypergraph `𝓗'`
  obtain ⟨𝓗', h𝓗'edges, h𝓗'le, h𝓗'lin, h𝓗'deg⟩ :=
    regularising_lemma 𝓗 R_res 𝓥 hm hlin hbig hVuniv hres
  -- ### 2. `𝓕 = ⋃ 𝓜_diff`, `𝓕' = 𝓕 ∩ 𝓗'.edges`, `𝓗* = 𝓗' ∖ 𝓕'`
  set 𝓕 : Hypergraph (Fin n) := famUnionFinset Mdiff Cdiff with h𝓕
  set 𝓕' : Hypergraph (Fin n) := {e | e ∈ 𝓕 ∧ e ∈ 𝓗'.edges} with h𝓕'
  have h𝓕'sub : 𝓕' ⊆ 𝓗'.edges := fun _ he => he.2
  have hdeg𝓕 : ∀ w, MultiHypergraph.hdeg 𝓕 w ≤ 1 := by
    rw [h𝓕]
    exact hdeg_famUnionFinset_le_one hMdiff_mat hS12.hCdiff_card
  have h𝓕'sub𝓕 : 𝓕' ⊆ 𝓕 := fun _ he => he.1
  have hdeg𝓕' : ∀ w, MultiHypergraph.hdeg 𝓕' w ≤ 1 := fun w =>
    le_trans (hdeg_mono h𝓕'sub𝓕 w) (hdeg𝓕 w)
  set 𝓗star : MultiHypergraph n := 𝓗'.sdiff 𝓕' with h𝓗star
  have hstar_edges : 𝓗star.edges = 𝓗'.edges \ 𝓕 := by
    rw [h𝓗star, MultiHypergraph.edges_sdiff, h𝓕']
    ext e
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
    tauto
  have hstar_le : 𝓗star ≤ MultiHypergraph.regHypergraph 𝓗 :=
    MultiHypergraph.le_trans (MultiHypergraph.sdiff_le 𝓗' 𝓕') h𝓗'le
  have hstar_lin : 𝓗star.IsLinear :=
    MultiHypergraph.isLinear_mono hstar_le (MultiHypergraph.isLinear_ofHypergraph hbig hlin)
  have hstar_size : ∀ e ∈ 𝓗star.edges, edgeSize e ≤ r₁ := by
    intro e he
    rw [hstar_edges] at he
    rw [h𝓗'edges] at he
    exact ((mem_smallEdges 𝓗 r₁ e).mp he.1.1).2
  have hDbound : |(1 - ρ) * ((n : ℝ) - 1) - (Dparam n ρ : ℝ)| ≤ 1 :=
    Dparam_floor_bound n ρ (le_of_lt hm.hρ0) (by linarith [hm.hρhalf]) hn1
  have hstar_deg : ∀ w, |((𝓗star.deg w : ℝ)) - (Dparam n ρ : ℝ)| ≤
      2 * β * (Dparam n ρ : ℝ) := by
    refine s12_star_degree (𝓗' := 𝓗') (𝓗star := 𝓗star) (𝓕 := 𝓕') h𝓗star h𝓕'sub hdeg𝓕'
      ?_ hDbound hnum1
    intro w
    have h := h𝓗'deg w
    rw [abs_le] at h ⊢
    constructor <;> nlinarith [hm.hβ0, Nat.cast_nonneg (α := ℝ) n]
  -- ### 3. The hypotheses of the Nibble Lemma
  have hU' : U = VplusTwo (MultiHypergraph.pow2 (MultiHypergraph.regHypergraph 𝓗)) (1 - ε) := by
    rw [VplusTwo_pow2_reg, hU]
  have hC1 : ((1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ)) →
      ((Cmain.card : ℕ) : ℝ) + 2 * γ * (n : ℝ) ≤ (S₂.ncard : ℝ) := by
    intro hU2
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hU10 : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) := by nlinarith [hU2, hm.hε0, hn0]
    have h1 := hS₂big hU10
    have h2 : 2 * γ * (n : ℝ) ≤ 4 * ε * (n : ℝ) := by nlinarith [hγε, hn0]
    rw [hS12.hCmain_card]
    linarith
  have hC2 : IsAbsorber (incidentTwo (MultiHypergraph.pow2 (MultiHypergraph.regHypergraph 𝓗)) U)
      R₂ 𝓥 ρ_abs (2 * γ) ξ := by
    rw [incidentTwo_pow2_reg]
    exact hR₂abs
  have hC4a : ∀ i, MultiHypergraph.IsMatching (MultiHypergraph.regHypergraph 𝓗)
      (cmainFam φ Cmain i) :=
    fun i => isMatching_famOf_reg (isMatching_colourFam (colourEnum Cmain i))
  have hC4b : ∀ i, ∀ e ∈ cmainFam φ Cmain i, e ∉ 𝓗star.edgeSet := by
    intro i e he hmem
    have hlt := cmainFam_lt_edgeSize he
    rw [MultiHypergraph.mem_edgeSet] at hmem
    rcases hmem with h1 | ⟨v, hv, -⟩
    · rw [hstar_edges, h𝓗'edges] at h1
      have hs : (edgeSize e : ℝ) ≤ (r₁ : ℝ) := by
        exact_mod_cast ((mem_smallEdges 𝓗 r₁ e).mp h1.1.1).2
      linarith
    · have h1 : (edgeSize e : ℝ) = 1 := by
        rw [hv, edgeSize_eq_ncard, Set.ncard_singleton]; norm_num
      have hr1 : (1 : ℝ) ≤ (r₁ : ℝ) := by
        have := hm.hr1; exact_mod_cast (le_trans (by norm_num : (1:ℕ) ≤ 2) this)
      linarith
  have hC4c : ∀ i, ∀ e ∈ cmainFam φ Cmain i, e ∉ R₂ := by
    intro i e he hmem
    have hlt := cmainFam_lt_edgeSize he
    have hp : (edgeSize e : ℝ) = 2 := by
      have h2 := (mem_pow2.mp (incidentTwo_subset_pow2 𝓗 U (hR₂abs.1 hmem))).2
      rw [h2]; norm_num
    have hr1 : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hm.hr1
    linarith
  have hC4d : ∀ i, ((famVert (cmainFam φ Cmain i)).ncard : ℝ) ≤ (2 * β) * ((Cmain.card : ℕ) : ℝ) := by
    intro i
    have hcv := hS12.classVertexCount_le_of_mem_cmain hvert (colourEnum_mem Cmain i)
    have hfam : famVert (cmainFam φ Cmain i) = φ.classVertices (colourEnum Cmain i) := by
      rw [cmainFam, famVert_famOf, matchVert_colourFam]
    rw [hfam, hS12.hCmain_card]
    exact s12_C4_small hcv hnD (le_of_lt (by linarith [hm.hβ0] : (0:ℝ) < β))
  have hC4e : ∀ e ∈ 𝓗star.edges, (({i : Fin Cmain.card |
      (e ∩ famVert (cmainFam φ Cmain i)).Nonempty} : Set (Fin Cmain.card)).ncard : ℝ) ≤
      (2 * β) * ((Cmain.card : ℕ) : ℝ) := by
    intro e he
    rw [hstar_edges] at he
    rw [h𝓗'edges] at he
    have he𝓗 : e ∈ 𝓗 := he.1.1.1
    have hsize : edgeSize e ≤ r₁ := ((mem_smallEdges 𝓗 r₁ e).mp he.1.1).2
    have hcast : ((Cmain.card : ℕ) : ℝ) = (Dparam n ρ : ℝ) := by rw [hS12.hCmain_card]
    rw [hcast]
    exact le_trans (card_cmain_meeting_le hr₀ hnpos hlin hS12 he𝓗 hsize) hEP2num
  -- ### 4. Apply the Nibble Lemma
  have hstar_deg' : ∀ w : Fin n, |((𝓗star.deg w : ℝ)) - ((Cmain.card : ℕ) : ℝ)| ≤
      2 * β * ((Cmain.card : ℕ) : ℝ) := by
    intro w
    rw [hS12.hCmain_card]
    exact hstar_deg w
  have hnib' : NibbleMarginsStrong n ((Cmain.card : ℕ) : ℝ) r₁ (2 * β) (2 * γ) ε ρ_abs ξ := by
    have hD : ((Cmain.card : ℕ) : ℝ) = ((Dparam n ρ : ℕ) : ℝ) := by
      rw [hS12.hCmain_card]
    rw [hD]
    exact hnib
  have h𝓗'R : ∀ e ∈ 𝓗star.edges, e ∉ R₂ := by
    intro e he hmem
    rw [hstar_edges, h𝓗'edges] at he
    exact he.1.2 (hR₂sub hmem)
  -- ### 4a. The three hypotheses the corrected (faithful) Nibble Lemma needs
  -- the ambient `𝓗_reg` is linear (the paper's `𝓗` is linear and has no singleton edges)
  have hreg_lin : (MultiHypergraph.regHypergraph 𝓗).IsLinear :=
    ⟨fun e he => hbig e he, hlin⟩
  -- the `M i` are pairwise edge-disjoint (the paper's C4)
  have hC4disj : ∀ i j, i ≠ j → EdgeDisjointFam (cmainFam φ Cmain i) (cmainFam φ Cmain j) := by
    intro i j hij
    have hcol : colourEnum Cmain i ≠ colourEnum Cmain j :=
      fun h => hij (colourEnum_injective Cmain h)
    have hd := disjoint_colourFam (φ := φ) hcol
    have hdimg : Disjoint (famOf (colourFam φ (colourEnum Cmain i)))
        (famOf (colourFam φ (colourEnum Cmain j))) := by
      rw [Set.disjoint_left]
      intro e he he'
      obtain ⟨e₁, he₁, h₁⟩ := he
      obtain ⟨e₂, he₂, h₂⟩ := he'
      rw [← h₁] at h₂
      exact (Set.disjoint_left.mp hd) he₁ ((Subtype.ext h₂).symm ▸ he₂)
    rw [EdgeDisjointFam, cmainFam]
    exact Disjoint.mono (fun e he => he.1) (fun e he => he.1) hdimg
  -- `2 ≤ r₁`, hence `n/(r₀-1) ≤ r₁n/(r₀-1) ≤ 2βD`
  have hnum : (n : ℝ) / ((r₀ : ℝ) - 1) ≤ 2 * β * ((Dparam n ρ : ℕ) : ℝ) := by
    have hr₁1 : (1 : ℝ) ≤ (r₁ : ℝ) := by
      have h2 : (2 : ℕ) ≤ r₁ := hm.hr1
      exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 2) h2)
    have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hr₀R2 : (0 : ℝ) < (r₀ : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr₀
      linarith
    calc (n : ℝ) / ((r₀ : ℝ) - 1) ≤ (r₁ : ℝ) * ((n : ℝ) / ((r₀ : ℝ) - 1)) :=
          le_mul_of_one_le_left (div_nonneg hnR (le_of_lt hr₀R2)) hr₁1
      _ = (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) := by ring
      _ ≤ 2 * β * ((Dparam n ρ : ℕ) : ℝ) := hEP2num
  -- the C4 interaction bound, now over the whole edge set of `𝓗*` (singletons included)
  have hC4e' : ∀ e ∈ 𝓗star.edgeSet, (({i : Fin Cmain.card |
      (e ∩ famVert (cmainFam φ Cmain i)).Nonempty} : Set (Fin Cmain.card)).ncard : ℝ) ≤
      (2 * β) * ((Cmain.card : ℕ) : ℝ) := by
    intro e he
    rw [MultiHypergraph.mem_edgeSet] at he
    rcases he with he | ⟨w, rfl, -⟩
    · exact hC4e e he
    · have hset : ({i : Fin Cmain.card |
          (({w} : Set (Fin n)) ∩ famVert (cmainFam φ Cmain i)).Nonempty} :
          Set (Fin Cmain.card)) = {i : Fin Cmain.card | w ∈ famVert (cmainFam φ Cmain i)} := by
        ext i
        simp
      rw [hset]
      exact card_cmain_vertex_le hr₀ hnpos hlin hS12 hnum w
  -- ### 4b. Apply the Nibble Lemma
  have hNibApp := hNib (𝓗 := MultiHypergraph.regHypergraph 𝓗) (𝓗' := 𝓗star) (R := R₂)
      (𝓥 := 𝓥) (U := U) (S := S₂) (D := Cmain.card)
      (M := fun i : Fin Cmain.card => cmainFam φ Cmain i)
  obtain ⟨N, hNsub, hNmat, hNadd, hNdise, hN2a, hN2b, hN3a, hN3b, hNsing⟩ :=
    hNibApp hnib' hU' hS₂U hC1 hU𝓥 hVuniv hC2 hreg_lin hstar_le h𝓗'R hstar_lin hstar_size
      hstar_deg' hC4a hC4disj hC4b hC4c hC4d hC4e'
  -- ### 5. The actual matchings `𝓜_main`
  let Mmain : Fin n → Set 𝓗 := fun c =>
    if h : c ∈ Cmain then toFam (N ((Cmain.orderIsoOfFin rfl).symm ⟨c, h⟩)) else ∅
  have hidx : ∀ (c : Fin n) (hc : c ∈ Cmain),
      colourEnum Cmain ((Cmain.orderIsoOfFin rfl).symm ⟨c, hc⟩) = c :=
    fun c hc => colourEnum_symm hc
  have hMmain_mem : ∀ (c : Fin n) (hc : c ∈ Cmain),
      Mmain c = toFam (N ((Cmain.orderIsoOfFin rfl).symm ⟨c, hc⟩)) := fun c hc => dif_pos hc
  have hMmain_nmem : ∀ c : Fin n, c ∉ Cmain → Mmain c = ∅ := fun c hc => dif_neg hc
  -- `e ∈ famOf (colourFam φ c)` forces `e` to be a large edge of `𝓗`
  have hlarge : ∀ (c : Fin n) (e : Set (Fin n)), e ∈ famOf (colourFam φ c) →
      r₁ < (edgeSize e : ℝ) := by
    rintro c e ⟨e', he', rfl⟩
    exact (mem_colourFam.mp he').1.2
  -- `D ≤ n`
  have hDn : (Dparam n ρ : ℝ) ≤ (n : ℝ) := by
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hρ1 : ρ ≤ 1 := le_trans hm.hρhalf (by norm_num)
    have h0 : (0 : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) := by nlinarith
    calc (Dparam n ρ : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) := by
          rw [Dparam]; exact Nat.floor_le h0
      _ ≤ (n : ℝ) := by nlinarith [hm.hρ0]
  refine ⟨𝓗', 𝓗star, N, Mmain, h𝓗'edges, h𝓗'deg, hstar_edges, hNmat, hNdise, ?_, ?_, hN2a, hN2b,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- N1: `φ⁻¹(c) ⊆ N_c`
    intro i
    rw [cmainFam]
    exact hNsub i
  · -- N1: the added edges lie in `𝓗* ∪ R₂`
    intro i e he hne
    rw [cmainFam] at hne
    exact hNadd i e he hne
  · -- N3: perfect coverage
    intro hUc i
    exact hN3a hUc i
  · -- N3: nearly-perfect coverage
    intro hUc
    exact hN3b hUc
  · -- MA1: `φ⁻¹(c) ⊆ M_c`
    intro c hc e he
    rw [hMmain_mem c hc, mem_toFam]
    refine ⟨?_, ?_⟩
    · have h := hNsub ((Cmain.orderIsoOfFin rfl).symm ⟨c, hc⟩)
      apply h
      have hmem : (e : Set (Fin n)) ∈ famOf (colourFam φ
          (colourEnum Cmain ((Cmain.orderIsoOfFin rfl).symm ⟨c, hc⟩))) := by
        rw [hidx c hc]
        exact ⟨e, he, rfl⟩
      exact hmem
    · have hlt := (mem_colourFam.mp he).1.2
      have hr1 : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hm.hr1
      rw [← edgeSize_eq_ncard]
      have h2 : (2 : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ) := by linarith
      exact_mod_cast le_of_lt h2
  · -- MA1: `M_c = ∅` off `C_main`
    exact hMmain_nmem
  · -- MA1: the `M_c` are matchings
    intro c
    by_cases hc : c ∈ Cmain
    · rw [hMmain_mem c hc]
      exact MultiHypergraph.IsMatching.toFam (hNmat _) (fun _ he => he)
    · rw [hMmain_nmem c hc]
      exact isMatching_empty 𝓗
  · -- MA1: the added edges of `M_c`
    intro c hc e he hne
    rw [hMmain_mem c hc, mem_toFam, nonsing, Set.mem_ofPred_eq] at he
    obtain ⟨hNmem, h2⟩ := he
    have hnotM : (e : Set (Fin n)) ∉ cmainFam φ Cmain
        ((Cmain.orderIsoOfFin rfl).symm ⟨c, hc⟩) := by
      intro hmem
      have hmem' : (e : Set (Fin n)) ∈ famOf (colourFam φ
          (colourEnum Cmain ((Cmain.orderIsoOfFin rfl).symm ⟨c, hc⟩))) := hmem
      rw [hidx c hc] at hmem'
      obtain ⟨e', he', heq⟩ := hmem'
      rw [Subtype.ext heq] at he'
      exact hne he'
    rcases hNadd _ (e : Set (Fin n)) hNmem hnotM with hst | hR₂
    · refine Or.inl ?_
      rw [MultiHypergraph.mem_edgeSet] at hst
      rcases hst with h1 | ⟨v, hv, -⟩
      · rw [hstar_edges, h𝓗'edges] at h1
        exact ⟨h1.1.1, fun hc' => hc'.elim h1.1.2 h1.2⟩
      · have h1 : (e : Set (Fin n)).ncard = 1 := by rw [hv, Set.ncard_singleton]
        omega
    · exact Or.inr hR₂
  · -- MA2 (i) with `R_abs`
    intro w
    have hsub : ({e ∈ R_abs | w ∈ e} : Set (Set (Fin n))) ∩ (⋃ i : Fin Cmain.card, N i) ⊆
        ({e ∈ R₂ | w ∈ e} : Set (Set (Fin n))) ∩ (⋃ i : Fin Cmain.card, N i) := by
      rintro e ⟨⟨hRabs, hw⟩, hUnion⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hUnion
      have hpow : (edgeSize e : ℝ) = 2 := by
        have h2 := (mem_pow2.mp (hRabs_pow2 hRabs)).2
        rw [h2]; norm_num
      have hnotM : e ∉ cmainFam φ Cmain i := by
        intro hmem
        have hbig2 := hlarge (colourEnum Cmain i) e hmem
        have hr1 : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hm.hr1
        linarith
      refine ⟨⟨?_, hw⟩, hUnion⟩
      rcases hNadd i e hi hnotM with hst | hR₂
      · exfalso
        rw [MultiHypergraph.mem_edgeSet] at hst
        rcases hst with h1 | ⟨v, hv, -⟩
        · rw [hstar_edges, h𝓗'edges] at h1
          exact h1.1.2 (hRabs_sub hRabs)
        · have h1 : (edgeSize e : ℝ) = 1 := by
            rw [hv, edgeSize_eq_ncard, Set.ncard_singleton]; norm_num
          linarith
      · exact hR₂
    refine le_trans ?_ (hN2a w)
    exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
  · -- MA2 (ii): the degree of the leftover hypergraph
    intro w
    have hsub : ({e ∈ 𝓗.smallEdges r₁ \
        (R_res ∪ famUnionFinset Mdiff Cdiff ∪ (⋃ i : Fin Cmain.card, N i)) | w ∈ e} :
        Set (Set (Fin n))) ⊆ ({e ∈ 𝓗star.edgeSet | w ∈ e} : Set (Set (Fin n))) \
          (⋃ i : Fin Cmain.card, N i) := by
      rintro e ⟨he, hw⟩
      rw [Set.mem_sdiff] at he
      obtain ⟨hsmall, hnot⟩ := he
      have hnotR : e ∉ R_res := fun h => hnot (Set.mem_union_left _ (Set.mem_union_left _ h))
      have hnotF : e ∉ famUnionFinset Mdiff Cdiff :=
        fun h => hnot (Set.mem_union_left _ (Set.mem_union_right _ h))
      have hnotN : e ∉ (⋃ i : Fin Cmain.card, N i) :=
        fun h => hnot (Set.mem_union_right _ h)
      exact ⟨⟨by
        rw [MultiHypergraph.mem_edgeSet]
        exact Or.inl (by
          rw [hstar_edges, h𝓗'edges]
          exact ⟨⟨hsmall, hnotR⟩, hnotF⟩), hw⟩, hnotN⟩
    refine le_trans ?_ (hN2b w)
    exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
  · -- `R₃ = R₂ ∖ ⋃ N_c` is a `(ρ_abs, 4γ, ξ, ε)`-absorber
    have hdel : ∀ v : Fin n,
        (degAt (R₂ \ (R₂ \ (⋃ i : Fin Cmain.card, N i))) v : ℝ) ≤ (2 * γ) * (n : ℝ) := by
      intro v
      have hEq : R₂ \ (R₂ \ (⋃ i : Fin Cmain.card, N i)) = R₂ ∩ (⋃ i : Fin Cmain.card, N i) := by
        ext e
        simp only [Set.mem_sdiff, Set.mem_inter_iff]
        tauto
      rw [hEq]
      have hinj : Set.InjOn (fun w : Fin n => ({v, w} : Set (Fin n)))
          (nbrs (R₂ ∩ (⋃ i : Fin Cmain.card, N i)) v) := by
        intro a _ b _ hab
        rcases Set.pair_eq_pair_iff.mp hab with ⟨-, h⟩ | ⟨h1, h2⟩
        · exact h
        · exact h2.trans h1
      have himg : ((fun w : Fin n => ({v, w} : Set (Fin n))) ''
          nbrs (R₂ ∩ (⋃ i : Fin Cmain.card, N i)) v) ⊆
          ({e ∈ R₂ | v ∈ e} : Set (Set (Fin n))) ∩ (⋃ i : Fin Cmain.card, N i) := by
        rintro e ⟨w, hw, rfl⟩
        exact ⟨⟨hw.1, by simp⟩, hw.2⟩
      have h1 : degAt (R₂ ∩ (⋃ i : Fin Cmain.card, N i)) v ≤
          ((({e ∈ R₂ | v ∈ e} : Set (Set (Fin n))) ∩
            (⋃ i : Fin Cmain.card, N i)).ncard) := by
        show (nbrs (R₂ ∩ (⋃ i : Fin Cmain.card, N i)) v).ncard ≤ _
        rw [← (Set.ncard_image_iff (f := fun w : Fin n => ({v, w} : Set (Fin n)))
          (s := nbrs (R₂ ∩ (⋃ i : Fin Cmain.card, N i)) v)).mpr hinj]
        exact Set.ncard_le_ncard himg (Set.toFinite _)
      have h2 := hN2a v
      have h4 : ((Cmain.card : ℕ) : ℝ) = (Dparam n ρ : ℝ) := by rw [hS12.hCmain_card]
      have h3 : (2 * γ) * (Dparam n ρ : ℝ) ≤ (2 * γ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hDn (by linarith [hγ0])
      have h1' : (degAt (R₂ ∩ (⋃ i : Fin Cmain.card, N i)) v : ℝ) ≤
          (2 * γ) * ((Cmain.card : ℕ) : ℝ) := by
        refine le_trans ?_ h2
        exact_mod_cast h1
      rw [h4] at h1'
      linarith
    have hres' : IsAbsorber (incidentTwo 𝓗 U) (R₂ \ (⋃ i : Fin Cmain.card, N i)) 𝓥 ρ_abs
        (2 * γ + 2 * γ) ξ :=
      IsAbsorber.delete hR₂abs Set.sdiff_subset hdel
    have hring : (2 * γ + 2 * γ : ℝ) = 4 * γ := by ring
    rwa [hring] at hres'
  · -- the edges of `𝓜_main` lie in `⋃ N`
    intro c hc e he
    rw [hMmain_mem c hc] at he
    rw [mem_toFam, nonsing, Set.mem_ofPred_eq] at he
    exact Set.mem_iUnion.mpr ⟨(Cmain.orderIsoOfFin rfl).symm ⟨c, hc⟩, he.1⟩
  · -- distinct matchings of `𝓜_main` are edge-disjoint
    intro c hc c' hc' hne
    rw [hMmain_mem c hc, hMmain_mem c' hc', Set.disjoint_left]
    intro e he he'
    have hij : (Cmain.orderIsoOfFin rfl).symm ⟨c, hc⟩ ≠
        (Cmain.orderIsoOfFin rfl).symm ⟨c', hc'⟩ := by
      intro h
      exact hne (by
        have := congrArg (fun x : Fin Cmain.card => colourEnum Cmain x) h
        rwa [hidx c hc, hidx c' hc'] at this)
    rw [mem_toFam, nonsing, Set.mem_ofPred_eq] at he he'
    exact Set.disjoint_left.mp (hNdise _ _ hij) he he'
  · -- the defining equation of `𝓜_main`
    intro i
    have hs : (Cmain.orderIsoOfFin rfl).symm ⟨colourEnum Cmain i, colourEnum_mem Cmain i⟩ = i := by
      rw [show (⟨colourEnum Cmain i, colourEnum_mem Cmain i⟩ : ↥Cmain) =
        Cmain.orderIsoOfFin rfl i from Subtype.ext rfl]
      exact OrderIso.symm_apply_apply _ i
    rw [hMmain_mem (colourEnum Cmain i) (colourEnum_mem Cmain i), hs]
  · -- `S₃ = S₂ ∖ ⋃_c (U ∖ V(N_c))` still has `4εn` vertices
    intro hUbig
    by_cases hU2 : (1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ)
    · have hnp := hN3b hU2
      have hone : ∀ i, (U \ famVert (N i)).ncard ≤ 1 := fun i => hnp.2.2 i
      have hXle : ((⋃ i : Fin Cmain.card, (U \ famVert (N i))).ncard : ℝ) ≤
          (Dparam n ρ : ℝ) := by
        have h1 : (⋃ i : Fin Cmain.card, (U \ famVert (N i))).ncard ≤
            ∑ i : Fin Cmain.card, (U \ famVert (N i)).ncard :=
          Set.ncard_iUnion_le_of_fintype _
        have h2 : ∑ i : Fin Cmain.card, (U \ famVert (N i)).ncard ≤ Cmain.card :=
          (Finset.sum_le_sum (fun i _ => hone i)).trans (by simp)
        have h3 : ((Cmain.card : ℕ) : ℝ) = (Dparam n ρ : ℝ) := by
          rw [hS12.hCmain_card]
        have h4 : ((∑ i : Fin Cmain.card, (U \ famVert (N i)).ncard : ℕ) : ℝ) ≤
            (Cmain.card : ℝ) := by exact_mod_cast h2
        calc ((⋃ i : Fin Cmain.card, (U \ famVert (N i))).ncard : ℝ)
            ≤ ((∑ i : Fin Cmain.card, (U \ famVert (N i)).ncard : ℕ) : ℝ) := by
              exact_mod_cast h1
          _ ≤ (Cmain.card : ℝ) := h4
          _ = (Dparam n ρ : ℝ) := h3
      have hS2 := hS₂big hUbig
      have hge := ncard_sdiff_ge S₂ (⋃ i : Fin Cmain.card, (U \ famVert (N i)))
      linarith
    · rw [not_lt] at hU2
      have hperf := hN3a hU2
      have hX : (⋃ i : Fin Cmain.card, (U \ famVert (N i))) = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨x, hx⟩
        rw [Set.mem_iUnion] at hx
        obtain ⟨i, hi⟩ := hx
        exact hi.2 (hperf i hi.1)
      rw [hX, Set.sdiff_empty]
      have hS2 := hS₂big hUbig
      linarith
  · -- the singleton bookkeeping of the matchings `N_i`
    intro w
    have h1 : (({i : Fin Cmain.card | ({w} : Set (Fin n)) ∈ N i ∧
        ({w} : Set (Fin n)) ∉ cmainFam φ Cmain i} : Set (Fin Cmain.card)).ncard) ≤
        𝓗star.singles w := hNsing w
    have h2 : ({i : Fin Cmain.card | ({w} : Set (Fin n)) ∈ N i ∧
        ({w} : Set (Fin n)) ∉ cmainFam φ Cmain i} : Set (Fin Cmain.card)) =
        ({i : Fin Cmain.card | ({w} : Set (Fin n)) ∈ N i} : Set (Fin Cmain.card)) := by
      ext i
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h
        exact h.1
      · intro h
        refine ⟨h, ?_⟩
        intro hmem
        have hlt := cmainFam_lt_edgeSize hmem
        have hsz : edgeSize ({w} : Set (Fin n)) = 1 := by
          rw [edgeSize_eq_ncard, Set.ncard_singleton]
        rw [hsz] at hlt
        have hr1 : (1 : ℝ) ≤ (r₁ : ℝ) := by
          exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hm.hr1)
        simp only [Nat.cast_one] at hlt
        exact absurd hlt (not_lt.mpr hr1)
    rw [h2] at h1
    exact le_trans h1 (hstar_le.2 w)

end

end ErdosFaberLovaszConjecture
