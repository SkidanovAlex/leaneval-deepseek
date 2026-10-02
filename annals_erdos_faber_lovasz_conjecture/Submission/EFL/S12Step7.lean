import Submission.EFL.S12Step6
import Submission.EFL.Nibble
import Submission.EFL.LeftoverLemma

/-!
# §12, Step 7 (`step:step7`): the leftover colouring of `C_buff`

This module formalises **Step 7** of the proof of Theorem 1.1.

From Step 6 we have the leftover hypergraph

`𝓗_rem = 𝓗_small ∖ (R_res ∪ ⋃𝓜_diff ∪ ⋃_c M_c)`

and the absorber `R₃ = R₂ ∖ ⋃_c N_c`.  Applying the Leftover Lemma
(`LeftoverStatement`, Lemma `lem:leftover`) with the colour set `C_buff`
(playing the role of `C`) gives a family `𝓜_buff = {M_c : c ∈ C_buff}` of
pairwise edge-disjoint matchings with

* **(B1)** `M_c ⊇ φ⁻¹(c)`, `𝓗_rem ⊆ ⋃_c (M_c ∖ φ⁻¹(c)) ⊆ 𝓗_rem ∪ R₃`;
* **(B2)** perfect coverage of `U` if `|U| ≤ (1-10ε)n`, and nearly-perfect
  coverage with defects in `S₃` otherwise.

The hypotheses L1--L5 of the Leftover Lemma are verified here from the
estimates of Steps 5/6 and Claim 12.1 (EP2).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Monotonicity of absorbers in `𝓥` -/

theorem Typical.mono_set {G' R : Hypergraph (Fin n)} {𝓥 𝓥' : Set (Set (Fin n))} {ρ γ : ℝ}
    (h : 𝓥' ⊆ 𝓥) (ht : Typical G' R ρ γ 𝓥) : Typical G' R ρ γ 𝓥' :=
  fun X hX v => ht X (h hX) v

theorem IsAbsorber.mono_set {G' R : Hypergraph (Fin n)} {𝓥 𝓥' : Set (Set (Fin n))}
    {ρ γ ξ : ℝ} (h : 𝓥' ⊆ 𝓥) (habs : IsAbsorber G' R 𝓥 ρ γ ξ) :
    IsAbsorber G' R 𝓥' ρ γ ξ :=
  ⟨habs.1, Typical.mono_set h habs.2.1, habs.2.2⟩

/-! ## The degree of a vertex is at most the number of edges through it -/

theorem degAt_le_hdeg (R : Hypergraph (Fin n)) (v : Fin n) :
    degAt R v ≤ MultiHypergraph.hdeg R v := by
  have hinj : Set.InjOn (fun w : Fin n => ({v, w} : Set (Fin n))) (nbrs R v) := by
    intro a _ b _ hab
    rcases Set.pair_eq_pair_iff.mp hab with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1
  have himg : (fun w : Fin n => ({v, w} : Set (Fin n))) '' (nbrs R v) ⊆ {e ∈ R | v ∈ e} := by
    rintro e ⟨w, hw, rfl⟩
    exact ⟨hw, by simp⟩
  show (nbrs R v).ncard ≤ MultiHypergraph.hdeg R v
  rw [← (Set.ncard_image_iff (f := fun w : Fin n => ({v, w} : Set (Fin n)))
    (s := nbrs R v)).mpr hinj]
  exact Set.ncard_le_ncard himg (Set.toFinite _)

/-! ## Families of edges: basic glue -/

theorem disjoint_famOf {𝓗 : Hypergraph (Fin n)} {M M' : Set 𝓗} (h : Disjoint M M') :
    Disjoint (famOf M) (famOf M') := by
  rw [Set.disjoint_left] at h ⊢
  rintro e ⟨e₁, he₁, rfl⟩ ⟨e₂, he₂, heq⟩
  exact h he₁ (Subtype.ext heq.symm ▸ he₂)

theorem famVert_famOf_colourFam {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} (c : Fin n) :
    famVert (famOf (colourFam φ c)) = φ.classVertices c := by
  rw [famVert_famOf, matchVert_colourFam]

theorem famOf_toFam {𝓗 : Hypergraph (Fin n)} (G : Set (Set (Fin n))) :
    famOf (toFam (𝓗 := 𝓗) G) = {e : Set (Fin n) | e ∈ 𝓗 ∧ e ∈ nonsing G} := by
  ext e
  constructor
  · rintro ⟨e', he', rfl⟩
    exact ⟨e'.2, he'⟩
  · rintro ⟨he𝓗, he⟩
    exact ⟨⟨e, he𝓗⟩, he, rfl⟩

/-! ## Claim 12.1 (EP2) for an arbitrary colour set of large edges -/

/-- **Claim 12.1 (EP2)** for a colour set `C` all of whose classes consist of
large edges: a small edge meets at most `r₁n/(r₀-1)` of the colour classes. -/
theorem card_colours_meeting_le {𝓗 : Hypergraph (Fin n)} {r₁ r₀ : ℕ} (hr₀ : 2 ≤ r₀)
    (hn : 0 < n) (hlin : 𝓗.IsLinear) {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)}
    {C : Finset (Fin n)}
    (hlarge : ∀ c ∈ C, ∀ e : ↥(medLarge 𝓗 (r₁ : ℝ)), φ.labels e = c →
      r₀ < edgeSize (e : Set (Fin n)))
    {e : Set (Fin n)} (he : e ∈ 𝓗) (hsize : edgeSize e ≤ r₁) :
    (({i : Fin C.card |
        (e ∩ famVert (famOf (colourFam φ (colourEnum C i)))).Nonempty} :
        Set (Fin C.card)).ncard : ℝ)
      ≤ (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) := by
  classical
  set S : Set (Fin C.card) :=
    {i | (e ∩ famVert (famOf (colourFam φ (colourEnum C i)))).Nonempty} with hS
  have hchoose : ∀ i ∈ S, ∃ f : ↥(medLarge 𝓗 (r₁ : ℝ)),
      φ.labels f = colourEnum C i ∧ r₀ < (edgeSize (f : Set (Fin n)) : ℝ) ∧
        ((f : Set (Fin n)) ∩ e).Nonempty := by
    intro i hi
    rw [hS] at hi
    simp only [Set.mem_ofPred_eq] at hi
    obtain ⟨v, hve, hvV⟩ := hi
    rw [famVert_famOf, matchVert_colourFam, mem_classVertices] at hvV
    obtain ⟨f, hfc, hvf⟩ := hvV
    have hl := hlarge (colourEnum C i) (colourEnum_mem C i) f hfc
    exact ⟨f, hfc, by exact_mod_cast hl, ⟨v, hvf, hve⟩⟩
  let pick : (i : {i : Fin C.card // i ∈ S}) → ↥(medLarge 𝓗 (r₁ : ℝ)) :=
    fun i => Classical.choose (hchoose i.1 i.2)
  have pick_lab : ∀ i : {i : Fin C.card // i ∈ S},
      φ.labels (pick i) = colourEnum C i.1 :=
    fun i => (Classical.choose_spec (hchoose i.1 i.2)).1
  have pick_large : ∀ i : {i : Fin C.card // i ∈ S},
      r₀ < (edgeSize (pick i : Set (Fin n)) : ℝ) :=
    fun i => (Classical.choose_spec (hchoose i.1 i.2)).2.1
  have pick_largeN : ∀ i : {i : Fin C.card // i ∈ S},
      r₀ < edgeSize (pick i : Set (Fin n)) := fun i => by exact_mod_cast pick_large i
  have pick_meet : ∀ i : {i : Fin C.card // i ∈ S},
      (((pick i : Set (Fin n)) ∩ e)).Nonempty :=
    fun i => (Classical.choose_spec (hchoose i.1 i.2)).2.2
  let g : {i : Fin C.card // i ∈ S} →
      {f : 𝓗.largeEdges r₀ // ((f : Set (Fin n)) ∩ e).Nonempty} :=
    fun i => ⟨⟨(pick i : Set (Fin n)),
      (mem_largeEdges 𝓗 r₀ _).mpr ⟨(pick i).2.1, pick_largeN i⟩⟩, pick_meet i⟩
  have hg_inj : Function.Injective g := by
    intro i j hij
    have h1 : ((pick i : Set (Fin n))) = ((pick j : Set (Fin n))) :=
      congrArg (fun x : {f : 𝓗.largeEdges r₀ // ((f : Set (Fin n)) ∩ e).Nonempty} =>
        (x.1 : Set (Fin n))) hij
    have hcol : colourEnum C i.1 = colourEnum C j.1 := by
      rw [← pick_lab i, ← pick_lab j]
      exact congrArg φ.labels (Subtype.ext h1)
    exact Subtype.ext (colourEnum_injective C hcol)
  have hcard := Nat.card_le_card_of_injective g hg_inj
  have hSncard : S.ncard = Nat.card {i : Fin C.card // i ∈ S} := rfl
  have hEP2 := card_largeEdges_meeting_le hlin hr₀ hn he hsize
  rw [hSncard]
  calc ((Nat.card {i : Fin C.card // i ∈ S} : ℕ) : ℝ)
      ≤ (Nat.card {f : 𝓗.largeEdges r₀ // ((f : Set (Fin n)) ∩ e).Nonempty} : ℝ) := by
        exact_mod_cast hcard
    _ ≤ (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) := hEP2


/-! ## The bridges `ofHypergraph 𝓗` -/

theorem VplusTwo_pow2_ofHypergraph (𝓗 : Hypergraph (Fin n)) (x : ℝ) :
    VplusTwo (MultiHypergraph.pow2 (MultiHypergraph.ofHypergraph 𝓗)) x = Vplus 𝓗 x := by
  ext v
  simp only [VplusTwo, Vplus, degAt, MultiHypergraph.pow2, MultiHypergraph.edges_ofHypergraph,
    Hypergraph.powFam]

theorem incidentTwo_pow2_ofHypergraph (𝓗 : Hypergraph (Fin n)) (U : Set (Fin n)) :
    incidentTwo (MultiHypergraph.pow2 (MultiHypergraph.ofHypergraph 𝓗)) U =
      incidentTwo 𝓗 U := by
  ext e
  simp only [incidentTwo, MultiHypergraph.pow2, MultiHypergraph.edges_ofHypergraph,
    Hypergraph.powFam]
  constructor <;> intro h
  · exact ⟨h.1.1, h.2⟩
  · exact ⟨⟨h.1, h.1.2⟩, h.2⟩

/-- Step 7: the output of the leftover colouring. -/
def S12Step7Result {n : ℕ} (𝓗 : Hypergraph (Fin n)) (r₁ : ℕ)
    (φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)) (U : Set (Fin n)) (S₃ : Set (Fin n))
    (Cbuff : Finset (Fin n)) (R₃ 𝓗rem : Hypergraph (Fin n)) (ε : ℝ) : Prop :=
  ∃ Mbuff : Fin n → Set 𝓗,
    (∀ c ∉ Cbuff, Mbuff c = ∅) ∧
    (∀ c ∈ Cbuff, colourFam φ c ⊆ Mbuff c) ∧
    (∀ c, IsMatching 𝓗 (Mbuff c)) ∧
    (∀ c ∈ Cbuff, ∀ e ∈ Mbuff c, e ∉ colourFam φ c →
      (e : Set (Fin n)) ∈ 𝓗rem ∪ R₃) ∧
    (∀ e ∈ 𝓗rem, ∃ c ∈ Cbuff, e ∈ famOf (Mbuff c)) ∧
    (∀ c c' : Fin n, c ≠ c' → Disjoint (famOf (Mbuff c)) (famOf (Mbuff c'))) ∧
    (((U.ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ)) → ∀ c ∈ Cbuff, Covers (Mbuff c) U) ∧
    (((1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ)) →
      (∀ c ∈ Cbuff, (U \ matchVert (Mbuff c)).ncard ≤ 1) ∧
      (∀ c ∈ Cbuff, U \ matchVert (Mbuff c) ⊆ S₃)) ∧
    (∀ u ∈ U, (({c : Fin n | c ∈ Cbuff ∧ u ∉ matchVert (Mbuff c)} :
      Set (Fin n)).ncard) ≤ 1)


/-! ## Step 7: the theorem -/

theorem s12_step7 {n : ℕ} {𝓗 : Hypergraph (Fin n)} {r₁ r₀ : ℕ} {β γ ρ ρ_abs ξ ε : ℝ}
    {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)} {U S₃ : Set (Fin n)}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (hS12 : IsS12Colours n 𝓗 (r₁ : ℝ) φ U (r₀ : ℝ) β γ ρ Cmed Cdiff Chuge Clarge Cmain
      Cbuff Cfinal)
    (hvert : ∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c →
      (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ))
    (hlin : 𝓗.IsLinear) (hbig : ∀ f ∈ 𝓗, 2 ≤ edgeSize f)
    (hleft : LeftoverMargins n r₁ γ ρ ρ_abs ε ξ) (hnpos : 0 < n) (hr₀ : 2 ≤ r₀)
    (hr₁r₀ : r₁ < r₀)
    {Mdiff : Fin n → Set 𝓗} {R_res R₂ R₃ : Hypergraph (Fin n)} {𝓥 : Set (Set (Fin n))}
    {Ncm : Fin Cmain.card → Set (Set (Fin n))}
    (hR₃eq : R₃ = R₂ \ (⋃ i : Fin Cmain.card, Ncm i))
    (hR₃abs : IsAbsorber (incidentTwo 𝓗 U) R₃ 𝓥 ρ_abs (4 * γ) ξ)
    (hR₃pow : R₃ ⊆ 𝓗.pow2) (hR₂sub : R₂ ⊆ R_res)
    (hS₃sub : S₃ ⊆ U)
    (hU : U = Vplus 𝓗 (1 - ε)) (hU𝓥 : U ∈ 𝓥) (hVuniv : (Set.univ : Set (Fin n)) ∈ 𝓥)
    (hremDeg : ∀ w : Fin n, (MultiHypergraph.hdeg (𝓗.smallEdges r₁ \
      (R_res ∪ famUnionFinset Mdiff Cdiff ∪ (⋃ i : Fin Cmain.card, Ncm i))) w : ℝ) ≤
        2 * γ * ((Cmain.card : ℕ) : ℝ))
    (hγ0 : 0 ≤ γ)
    (hS₃big : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) → 4 * ε * (n : ℝ) ≤ (S₃.ncard : ℝ))
    (hL1 : (10 * Real.sqrt γ) * ((Cmain.card : ℕ) : ℝ) / 2 ≤ (Cbuff.card : ℝ))
    (hβγ : β ≤ 5 * Real.sqrt γ)
    (hL3 : 4 * γ ≤ 100 * Real.sqrt γ)
    (hL4ov : (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) ≤ γ * ((Cmain.card : ℕ) : ℝ))
    (hL5 : 10 * Real.sqrt γ < 3 * ε) :
    S12Step7Result 𝓗 r₁ φ U S₃ Cbuff R₃
      (𝓗.smallEdges r₁ \ (R_res ∪ famUnionFinset Mdiff Cdiff ∪
        (⋃ i : Fin Cmain.card, Ncm i))) ε := by
  classical
  set 𝓗rem : Hypergraph (Fin n) :=
    𝓗.smallEdges r₁ \ (R_res ∪ famUnionFinset Mdiff Cdiff ∪ (⋃ i : Fin Cmain.card, Ncm i))
    with h𝓗rem
  set M : Fin Cbuff.card → Set (Set (Fin n)) :=
    fun i => famOf (colourFam φ (colourEnum Cbuff i)) with hM
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt γ := Real.sqrt_nonneg γ
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  -- ### The `M_i` are matchings of `𝓗` of small vertex sets
  have hMmat : ∀ i, MultiHypergraph.IsMatching (MultiHypergraph.ofHypergraph 𝓗) (M i) :=
    fun i => MultiHypergraph.isMatching_famOf (isMatching_colourFam _)
  have hMdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j) := by
    intro i j hij
    exact disjoint_famOf (disjoint_colourFam (fun h => hij (colourEnum_injective Cbuff h)))
  have hMsize : ∀ i, ((famVert (M i)).ncard : ℝ) ≤ (10 * Real.sqrt γ) * (n : ℝ) / 2 := by
    intro i
    have hcv := hS12.classVertexCount_le_of_buff_union_final hvert (colourEnum Cbuff i)
      (Finset.mem_union_left Cfinal (colourEnum_mem Cbuff i))
    rw [Hypergraph.Coloring.classVertexCount] at hcv
    have hfam : famVert (M i) = φ.classVertices (colourEnum Cbuff i) := by
      rw [hM]
      exact famVert_famOf_colourFam _
    rw [hfam]
    have h5 : β * (n : ℝ) ≤ (10 * Real.sqrt γ) * (n : ℝ) / 2 := by nlinarith
    linarith
  -- ### properties of `𝓗_rem`
  have hremEdges : 𝓗rem ⊆ (MultiHypergraph.ofHypergraph 𝓗).edges := by
    intro e he
    rw [h𝓗rem] at he
    exact ((mem_smallEdges 𝓗 r₁ e).mp ((Set.mem_sdiff e).mp he).1).1
  have hremR : ∀ e ∈ 𝓗rem, e ∉ R₃ := by
    intro e he hR
    rw [h𝓗rem] at he
    have h1 : e ∈ R₂ \ (⋃ i : Fin Cmain.card, Ncm i) := by rwa [← hR₃eq]
    exact ((Set.mem_sdiff e).mp he).2
      (Set.mem_union_left _ (Set.mem_union_left _ (hR₂sub ((Set.mem_sdiff e).mp h1).1)))
  have hremM : ∀ e ∈ 𝓗rem, ∀ i, e ∉ M i := by
    intro e he i hMi
    rw [h𝓗rem] at he
    have hsmall : edgeSize e ≤ r₁ :=
      ((mem_smallEdges 𝓗 r₁ e).mp ((Set.mem_sdiff e).mp he).1).2
    rw [hM] at hMi
    obtain ⟨e', he', heq⟩ := hMi
    obtain ⟨hmed, hcl⟩ := mem_colourFam.mp he'
    have hlarge := (IsS12Colours.large_nonhuge_of_buff_union_final hS12
      (Finset.mem_union_left Cfinal (colourEnum_mem Cbuff i))
      (⟨(e' : Set (Fin n)), hmed⟩ : ↥(medLarge 𝓗 (r₁ : ℝ))) hcl).1
    have : r₀ < edgeSize e := by
      rw [← heq]
      exact_mod_cast hlarge
    omega
  have hremDegAt : ∀ v : Fin n, (MultiHypergraph.hdeg 𝓗rem v : ℝ) ≤
      (10 * Real.sqrt γ) ^ 2 * ((Cmain.card : ℕ) : ℝ) / 20 := by
    intro v
    have h1 : (MultiHypergraph.hdeg 𝓗rem v : ℝ) ≤ 2 * γ * ((Cmain.card : ℕ) : ℝ) := by
      rw [h𝓗rem]; exact hremDeg v
    have h2 : 2 * γ ≤ (10 * Real.sqrt γ) ^ 2 / 20 := by
      have := Real.sq_sqrt hγ0
      nlinarith
    have h3 : (0 : ℝ) ≤ ((Cmain.card : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hremSize : ∀ e ∈ 𝓗rem, edgeSize e ≤ r₁ := by
    intro e he
    rw [h𝓗rem] at he
    exact ((mem_smallEdges 𝓗 r₁ e).mp ((Set.mem_sdiff e).mp he).1).2
  have hremOv : ∀ e ∈ 𝓗rem, (({i : Fin Cbuff.card |
      (e ∩ famVert (M i)).Nonempty}).ncard : ℝ) ≤
      (10 * Real.sqrt γ) ^ 2 * ((Cmain.card : ℕ) : ℝ) / 100 := by
    intro e he
    rw [h𝓗rem] at he
    obtain ⟨hsmall, -⟩ := (Set.mem_sdiff e).mp he
    have he𝓗 : e ∈ 𝓗 := ((mem_smallEdges 𝓗 r₁ e).mp hsmall).1
    have hsize : edgeSize e ≤ r₁ := ((mem_smallEdges 𝓗 r₁ e).mp hsmall).2
    have hlarge : ∀ c ∈ Cbuff, ∀ f : ↥(medLarge 𝓗 (r₁ : ℝ)), φ.labels f = c →
        r₀ < edgeSize (f : Set (Fin n)) := by
      intro c hc f hlab
      exact_mod_cast (IsS12Colours.large_nonhuge_of_buff_union_final hS12
        (Finset.mem_union_left Cfinal hc) f hlab).1
    have h1 := card_colours_meeting_le hr₀ hnpos hlin hlarge he𝓗 hsize
    have h2 : (10 * Real.sqrt γ) ^ 2 / 100 = γ := by
      have hsq := Real.sq_sqrt hγ0
      nlinarith
    calc (({i : Fin Cbuff.card | (e ∩ famVert (M i)).Nonempty}).ncard : ℝ)
        ≤ (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) := h1
      _ ≤ γ * ((Cmain.card : ℕ) : ℝ) := hL4ov
      _ = (10 * Real.sqrt γ) ^ 2 * ((Cmain.card : ℕ) : ℝ) / 100 := by
          have hsq := Real.sq_sqrt hγ0
          nlinarith [hsq, Nat.cast_nonneg (α := ℝ) Cmain.card]
  -- ### L1 (upper bound) and L3, L5
  have hL1' : ((Cbuff.card : ℕ) : ℝ) ≤ (10 * Real.sqrt γ) * ((Cmain.card : ℕ) : ℝ) := by
    have h2 : Dparam n ρ = Cmain.card := hS12.hCmain_card.symm
    rw [hS12.hCbuff_card, h2, D'param]
    exact Nat.floor_le (by positivity)
  have h𝓥sub : ({(Set.univ : Set (Fin n)), U} : Set (Set (Fin n))) ⊆ 𝓥 := by
    intro X hX
    rcases Set.mem_insert_iff.mp hX with rfl | hX
    · exact hVuniv
    · rw [Set.mem_singleton_iff] at hX
      exact hX ▸ hU𝓥
  have hL3' : IsAbsorber (incidentTwo (MultiHypergraph.pow2 (MultiHypergraph.ofHypergraph 𝓗)) U)
      R₃ ({(Set.univ : Set (Fin n)), U} : Set (Set (Fin n))) ρ_abs
      (10 * (10 * Real.sqrt γ)) ξ := by
    rw [incidentTwo_pow2_ofHypergraph]
    exact IsAbsorber.mono_gamma (IsAbsorber.mono_set h𝓥sub hR₃abs) (by linarith [hL3])
  have hU' : U = VplusTwo (MultiHypergraph.pow2 (MultiHypergraph.ofHypergraph 𝓗)) (1 - ε) := by
    rw [VplusTwo_pow2_ofHypergraph, hU]
  have hL5' : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      (10 * Real.sqrt γ + ε) * (n : ℝ) < (S₃.ncard : ℝ) := by
    intro hUbig
    have h1 := hS₃big hUbig
    have h2 : (10 * Real.sqrt γ + ε) * (n : ℝ) < 4 * ε * (n : ℝ) := by nlinarith
    linarith
  have hR₃M : ∀ i, ∀ e ∈ M i, e ∉ R₃ := by
    intro i e he hR
    have h2 : (edgeSize e : ℝ) = 2 := by
      have h := (mem_pow2.mp (hR₃pow hR)).2
      rw [h]; norm_num
    have hlarge : r₀ < (edgeSize e : ℝ) := by
      rw [hM] at he
      obtain ⟨e', he', heq⟩ := he
      obtain ⟨hmed, hcl⟩ := mem_colourFam.mp he'
      have hh := (IsS12Colours.large_nonhuge_of_buff_union_final hS12
        (Finset.mem_union_left Cfinal (colourEnum_mem Cbuff i))
        (⟨(e' : Set (Fin n)), hmed⟩ : ↥(medLarge 𝓗 (r₁ : ℝ))) hcl).1
      rw [← heq]
      exact_mod_cast hh
    have : (2 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr₀
    linarith
  -- ### The `M_i` and `𝓗_rem` have no singleton edges
  have hMns : ∀ i, ∀ e ∈ M i, 2 ≤ e.ncard := by
    intro i e he
    rw [hM] at he
    obtain ⟨e', he', heq⟩ := he
    obtain ⟨hmed, hcl⟩ := mem_colourFam.mp he'
    have hlarge := (IsS12Colours.large_nonhuge_of_buff_union_final hS12
      (Finset.mem_union_left Cfinal (colourEnum_mem Cbuff i))
      (⟨(e' : Set (Fin n)), hmed⟩ : ↥(medLarge 𝓗 (r₁ : ℝ))) hcl).1
    have h2 : (2 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr₀
    have hlarge' : (r₀ : ℝ) < (edgeSize e : ℝ) := by rw [← heq]; exact hlarge
    have h3 : (2 : ℝ) < (edgeSize e : ℝ) := lt_of_le_of_lt h2 hlarge'
    have h4 : 2 < edgeSize e := by exact_mod_cast h3
    rw [edgeSize_eq_ncard] at h4
    omega
  have hremNs : ∀ e ∈ 𝓗rem, 2 ≤ e.ncard := by
    intro e he
    have h1 := hbig e (hremEdges he)
    rw [edgeSize_eq_ncard] at h1
    omega
  -- ### Apply the Leftover Lemma
  have hremSize' : ∀ e ∈ 𝓗rem, edgeSize e ≤ max r₁ 2 :=
    fun e he => le_trans (hremSize e he) (le_max_left r₁ 2)
  obtain ⟨G, hGsub, hGmat, hGadd, hGdisj, hGcover, hGperf, hGnear⟩ :=
    leftover_colouring_lemma hleft.hK (le_max_right r₁ 2) (MultiHypergraph.ofHypergraph 𝓗)
      R₃ 𝓗rem M
      (MultiHypergraph.isLinear_ofHypergraph hbig hlin)
      hU' hL1 hL1' hMns hMmat hMdisj hMsize hR₃pow hR₃M hL3'
      hremNs hremEdges hremR hremM hremDegAt hremSize' hremOv hS₃sub hL5'
      hleft.hm hleft.hn4
      (by rw [hS12.hCmain_card]; exact hleft.hDn)
      (by rw [hS12.hCmain_card]; exact hleft.hkanthr)
      (by rw [hS12.hCmain_card, hS12.hCbuff_card]; exact hleft.hTm)
      (by rw [hS12.hCbuff_card]; exact hleft.hcher)
  -- ### The matchings of `C_buff`
  have hGsub𝓗 : ∀ j, G j ⊆ 𝓗 := fun j e he => by
    have h := (hGmat j).1 he
    rwa [MultiHypergraph.edgeSet_ofHypergraph] at h
  have hGns : ∀ j, ∀ e ∈ G j, 2 ≤ (e : Set (Fin n)).ncard := by
    intro j e he
    have := hbig e (hGsub𝓗 j he)
    rwa [edgeSize_eq_ncard] at this
  let Mbuff : Fin n → Set 𝓗 := fun c =>
    if h : c ∈ Cbuff then toFam (G ((Cbuff.orderIsoOfFin rfl).symm ⟨c, h⟩)) else ∅
  have hidx : ∀ (c : Fin n) (hc : c ∈ Cbuff),
      colourEnum Cbuff ((Cbuff.orderIsoOfFin rfl).symm ⟨c, hc⟩) = c :=
    fun c hc => colourEnum_symm hc
  have hMb_mem : ∀ (c : Fin n) (hc : c ∈ Cbuff),
      Mbuff c = toFam (G ((Cbuff.orderIsoOfFin rfl).symm ⟨c, hc⟩)) := fun c hc => dif_pos hc
  have hMb_nmem : ∀ c : Fin n, c ∉ Cbuff → Mbuff c = ∅ := fun c hc => dif_neg hc
  have hMb_match : ∀ i : Fin Cbuff.card, matchVert (Mbuff (colourEnum Cbuff i)) = famVert (G i) := by
    intro i
    have hidx2 : (Cbuff.orderIsoOfFin rfl).symm
        ⟨colourEnum Cbuff i, colourEnum_mem Cbuff i⟩ = i := by
      apply (Cbuff.orderIsoOfFin rfl).injective
      exact Subtype.ext (colourEnum_symm (colourEnum_mem Cbuff i))
    rw [hMb_mem _ (colourEnum_mem Cbuff i), hidx2,
      matchVert_toFam (hGsub𝓗 _) (fun e he => hGns _ e he)]
  refine ⟨Mbuff, hMb_nmem, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `φ⁻¹(c) ⊆ M_c`
    intro c hc e he
    rw [hMb_mem c hc, mem_toFam_iff]
    have hmem : (e : Set (Fin n)) ∈ M ((Cbuff.orderIsoOfFin rfl).symm ⟨c, hc⟩) := by
      have h1 : (e : Set (Fin n)) ∈ famOf (colourFam φ
          (colourEnum Cbuff ((Cbuff.orderIsoOfFin rfl).symm ⟨c, hc⟩))) := by
        rw [hidx c hc]
        exact ⟨e, he, rfl⟩
      exact h1
    exact ⟨hGsub _ hmem, by
      have h2 : 2 ≤ edgeSize (e : Set (Fin n)) := hbig _ (mem_colourFam.mp he).1.1
      rwa [edgeSize_eq_ncard] at h2⟩
  · -- the `M_c` are matchings of `𝓗`
    intro c
    by_cases hc : c ∈ Cbuff
    · rw [hMb_mem c hc]
      exact MultiHypergraph.IsMatching.toFam (hGmat _) (fun _ he => he)
    · rw [hMb_nmem c hc]
      exact isMatching_empty 𝓗
  · -- the added edges lie in `𝓗_rem ∪ R₃`
    intro c hc e he hne
    rw [hMb_mem c hc] at he
    have hinG : (e : Set (Fin n)) ∈ G ((Cbuff.orderIsoOfFin rfl).symm ⟨c, hc⟩) :=
      (mem_toFam_iff.mp he).1
    have hnotM : (e : Set (Fin n)) ∉ M ((Cbuff.orderIsoOfFin rfl).symm ⟨c, hc⟩) := by
      intro hmem
      have hmem' : (e : Set (Fin n)) ∈ famOf (colourFam φ
          (colourEnum Cbuff ((Cbuff.orderIsoOfFin rfl).symm ⟨c, hc⟩))) := hmem
      rw [hidx c hc] at hmem'
      obtain ⟨e', he', heq⟩ := hmem'
      rw [Subtype.ext heq] at he'
      exact hne he'
    exact hGadd _ (e : Set (Fin n)) hinG hnotM
  · -- every edge of `𝓗_rem` lies in one of the matchings
    intro e he
    obtain ⟨j, hj⟩ := hGcover e he
    refine ⟨colourEnum Cbuff j, colourEnum_mem Cbuff j, ?_⟩
    have hidx2 : (Cbuff.orderIsoOfFin rfl).symm
        ⟨colourEnum Cbuff j, colourEnum_mem Cbuff j⟩ = j := by
      apply (Cbuff.orderIsoOfFin rfl).injective
      exact Subtype.ext (colourEnum_symm (colourEnum_mem Cbuff j))
    rw [hMb_mem _ (colourEnum_mem Cbuff j), hidx2, famOf_toFam]
    exact ⟨hremEdges he, hj, hGns j _ hj⟩
  · -- distinct colour classes of `C_buff` are edge-disjoint
    intro c c' hne
    by_cases hc : c ∈ Cbuff
    · by_cases hc' : c' ∈ Cbuff
      · have hidxne : (Cbuff.orderIsoOfFin rfl).symm ⟨c, hc⟩ ≠
            (Cbuff.orderIsoOfFin rfl).symm ⟨c', hc'⟩ := by
          intro h
          exact hne (by
            have := congrArg (fun x : Fin Cbuff.card => colourEnum Cbuff x) h
            rwa [hidx c hc, hidx c' hc'] at this)
        have hd : Disjoint (nonsing (G _)) (nonsing (G _)) := hGdisj _ _ hidxne
        rw [hMb_mem c hc, hMb_mem c' hc', famOf_toFam, famOf_toFam]
        exact Set.disjoint_of_subset_left (fun e he => he.2)
          (Set.disjoint_of_subset_right (fun e he => he.2) hd)
      · rw [hMb_nmem c' hc']
        simp [famOf]
    · rw [hMb_nmem c hc]
      simp [famOf]
  · -- perfect coverage
    intro hUc c hc
    rw [Covers, hMb_mem c hc, matchVert_toFam (hGsub𝓗 _) (fun e he => hGns _ e he)]
    exact hGperf hUc _
  · -- nearly-perfect coverage
    intro hUc
    refine ⟨?_, ?_⟩
    · intro c hc
      rw [hMb_mem c hc, matchVert_toFam (hGsub𝓗 _) (fun e he => hGns _ e he)]
      exact (hGnear hUc).2.2 _
    · intro c hc
      rw [hMb_mem c hc, matchVert_toFam (hGsub𝓗 _) (fun e he => hGns _ e he)]
      exact (hGnear hUc).2.1 _
  · -- the per-vertex bound on the misses of `𝓜_buff`
    intro u hu
    rw [ncard_finset_subtype_eq (s := Cbuff) (P := fun c => u ∉ matchVert (Mbuff c))]
    by_cases hUc : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ)
    · -- nearly-perfect coverage: at most one colour misses `u`
      have h1 : (({i : Fin Cbuff.card | u ∈ famVert (G i)} : Set (Fin Cbuff.card)).ncard : ℝ) + 1 ≥
          (Fintype.card (Fin Cbuff.card) : ℝ) := (hGnear hUc).1 u hu
      rw [Fintype.card_fin] at h1
      have hsplit : ({i : Fin Cbuff.card | u ∉ famVert (G i)} : Set (Fin Cbuff.card)).ncard +
          ({i : Fin Cbuff.card | u ∈ famVert (G i)} : Set (Fin Cbuff.card)).ncard = Cbuff.card := by
        have hcomp : ({i : Fin Cbuff.card | u ∈ famVert (G i)} : Set (Fin Cbuff.card))ᶜ =
            {i : Fin Cbuff.card | u ∉ famVert (G i)} := by
          ext i
          simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
        have hc := Set.ncard_compl_add_ncard
          ({i : Fin Cbuff.card | u ∈ famVert (G i)} : Set (Fin Cbuff.card))
        rw [hcomp] at hc
        rw [hc, Nat.card_eq_fintype_card, Fintype.card_fin]
      have h2 : ({i : Fin Cbuff.card | u ∉ famVert (G i)} : Set (Fin Cbuff.card)).ncard ≤ 1 := by
        have h3 : (({i : Fin Cbuff.card | u ∉ famVert (G i)} :
            Set (Fin Cbuff.card)).ncard : ℝ) ≤ 1 := by
          have h4 := congrArg (fun x : ℕ => (x : ℝ)) hsplit
          push_cast at h4
          linarith
        exact_mod_cast h3
      refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) h2
      intro i hi
      show u ∉ famVert (G i)
      have hhi : u ∉ matchVert (Mbuff (colourEnum Cbuff i)) := hi
      rwa [hMb_match i] at hhi
    · -- perfect coverage: no colour misses `u`
      have hempty : ({i : Fin Cbuff.card | u ∉ matchVert (Mbuff (colourEnum Cbuff i))} :
          Set (Fin Cbuff.card)) = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨i, hi⟩
        have hhi : u ∉ matchVert (Mbuff (colourEnum Cbuff i)) := hi
        rw [hMb_match i] at hhi
        exact hhi (hGperf (not_lt.mp hUc) i hu)
      rw [hempty, Set.ncard_empty]
      omega

end

end ErdosFaberLovaszConjecture
