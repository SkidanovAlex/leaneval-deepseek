import Submission.EFL.S12Mprev
import Submission.EFL.LineGraph
import Submission.Commons.Combinatorics.SimpleGraph.hallFinishing_of_pairFamily

/-!
# §12, Step 10: the final colouring

Step 10 of §12 colours the edges of `G_final` with the colours of `C_final`,
compatibly with the partial colouring `φ` of the medium/large edges, and then
combines the `n - |C_final|` matchings of `𝓜_prev` with the `|C_final|`
matchings found here into an `n`-colouring of `𝓗`.

The mathematical inputs of the step are Vizing's theorem (Case A₁), Corollary
10.13 (`cor:optcol`, Case A₂) and the Hall-based finishing lemma (Lemma 10.2,
Case B).  In this module we

* package the output of the step as the structure `S12Finishing` (a family of
  matchings supported on `C_final`, extending the colour classes of `φ` and
  covering the leftover graph `R_final`);
* prove the two "graph-colouring" cases A₁/A₂ in one stroke
  (`exists_finishing_of_colorable`): any colouring of the leftover 2-graph `R`
  with `|C_final|` colours, together with the vanishing of the colour classes
  `φ⁻¹(c)` of `φ` on `C_final` (the paper's (T1)), yields `S12Finishing`;
* prove the final packaging `chromaticIndex_le_of_decomposition`: `𝓜_prev`
  together with the output of Step 10 gives `χ'(𝓗) ≤ n`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-! ## Preliminaries on the leftover 2-graph -/

/-- For a family `R` of two-element sets, the neighbours of `v` in `R` are
exactly the `w ≠ v` with `{v,w} ∈ R`. -/
theorem nbrs_eq_pair_offdiag {R : Hypergraph (Fin n)} (hR2 : ∀ e ∈ R, e.ncard = 2)
    (v : Fin n) : nbrs R v = {w : Fin n | w ≠ v ∧ ({v, w} : Set (Fin n)) ∈ R} := by
  ext w
  constructor
  · intro hw
    exact ⟨fun hwv => notMem_nbrs_self R hR2 v (hwv ▸ hw), hw⟩
  · rintro ⟨_, hw⟩
    exact hw

/-- For a family `R` of two-element sets, `degAt R v` is the number of
`w ≠ v` with `{v,w} ∈ R` (the form in which the Vizing-type bounds are
stated). -/
theorem degAt_eq_pair_offdiag {R : Hypergraph (Fin n)} (hR2 : ∀ e ∈ R, e.ncard = 2)
    (v : Fin n) :
    degAt R v = {w : Fin n | w ≠ v ∧ ({v, w} : Set (Fin n)) ∈ R}.ncard := by
  rw [degAt, nbrs_eq_pair_offdiag hR2 v]

/-! ## A pair-family colouring is a colouring of the 2-graph -/

/-- A colouring of a family of pairs (in the "Vizing" form used by the
commons lemmas) is an edge-colouring of the corresponding hypergraph. -/
theorem colorable_of_pairFamily_coloring {R : Hypergraph (Fin n)} {k : ℕ}
    (col : R → Fin k)
    (hcol : ∀ f₁ f₂ : R, f₁ ≠ f₂ → ((f₁.1 : Set (Fin n)) ∩ f₂.1).Nonempty →
      col f₁ ≠ col f₂) :
    R.Colorable k :=
  ⟨⟨col, hcol⟩⟩

/-! ## The output of Step 10 -/

/-- The output of §12 Step 10 on the colour set `Cfin`: a family of matchings
of `𝓗`, supported on `Cfin`, extending the colour classes of `φ` on `Cfin` and
covering the reserved graph `Rfin`. -/
structure S12Finishing {n : ℕ} (𝓗 : Hypergraph (Fin n)) {r₁ : ℝ}
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (Cfin : Finset (Fin n))
    (Rfin : Hypergraph (Fin n)) (Mfin : Fin n → Set 𝓗) : Prop where
  /-- `Mfin` is supported on `Cfin`. -/
  support : ∀ c ∉ Cfin, Mfin c = ∅
  /-- `Mfin` extends the colour class of `φ` at every colour of `Cfin`. -/
  extends_class : ∀ c ∈ Cfin, colourFam φ c ⊆ Mfin c
  /-- Every `Mfin c` is a matching of `𝓗`. -/
  matching : ∀ c, IsMatching 𝓗 (Mfin c)
  /-- The matchings cover the leftover graph `Rfin`. -/
  covers : ∀ e ∈ Rfin, ∃ c ∈ Cfin, e ∈ famOf (Mfin c)

theorem S12Finishing.support' {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {Cfin : Finset (Fin n)}
    {Rfin : Hypergraph (Fin n)} {Mfin : Fin n → Set 𝓗}
    (h : S12Finishing 𝓗 φ Cfin Rfin Mfin) : ∀ c ∉ Cfin, Mfin c = ∅ := h.support

/-! ## Cases A₁ and A₂: reducing to a colouring of the leftover 2-graph -/

/-- **§12 Step 10, the graph cases.**  If the leftover graph `R` is a subfamily
of `𝓗` that can be coloured with `|Cfin|` colours, and the colour classes of `φ`
on `Cfin` are empty (the paper's (T1), true in Types A₁ and A₂), then `R` is
covered by `|Cfin|` matchings extending those (empty) colour classes. -/
theorem exists_finishing_of_colorable {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {Cfin : Finset (Fin n)} {R : Hypergraph (Fin n)}
    (hRsub : R ⊆ 𝓗) (hcol : R.Colorable Cfin.card)
    (hempty : ∀ c ∈ Cfin, colourFam φ c = ∅) :
    ∃ Mfin : Fin n → Set 𝓗, S12Finishing 𝓗 φ Cfin R Mfin := by
  classical
  obtain ⟨C⟩ := hcol
  refine ⟨fun c => if h : c ∈ Cfin then
      subFam (𝓖 := R) (C.colorClass ((Cfin.orderIsoOfFin rfl).symm ⟨c, h⟩)) else ∅,
    ?_, ?_, ?_, ?_⟩
  · intro c hc
    exact dif_neg hc
  · intro c hc
    rw [dif_pos hc, hempty c hc]
    exact Set.empty_subset _
  · intro c
    by_cases h : c ∈ Cfin
    · rw [dif_pos h]
      exact (C.colorClass_isMatching _).subFam
    · rw [dif_neg h]
      exact isMatching_empty 𝓗
  · intro e he
    set c₀ : Fin Cfin.card := C.labels ⟨e, he⟩ with hc₀
    set c : Fin n := ((Cfin.orderIsoOfFin rfl) c₀).1 with hc
    have hcmem : c ∈ Cfin := ((Cfin.orderIsoOfFin rfl) c₀).2
    refine ⟨c, hcmem, ?_⟩
    refine ⟨⟨e, hRsub he⟩, ?_, rfl⟩
    rw [dif_pos hcmem]
    refine ⟨he, ?_⟩
    rw [mem_colorClass]
    have hsymm : ((Cfin.orderIsoOfFin rfl).symm ⟨c, hcmem⟩) = c₀ := by
      refine (Cfin.orderIsoOfFin rfl).injective ?_
      rw [OrderIso.apply_symm_apply]
    rw [hsymm]

/-- **§12 Step 10, Case A₁ (Vizing).**  The paper's Case 1: if the leftover
graph `R = R_final` has maximum degree at most `|C_final| - 1`, Vizing gives a
colour class decomposition and `S12Finishing` follows. -/
theorem exists_finishing_vizing {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {Cfin : Finset (Fin n)} {R : Hypergraph (Fin n)}
    {D : ℕ} (hRsub : R ⊆ 𝓗)
    (hcol : ∃ col : R → Fin D, ∀ f₁ f₂ : R, f₁ ≠ f₂ →
      ((f₁.1 : Set (Fin n)) ∩ f₂.1).Nonempty → col f₁ ≠ col f₂)
    (hempty : ∀ c ∈ Cfin, colourFam φ c = ∅) (hk : D ≤ Cfin.card) :
    ∃ Mfin : Fin n → Set 𝓗, S12Finishing 𝓗 φ Cfin R Mfin := by
  obtain ⟨col, hcol'⟩ := hcol
  exact exists_finishing_of_colorable hRsub
    (Hypergraph.Colorable.mono hk (colorable_of_pairFamily_coloring col hcol')) hempty

/-- **§12 Step 10, Case A₁ (Vizing), from the degree bound.**  Vizing's theorem
in the pair-family form
(`Commons.Combinatorics.SimpleGraph.edgeColoring_of_pairFamily`, ported into
the cone as `Submission/EFL/Comm/EdgeColoringPairFamily.lean`) gives the colour
class decomposition of the leftover graph. -/
theorem exists_finishing_vizing_of_degAt {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {Cfin : Finset (Fin n)} {R : Hypergraph (Fin n)}
    (hRsub : R ⊆ 𝓗) (hR2 : ∀ e ∈ R, e.ncard = 2)
    (hdeg : ∀ w : Fin n,
      {x : Fin n | x ≠ w ∧ ({w, x} : Set (Fin n)) ∈ R}.ncard ≤ Cfin.card - 1)
    (hk : 1 ≤ Cfin.card)
    (hempty : ∀ c ∈ Cfin, colourFam φ c = ∅) :
    ∃ Mfin : Fin n → Set 𝓗, S12Finishing 𝓗 φ Cfin R Mfin := by
  classical
  obtain ⟨col, hcol⟩ :=
    Commons.Combinatorics.SimpleGraph.edgeColoring_of_pairFamily R hR2 (Cfin.card - 1) hdeg
  have hcast : Cfin.card - 1 + 1 = Cfin.card := by omega
  refine exists_finishing_vizing (D := Cfin.card) hRsub ?_ hempty le_rfl
  refine ⟨fun f => Fin.cast hcast (col f), ?_⟩
  intro f₁ f₂ hne hinn h
  exact hcol f₁ f₂ hne hinn (Fin.cast_injective hcast h)

/-! ## Case B: the Hall-based finishing -/

/-- The paper's `C_w = {c ∈ C_final : w ∈ V(φ⁻¹(c))}`: the colours of `C_final`
whose colour class of `φ` contains the vertex `w`. -/
def finalColoursAt {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (Cfin : Finset (Fin n)) (w : Fin n) :
    Finset (Fin n) :=
  Cfin.filter (fun c => w ∈ matchVert (colourFam φ c))

theorem mem_finalColoursAt {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {Cfin : Finset (Fin n)} {w c : Fin n} :
    c ∈ finalColoursAt φ Cfin w ↔ c ∈ Cfin ∧ w ∈ matchVert (colourFam φ c) := by
  simp only [finalColoursAt, Finset.mem_filter]

/-- **§12 Step 10, Case B (Hall-based finishing).**  If the leftover graph `R`
admits an edge-colouring `ψ` with colours in `Cfin` that avoids, at both ends of
every edge, the colours of `Cfin` already used by `φ` at that vertex (the output
of the Hall-based finishing lemma, Lemma 10.2), then `ψ⁻¹(c) ∪ φ⁻¹(c)` is a
matching for every `c ∈ Cfin`, and `S12Finishing` follows. -/
theorem exists_finishing_hall {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {Cfin : Finset (Fin n)} {R : Hypergraph (Fin n)}
    (hRsub : R ⊆ 𝓗)
    (hψ : ∃ ψ : R → Fin n, (∀ e : R, ψ e ∈ Cfin) ∧
      (∀ e₁ e₂ : R, e₁ ≠ e₂ → ((e₁.1 : Set (Fin n)) ∩ e₂.1).Nonempty → ψ e₁ ≠ ψ e₂) ∧
      (∀ e : R, ∀ v ∈ (e.1 : Set (Fin n)), ψ e ∉ finalColoursAt φ Cfin v)) :
    ∃ Mfin : Fin n → Set 𝓗, S12Finishing 𝓗 φ Cfin R Mfin := by
  classical
  obtain ⟨ψ, hψC, hψprop, hψavoid⟩ := hψ
  refine ⟨fun c => if h : c ∈ Cfin then
      {e : 𝓗 | (∃ he : (e : Set (Fin n)) ∈ R,
          ψ (⟨(e : Set (Fin n)), he⟩ : R) = c) ∨ e ∈ colourFam φ c} else ∅,
    ?_, ?_, ?_, ?_⟩
  · intro c hc
    exact dif_neg hc
  · intro c hc
    rw [dif_pos hc]
    intro e he
    exact Or.inr he
  · intro c
    by_cases h : c ∈ Cfin
    · rw [dif_pos h]
      intro a ha b hb hab
      simp only [Set.mem_ofPred_eq] at ha hb
      rcases ha with ⟨he₁, hψ₁⟩ | ha'
      · rcases hb with ⟨he₂, hψ₂⟩ | hb'
        · by_contra hdisj
          rw [Set.not_disjoint_iff] at hdisj
          obtain ⟨v, hv₁, hv₂⟩ := hdisj
          have hne : (⟨(a : Set (Fin n)), he₁⟩ : R) ≠ ⟨(b : Set (Fin n)), he₂⟩ := by
            intro hEq
            exact hab (Subtype.ext (congrArg (fun x : R => (x : Set (Fin n))) hEq))
          exact hψprop _ _ hne ⟨v, hv₁, hv₂⟩ (by rw [hψ₁, hψ₂])
        · by_contra hdisj
          rw [Set.not_disjoint_iff] at hdisj
          obtain ⟨v, hv₁, hv₂⟩ := hdisj
          have hvC : c ∈ finalColoursAt φ Cfin v := by
            rw [mem_finalColoursAt, mem_matchVert]
            exact ⟨h, b, hb', hv₂⟩
          rw [← hψ₁] at hvC
          exact hψavoid _ v hv₁ hvC
      · rcases hb with ⟨he₂, hψ₂⟩ | hb'
        · by_contra hdisj
          rw [Set.not_disjoint_iff] at hdisj
          obtain ⟨v, hv₁, hv₂⟩ := hdisj
          have hvC : c ∈ finalColoursAt φ Cfin v := by
            rw [mem_finalColoursAt, mem_matchVert]
            exact ⟨h, a, ha', hv₁⟩
          rw [← hψ₂] at hvC
          exact hψavoid _ v hv₂ hvC
        · exact isMatching_colourFam c ha' hb' hab
    · rw [dif_neg h]
      exact isMatching_empty 𝓗
  · intro e he
    refine ⟨ψ ⟨e, he⟩, hψC ⟨e, he⟩, ?_⟩
    refine ⟨⟨e, hRsub he⟩, ?_, rfl⟩
    rw [dif_pos (hψC ⟨e, he⟩)]
    exact Or.inl ⟨he, rfl⟩

/-- **§12 Step 10, Case B, from the numerical data.**  Same as
`exists_finishing_hall`, with the Hall-type hypotheses of Lemma 10.2 supplied in
the form in which they arise in the paper: `7δn ≤ |C_final|`, the FPP-extremal
set `U` is small and meets every edge of the leftover graph, the degree
deficiencies `d_{R_final}(w) ≤ |C_final| - 1 - |C_w|`, and the two smallness
conditions `|C_w| ≤ δn`, `|{w : c ∈ C_w}| ≤ δn`. -/
theorem exists_finishing_hall_of_margins {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {Cfin : Finset (Fin n)} {R : Hypergraph (Fin n)}
    {U : Set (Fin n)} {δ : ℝ}
    (hRsub : R ⊆ 𝓗) (hR2 : ∀ e ∈ R, e.ncard = 2)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hC : 7 * δ * (n : ℝ) ≤ (Cfin.card : ℝ))
    (hUfin : (U.ncard : ℝ) ≤ δ * (n : ℝ))
    (hUcov : ∀ e ∈ R, ∃ u ∈ e, u ∈ U)
    (hdeg : ∀ w : Fin n, degAt R w + (finalColoursAt φ Cfin w).card ≤ Cfin.card - 1)
    (hCw : ∀ w : Fin n, ((finalColoursAt φ Cfin w).card : ℝ) ≤ δ * (n : ℝ))
    (hCcol : ∀ c ∈ Cfin,
      (((Finset.univ : Finset (Fin n)).filter (fun w => c ∈ finalColoursAt φ Cfin w)).card : ℝ)
        ≤ δ * (n : ℝ)) :
    ∃ Mfin : Fin n → Set 𝓗, S12Finishing 𝓗 φ Cfin R Mfin := by
  classical
  have hdeg' : ∀ w : Fin n,
      {x : Fin n | x ≠ w ∧ ({w, x} : Set (Fin n)) ∈ R}.ncard ≤ Cfin.card -
        (finalColoursAt φ Cfin w).card := by
    intro w
    rw [← degAt_eq_pair_offdiag hR2 w]
    have h := hdeg w
    omega
  have hU' : ∃ U' : Finset (Fin n), (U'.card : ℝ) ≤ δ * (n : ℝ) ∧
      ∀ e ∈ R, ∃ u ∈ e, u ∈ U' := by
    refine ⟨vertFinset U, ?_, ?_⟩
    · rw [vertFinset_card]; exact hUfin
    · intro e he
      obtain ⟨u, hu, hUu⟩ := hUcov e he
      exact ⟨u, hu, by rw [mem_vertFinset]; exact hUu⟩
  obtain ⟨ψ, hψC, hψprop, hψavoid⟩ :=
    Commons.Combinatorics.SimpleGraph.hallFinishing_of_pairFamily R hR2 Cfin
      (finalColoursAt φ Cfin) δ hδ0 hδ1 hC hU' hdeg' hCw hCcol
  exact exists_finishing_hall hRsub ⟨ψ, hψC, hψprop, hψavoid⟩

/-! ## The final packaging: `𝓜_prev ∪ 𝓜_final` -/

/-- **§12 Step 10, the final packaging.**  Suppose `𝓜_prev` is a family of
matchings supported on the colour set `Cprev` and `𝓜_final` a family of
matchings supported on the disjoint colour set `Cfin`, and suppose that every
edge of `𝓗` lies in one of them.  Then `χ'(𝓗) ≤ n`. -/
theorem chromaticIndex_le_of_decomposition {𝓗 : Hypergraph (Fin n)}
    {Cprev Cfin : Finset (Fin n)} (hdisj : Disjoint Cprev Cfin)
    {Mprev Mfin : Fin n → Set 𝓗}
    (hmat1 : ∀ c, IsMatching 𝓗 (Mprev c)) (hmat2 : ∀ c, IsMatching 𝓗 (Mfin c))
    (hcov : ∀ e : 𝓗, (∃ c, c ∈ Cprev ∧ e ∈ Mprev c) ∨ (∃ c, c ∈ Cfin ∧ e ∈ Mfin c)) :
    𝓗.chromaticIndex ≤ n := by
  classical
  refine chromaticIndex_le_of_matchingDecomposition
    (M := fun c => if c ∈ Cprev then Mprev c else Mfin c) ?_ ?_
  · intro c
    by_cases h : c ∈ Cprev
    · rw [if_pos h]; exact hmat1 c
    · rw [if_neg h]; exact hmat2 c
  · intro e
    rcases hcov e with ⟨c, hc, he⟩ | ⟨c, hc, he⟩
    · exact ⟨c, by rw [if_pos hc]; exact he⟩
    · have hnc : c ∉ Cprev := fun h => Finset.disjoint_left.mp hdisj h hc
      exact ⟨c, by rw [if_neg hnc]; exact he⟩

/-- **§12 Step 10, the final assembly.**  `𝓜_prev` together with the output of
Step 10 (`S12Finishing`) covers every edge of `𝓗`: the edges of `𝓗` either lie
in `𝓜_prev`, in the leftover graph `R_final`, or in a colour class `φ⁻¹(c)` with
`c ∈ C_final`.  Since `𝓜_final` (from `S12Finishing`) covers the latter two and
`C_prev`, `C_final` are disjoint, `χ'(𝓗) ≤ n`. -/
theorem chromaticIndex_le_of_prev_and_finishing {𝓗 : Hypergraph (Fin n)}
    {Cprev Cfin : Finset (Fin n)} (hdisj : Disjoint Cprev Cfin)
    {Mprev : Fin n → Set 𝓗} (hmat1 : ∀ c, IsMatching 𝓗 (Mprev c))
    {r₁ : ℝ} {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {Rfin : Hypergraph (Fin n)}
    {Mfin : Fin n → Set 𝓗} (hfin : S12Finishing 𝓗 φ Cfin Rfin Mfin)
    (hcov : ∀ e : 𝓗, (∃ c, c ∈ Cprev ∧ e ∈ Mprev c) ∨
        ((e : Set (Fin n)) ∈ Rfin ∨ ∃ c, c ∈ Cfin ∧ e ∈ colourFam φ c)) :
    𝓗.chromaticIndex ≤ n := by
  classical
  refine chromaticIndex_le_of_decomposition hdisj hmat1 hfin.matching ?_
  intro e
  rcases hcov e with h | h
  · exact Or.inl h
  · right
    rcases h with hR | ⟨c, hc, he⟩
    · obtain ⟨c, hc, he'⟩ := hfin.covers _ hR
      obtain ⟨e', he'c, heq⟩ := he'
      exact ⟨c, hc, (Subtype.ext heq) ▸ he'c⟩
    · exact ⟨c, hc, hfin.extends_class c hc he⟩

end

end ErdosFaberLovaszConjecture
