import Submission.EFL.S12Setup
import Submission.EFL.HugeStep2
import Submission.EFL.LeftoverMargins
import Submission.EFL.Nibble
import Submission.EFL.S12Numeric
import Submission.EFL.Comm.InternalMatchingConnect
import Submission.Commons.Combinatorics.Partition.exists_colouring_parts_ge
import Submission.Commons.Combinatorics.BalancedColouring.exists_colouring_bounded_load

/-!
# §7: the Leftover Colouring Lemma (`lem:leftover`), assembled

This module proves the paper's Lemma `lem:leftover` (the Leftover Lemma) from
Kahn's theorem (`KahnStatement`) and the huge-edge absorption lemma
(`huge_edge_absorption`, Lemma 7.3), together with the small counting lemmas it
needs; it is placed *below* `S12Step7` so that the §12 chain can apply it there.

The proof: partition the colour set `Fin k` into `t = ⌈4/γ⌉` parts of size
`≥ γ²D/10`; colour the leftover hypergraph `𝓗_rem` into each part by Kahn's
theorem, avoiding the colours of the matchings `M_c` that the edge meets (Step
1, `exists_list_colouring_in_part`); merge the `t` colourings by sending each
edge to a random one of them (Step 2, `exists_merged_colouring`, a balanced
colouring produced by the union bound + Chernoff from the commons); then extend
each `M_c ∪ ψ⁻¹(c)` to a matching by the absorber `R` (Step 3,
`leftover_absorption`, Lemma 7.3).

The asymptotic hypotheses (`HugeMargins`, Kahn's threshold, the Chernoff
condition) are bundled in `LeftoverMargins` (`Submission/EFL/LeftoverMargins.lean`),
which `exists_leftoverMargins` shows to hold for all large `n` from a constant
hierarchy.

`LeftoverStatement` is stated for a `MultiHypergraph` (whose singleton edges
are available in several copies), while Lemma 7.3 is stated for a plain
`Hypergraph`; the relevant identifications are recorded first.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}


/-! ## Glue between multi-hypergraphs and hypergraphs -/

/-- `pow2` is idempotent. -/
theorem Hypergraph.pow2_idem (G : Hypergraph (Fin n)) :
    Hypergraph.pow2 (Hypergraph.pow2 G) = Hypergraph.pow2 G := by
  ext e
  simp only [mem_pow2]
  tauto

/-- The `2`-uniform part of a multi-hypergraph is the `2`-uniform part of its
underlying family of edges (the singletons have size one). -/
theorem MultiHypergraph.pow2_eq_edgeSet_pow2 (𝓜 : MultiHypergraph n) :
    𝓜.pow2 = Hypergraph.pow2 𝓜.edgeSet := by
  ext e
  simp only [MultiHypergraph.mem_pow2, mem_pow2, MultiHypergraph.mem_edgeSet]
  constructor
  · rintro ⟨he, hsz⟩
    exact ⟨Or.inl he, hsz⟩
  · rintro ⟨h, hsz⟩
    rcases h with h | ⟨v, rfl, -⟩
    · exact ⟨h, hsz⟩
    · rw [edgeSize_eq_ncard, Set.ncard_singleton] at hsz
      omega

/-- The `2`-edges incident to `U`: same description for a multi-hypergraph and
for its underlying family of edges. -/
theorem MultiHypergraph.incidentTwo_pow2 (𝓜 : MultiHypergraph n) (U : Set (Fin n)) :
    incidentTwo 𝓜.pow2 U = incidentTwo 𝓜.edgeSet U := by
  unfold incidentTwo
  rw [MultiHypergraph.pow2_eq_edgeSet_pow2 𝓜, Hypergraph.pow2_idem]

/-- A multi-hypergraph is linear iff its underlying family of edges is. -/
theorem MultiHypergraph.isLinear_edges {𝓜 : MultiHypergraph n} (h : 𝓜.IsLinear) :
    Hypergraph.IsLinear 𝓜.edges := h.2

/-- A subfamily of a linear family is linear. -/
theorem MultiHypergraph.edges_isLinear_of_subset {𝓜 : MultiHypergraph n}
    {𝓖 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓜.edges) (hlin : 𝓜.IsLinear) :
    Hypergraph.IsLinear 𝓖 :=
  hlin.2.mono hsub

/-! ## Step 1 of the Leftover Lemma: the Kahn list-colouring of each part

Given a linear hypergraph `𝓖` with `Δ(𝓖) ≤ D'`, edge sizes `≤ r`, a colour set
`P` of size `≥ (3/2)D'` and, on every edge, a forbidden list `L e ⊆ P` of size
`≤ D'/4`, Kahn's theorem (with `α = 1/2`) produces a proper colouring of `𝓖`
with colours in `P` avoiding all the lists. -/

/-- **Kahn's theorem (`α = 1/2`), transported to an arbitrary colour set.** -/
theorem exists_list_colouring_in_part {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    {D₀ : ℝ} (hD₀ : 0 < D₀)
    (hD₀body : ∀ D : ℝ, D₀ ≤ D → ∀ m : ℕ, ∀ 𝓖 : Hypergraph (Fin m), 𝓖.IsLinear →
      ((hypergraphMaxDegree 𝓖 : ℕ) : ℝ) ≤ D →
      (∀ e : 𝓖, (edgeSize (e : Set (Fin m)) : ℝ) ≤ (r : ℝ)) →
      ∀ c : ℕ, (3 / 2) * D ≤ (c : ℝ) → ∀ L : 𝓖 → Finset (Fin c),
        (∀ e : 𝓖, ((L e).card : ℝ) ≤ D / 4) →
        ∃ φ : 𝓖.Coloring (Fin c), ∀ e : 𝓖, φ.labels e ∉ L e)
    {n : ℕ} {𝓖 : Hypergraph (Fin n)} {P : Finset ι} {D' : ℝ}
    (hlin : 𝓖.IsLinear)
    (hΔ : ((hypergraphMaxDegree 𝓖 : ℕ) : ℝ) ≤ D')
    (hsize : ∀ e : 𝓖, (edgeSize (e : Set (Fin n)) : ℝ) ≤ (r : ℝ))
    (hPcard : (3 / 2) * D' ≤ (P.card : ℝ))
    (hD₀D' : D₀ ≤ D')
    (L : 𝓖 → Finset ι) (hLsub : ∀ e : 𝓖, L e ⊆ P)
    (hLcard : ∀ e : 𝓖, ((L e).card : ℝ) ≤ D' / 4) :
    ∃ ψ : 𝓖.Coloring ι, (∀ e : 𝓖, ψ.labels e ∈ P) ∧ ∀ e : 𝓖, ψ.labels e ∉ L e := by
  classical
  -- enumerate the colour set `P`
  have hcardP : Fintype.card ↥P = P.card := by simp
  set eP : ↥P ≃ Fin P.card := (Fintype.equivFin ↥P).trans (finCongr hcardP) with heP
  -- the forbidden lists, transported to `Fin P.card`
  set L' : 𝓖 → Finset (Fin P.card) :=
    fun e => Finset.univ.filter (fun i : Fin P.card => ((eP.symm i : ↥P) : ι) ∈ L e)
    with hL'
  have hL'card : ∀ e : 𝓖, ((L' e).card : ℝ) ≤ D' / 4 := by
    intro e
    have h1 : (L' e).card ≤ (L e).card := by
      refine Finset.card_le_card_of_injOn (fun i : Fin P.card => ((eP.symm i : ↥P) : ι))
        ?_ ?_
      · intro i hi
        rw [hL'] at hi
        exact (Finset.mem_filter.mp hi).2
      · intro i _ j _ hij
        exact eP.symm.injective (Subtype.ext hij)
    have h2 : ((L' e).card : ℝ) ≤ ((L e).card : ℝ) := by exact_mod_cast h1
    linarith [h2, hLcard e]
  have hD'0 : 0 < D' := lt_of_lt_of_le hD₀ hD₀D'
  obtain ⟨φ, hφ⟩ := hD₀body D' hD₀D' n 𝓖 hlin hΔ hsize P.card hPcard L' hL'card
  refine ⟨{ labels := fun e => ((eP.symm (φ.labels e) : ↥P) : ι)
            isColoring := fun e₁ e₂ h hne => ?_ }, ?_, ?_⟩
  · rintro heq
    exact φ.isColoring e₁ e₂ h hne (eP.symm.injective (Subtype.ext heq))
  · intro e
    exact (eP.symm (φ.labels e)).2
  · intro e hcon
    exact hφ e (by
      rw [hL']
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)


/-! ## Step 2 of the Leftover Lemma: merging the `t` colourings

Each edge independently picks one of the `t` colourings; by Chernoff + union
bound (the commons lemma `exists_colouring_bounded_load`) the resulting colour
classes are all small. -/

/-- **Merging `t` colourings.**  Given `t` proper colourings `ψ j` of `𝓖` with
pairwise disjoint colour sets `P j ∋ ψ j e`, if every class of every `ψ j` has
total edge size at most `W` and the union bound `|ι| · 2 exp(-τ²/(2(C(W/t+τ/3))))
< 1` holds, then there is a choice `pick : 𝓖 → Fin t` such that every colour
class of the merged colouring `e ↦ ψ (pick e) e` has total edge size at most
`W/t + τ`. -/
theorem exists_merged_colouring {𝓖 : Hypergraph (Fin n)} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {t : ℕ} (ht : 2 ≤ t) (ψ : Fin t → 𝓖.Coloring ι)
    (P : Fin t → Finset ι) (hP : ∀ j e, (ψ j).labels e ∈ P j)
    (hPdisj : ∀ j j', j ≠ j' → Disjoint (P j) (P j'))
    {C W τ : ℝ} (hC0 : 0 ≤ C) (hwle : ∀ e : 𝓖, (edgeSize (e : Set (Fin n)) : ℝ) ≤ C)
    (hW0 : 0 ≤ W) (hτ0 : 0 ≤ τ)
    (hW : ∀ (j : Fin t) (c : ι), c ∈ P j →
      (Finset.univ.filter (fun e : 𝓖 => (ψ j).labels e = c)).sum
        (fun e => (edgeSize (e : Set (Fin n)) : ℝ)) ≤ W)
    (hcard : (Fintype.card ι : ℝ) *
      (2 * Real.exp (-(τ ^ 2) / (2 * (C * (W / t + τ / 3))))) < 1) :
    ∃ pick : 𝓖 → Fin t, ∀ c : ι,
      (Finset.univ.filter (fun e : 𝓖 => (ψ (pick e)).labels e = c)).sum
        (fun e => (edgeSize (e : Set (Fin n)) : ℝ)) ≤ W / t + τ := by
  classical
  have ht0 : 0 < t := by omega
  -- the part containing a given colour (arbitrary if the colour is in no part)
  set jof : ι → Fin t := fun c =>
    if h : (Finset.univ.filter (fun j : Fin t => c ∈ P j)).Nonempty then h.choose
    else ⟨0, ht0⟩ with hjof
  have hjof_mem : ∀ c : ι, (∃ j, c ∈ P j) → c ∈ P (jof c) := by
    intro c h
    have hne : (Finset.univ.filter (fun j : Fin t => c ∈ P j)).Nonempty :=
      ⟨h.choose, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.choose_spec⟩⟩
    simp only [hjof, dif_pos hne]
    exact (Finset.mem_filter.mp hne.choose_spec).2
  have hjof_eq : ∀ c j, c ∈ P j → jof c = j := by
    intro c j hj
    have hmem := hjof_mem c ⟨j, hj⟩
    by_contra hne
    exact (Finset.disjoint_left.mp (hPdisj (jof c) j hne) hmem) hj
  have hχ : ∀ e j c, (ψ j).labels e = c → j = jof c := by
    intro e j c hc
    rw [← hc]
    exact (hjof_eq _ _ (hP j e)).symm
  have hW' : ∀ c : ι, (Finset.univ.filter (fun e : 𝓖 => (ψ (jof c)).labels e = c)).sum
      (fun e => (edgeSize (e : Set (Fin n)) : ℝ)) ≤ W := by
    intro c
    by_cases hc : c ∈ P (jof c)
    · exact hW (jof c) c hc
    · have hempty : (Finset.univ.filter (fun e : 𝓖 => (ψ (jof c)).labels e = c)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he
        have h1 : (ψ (jof c)).labels e = c := (Finset.mem_filter.mp he).2
        have h2 : (ψ (jof c)).labels e ∈ P (jof c) := hP (jof c) e
        rw [h1] at h2
        exact hc h2
      rw [hempty, Finset.sum_empty]
      exact hW0
  obtain ⟨pick, hpick⟩ :=
    Commons.Combinatorics.BalancedColouring.exists_colouring_bounded_load t ht jof
      (fun e j => (ψ j).labels e) hχ (fun e : 𝓖 => (edgeSize (e : Set (Fin n)) : ℝ))
      (fun e => Nat.cast_nonneg _) hC0 hwle hW0 hτ0 hW' hcard
  exact ⟨pick, hpick⟩


/-! ## The "full" family of a set family inside a hypergraph

`toFam` (of `Nibble.lean`) deletes the singleton edges, because in the
multi-hypergraph world they are available in several copies.  For the
absorption step of the Leftover Lemma we need the *full* family (`toFamFull`),
which keeps them: the singleton edges of a colour class do cover their vertex
and must be counted in the class's vertex set. -/

/-- The family of *all* edges of `𝓗` whose underlying vertex set lies in `G`
(singletons included, in contrast to `toFam`). -/
def toFamFull {𝓗 : Hypergraph (Fin n)} (G : Set (Set (Fin n))) : Set 𝓗 :=
  {e : 𝓗 | (e : Set (Fin n)) ∈ G}

theorem mem_toFamFull {𝓗 : Hypergraph (Fin n)} {G : Set (Set (Fin n))} {e : 𝓗} :
    e ∈ toFamFull (𝓗 := 𝓗) G ↔ (e : Set (Fin n)) ∈ G := Iff.rfl

/-- The vertex set of the full family is the union of the underlying sets. -/
theorem matchVert_toFamFull {𝓗 : Hypergraph (Fin n)} {G : Set (Set (Fin n))}
    (hG : G ⊆ 𝓗) : matchVert (toFamFull (𝓗 := 𝓗) G) = famVert G := by
  ext v
  rw [mem_matchVert, mem_famVert]
  constructor
  · rintro ⟨e, he, hve⟩
    exact ⟨(e : Set (Fin n)), he, hve⟩
  · rintro ⟨e, he, hve⟩
    exact ⟨⟨e, hG he⟩, he, hve⟩

/-- Going back: the underlying family of the full family is the original one. -/
theorem famOf_toFamFull {𝓗 : Hypergraph (Fin n)} {G : Set (Set (Fin n))}
    (hG : G ⊆ 𝓗) : famOf (toFamFull (𝓗 := 𝓗) G) = G := by
  ext e
  constructor
  · rintro ⟨e', he', rfl⟩
    exact he'
  · intro he
    exact ⟨⟨e, hG he⟩, he, rfl⟩

/-- A pairwise disjoint subfamily of `𝓗` is a matching. -/
theorem isMatching_toFamFull {𝓗 : Hypergraph (Fin n)} {G : Set (Set (Fin n))}
    (hG : G.Pairwise fun e₁ e₂ => Disjoint e₁ e₂) : IsMatching 𝓗 (toFamFull (𝓗 := 𝓗) G) :=
  fun e₁ h₁ e₂ h₂ hne => hG h₁ h₂ (fun heq => hne (Subtype.ext heq))

/-- A multi-hypergraph matching is a matching of the underlying family of
edges, after passing to the full family of subtypes. -/
theorem MultiHypergraph.IsMatching.toFamFull_edgeSet {𝓜 : MultiHypergraph n}
    {N : Set (Set (Fin n))} (hN : MultiHypergraph.IsMatching 𝓜 N) :
    ErdosFaberLovaszConjecture.IsMatching 𝓜.edgeSet (toFamFull (𝓗 := 𝓜.edgeSet) N) :=
  isMatching_toFamFull hN.2

/-- Conversely, a matching of the underlying family of edges (as a family of
subtypes) is a multi-hypergraph matching of its underlying family of sets. -/
theorem MultiHypergraph.isMatching_famOf_edgeSet {𝓜 : MultiHypergraph n}
    {N : Set 𝓜.edgeSet} (hN : ErdosFaberLovaszConjecture.IsMatching 𝓜.edgeSet N) :
    MultiHypergraph.IsMatching 𝓜 (famOf N) := by
  constructor
  · rintro e ⟨e', he', rfl⟩
    exact e'.2
  · intro e₁ h₁ e₂ h₂ hne
    obtain ⟨e₁', he₁', rfl⟩ := h₁
    obtain ⟨e₂', he₂', heq⟩ := h₂
    rw [← heq] at hne ⊢
    exact hN he₁' he₂' (fun heq' => hne (by rw [heq']))

/-- Edge-disjointness in the multi-hypergraph sense passes to the underlying
hypergraph, provided no singleton edge is involved (as in the application of
the Leftover Lemma, where all the relevant edges have size at least two). -/
theorem edgeDisjointFam_toFamFull {𝓜 : MultiHypergraph n} {N N' : Set (Set (Fin n))}
    (hns : ∀ e ∈ N, 2 ≤ e.ncard) (hns' : ∀ e ∈ N', 2 ≤ e.ncard)
    (h : EdgeDisjointFam N N') :
    Disjoint (toFamFull (𝓗 := 𝓜.edgeSet) N) (toFamFull (𝓗 := 𝓜.edgeSet) N') := by
  rw [EdgeDisjointFam, Set.disjoint_left] at h
  rw [Set.disjoint_left]
  intro e he he'
  exact h ⟨he, hns _ he⟩ ⟨he', hns' _ he'⟩


/-! ## Step 3 of the Leftover Lemma: the absorption

Given the colour classes `ψ⁻¹(c)` (as `cls c`) of the merged colouring and the
matchings `M c`, the families `M c ∪ cls c` are matchings of small vertex set
that avoid the absorber `R`; Lemma 7.3 (the huge-edge absorption) then extends
them to matchings `N c` with the desired coverage of `U`. -/

/-- **The absorption step of the Leftover Lemma.** -/
theorem leftover_absorption {𝓜 : MultiHypergraph n} {R : Hypergraph (Fin n)}
    {U S : Set (Fin n)} {ρ γ ξ ε : ℝ} {k : ℕ} {M cls : Fin k → Set (Set (Fin n))}
    (hm : HugeMargins n ρ ε γ (1 / 2) ξ) (hn4 : 4 ≤ n)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤
      (degAt (incidentTwo 𝓜.edgeSet U) u : ℝ))
    (hRpow : R ⊆ Hypergraph.pow2 𝓜.edgeSet)
    (hRabs : IsAbsorber (incidentTwo 𝓜.edgeSet U) R
      ({(Set.univ : Set (Fin n)), U} : Set (Set (Fin n))) ρ (10 * γ) ξ)
    (hns : ∀ i, ∀ e ∈ M i ∪ cls i, 2 ≤ e.ncard)
    (hMmat : ∀ i, MultiHypergraph.IsMatching 𝓜 (M i ∪ cls i))
    (hdisj : ∀ i j, i ≠ j → EdgeDisjointFam (M i ∪ cls i) (M j ∪ cls j))
    (havoid : ∀ i, ∀ e ∈ M i ∪ cls i, e ∉ R)
    (hsize : ∀ i, ((famVert (M i ∪ cls i)).ncard : ℝ) ≤ γ * (n : ℝ))
    (hSsub : S ⊆ U)
    (hSbig : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      (γ + ε) * (n : ℝ) < (S.ncard : ℝ))
    (hk : (k : ℝ) ≤ γ * (n : ℝ)) :
    ∃ N : Fin k → Set (Set (Fin n)),
      (∀ i, M i ∪ cls i ⊆ N i) ∧
      (∀ i, ∀ e ∈ N i, e ∉ M i ∪ cls i → e ∈ R) ∧
      (∀ i, MultiHypergraph.IsMatching 𝓜 (N i)) ∧
      (∀ i j, i ≠ j → EdgeDisjointFam (N i) (N j)) ∧
      (((U.ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ)) → ∀ i, CoversFamMulti (N i) U) ∧
      (((1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ)) → NearlyPerfectCoverageFam N U S) := by
  classical
  haveI : Fintype 𝓜.edgeSet := Fintype.ofFinite _
  -- the matchings of the underlying hypergraph
  set N₀ : Fin k → Set 𝓜.edgeSet := fun i => toFam (M i ∪ cls i) with hN₀
  have hN₀mat : ∀ i, IsMatching 𝓜.edgeSet (N₀ i) := fun i =>
    isMatching_toFam (hMmat i).2
  have hN₀disj : ∀ i j, i ≠ j → Disjoint (N₀ i) (N₀ j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro e he he'
    rw [hN₀, mem_toFam] at he he'
    exact Set.disjoint_left.mp (hdisj i j hij) he he'
  have hN₀R : ∀ i, ∀ e ∈ N₀ i, (e : Set (Fin n)) ∉ R := by
    intro i e he
    rw [hN₀, mem_toFam] at he
    exact havoid i _ he.1
  have hN₀sub : ∀ i, M i ∪ cls i ⊆ 𝓜.edgeSet := fun i e he => (hMmat i).1 he
  have hN₀abs : ∀ i, AbsorbableBySmall 𝓜.edgeSet (N₀ i) R U S ρ ε γ (1 / 2) ξ := by
    intro i
    refine ⟨⟨{(Set.univ : Set (Fin n)), U}, ?_, ?_, ?_⟩, ?_, ?_⟩
    · exact Set.mem_insert_iff.mpr (Or.inr rfl)
    · exact Set.mem_insert_iff.mpr (Or.inl rfl)
    · exact hRabs
    · intro e he
      exact hN₀R i e he
    · rw [show N₀ i = toFam (𝓗 := 𝓜.edgeSet) (M i ∪ cls i) from rfl,
        matchVert_toFam (𝓗 := 𝓜.edgeSet) (G := M i ∪ cls i) (hN₀sub i) (hns i)]
      exact hsize i
  obtain ⟨N', hN'sub, hN'add, hN'mat, hN'disj, hN'perf, hN'near⟩ :=
    huge_edge_absorption (𝓗 := 𝓜.edgeSet) (R := R) (U := U) (S := S) (B := 0)
      hm (internalMatchingInput n 0) hUdeg hn4 (by push_cast; have := hm.hγ; positivity) hRpow hSsub hSbig N₀
      (fun i => Or.inl (hN₀abs i)) hN₀R hN₀mat hN₀disj hk
  -- pass back to the multi-hypergraph world
  have hfamN₀ : ∀ i, famOf (N₀ i) = M i ∪ cls i := fun i =>
    famOf_toFam_eq (𝓗 := 𝓜.edgeSet) (hN₀sub i) (hns i)
  refine ⟨fun i => famOf (N' i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `F1`: the initial matchings are contained
    intro i e he
    have h1 : e ∈ famOf (N₀ i) := by rw [hfamN₀ i]; exact he
    exact famOf_mono (hN'sub i) h1
  · -- `F1`: the added edges lie in `R`
    intro i e he hne
    obtain ⟨e', he', heq⟩ := mem_famOf.mp he
    have h1 : e' ∉ N₀ i := by
      intro hcon
      exact hne (by
        rw [← heq, ← hfamN₀ i]
        exact famOf_subset_self e' hcon)
    have h2 := hN'add i e' he' h1
    rwa [heq] at h2
  · -- the classes are matchings
    intro i
    exact MultiHypergraph.isMatching_famOf_edgeSet (hN'mat i)
  · -- the classes are pairwise edge-disjoint
    intro i j hij
    rw [EdgeDisjointFam, Set.disjoint_left]
    rintro e ⟨he, -⟩ ⟨he', -⟩
    obtain ⟨e₁, he₁, heq₁⟩ := mem_famOf.mp he
    obtain ⟨e₂, he₂, heq₂⟩ := mem_famOf.mp he'
    have hEq : e₁ = e₂ := Subtype.ext (heq₁.trans heq₂.symm)
    exact (Set.disjoint_left.mp (hN'disj i j hij) he₁) (hEq ▸ he₂)
  · -- perfect coverage
    intro hU i u hu
    have h1 : u ∈ matchVert (N' i) := hN'perf hU i hu
    rw [famVert_famOf (N' i)]
    exact h1
  · -- nearly perfect coverage
    intro hU
    obtain ⟨h1, h2, h3⟩ := hN'near hU
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      have h := h1 u hu
      have hset : {i : Fin k | u ∈ famVert (famOf (N' i))} =
          {i : Fin k | u ∈ matchVert (N' i)} := by
        ext i
        exact iff_of_eq (congrArg (fun X : Set (Fin n) => u ∈ X) (famVert_famOf (N' i)))
      rw [hset]
      simpa using h
    · intro i
      have h := h2 i
      rw [famVert_famOf (N' i)]
      exact h
    · intro i
      have h := h3 i
      rw [famVert_famOf (N' i)]
      exact h





/-! ## Elementary counting lemmas for finite families of vertex sets -/

/-- The vertex set of a finite family of subsets of `Fin n` is the union of the
`verts` of its members. -/
theorem famVert_finset_eq_biUnion {S : Finset (Set (Fin n))} :
    famVert (S : Set (Set (Fin n))) = ((S.biUnion fun e => verts e) : Set (Fin n)) := by
  ext v
  simp [famVert, Set.mem_sUnion, mem_verts]

/-- The vertex set of a finite family is at most the sum of the edge sizes. -/
theorem ncard_famVert_finset_le {S : Finset (Set (Fin n))} :
    (famVert (S : Set (Set (Fin n)))).ncard ≤ ∑ e ∈ S, edgeSize e := by
  rw [famVert_finset_eq_biUnion, Set.ncard_coe_finset]
  exact Finset.card_biUnion_le

/-- The sum of the edge sizes of a pairwise disjoint family of subsets of
`Fin n` is at most `n`. -/
theorem sum_edgeSize_le_of_pairwise_disjoint {S : Finset (Set (Fin n))}
    (hdisj : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint e f) :
    ∑ e ∈ S, edgeSize e ≤ n := by
  have hd : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint (verts e) (verts f) := by
    intro e he f hf hne
    rw [Finset.disjoint_left]
    intro v hve hvf
    exact (Set.disjoint_left.mp (hdisj e he f hf hne)) ((mem_verts e v).mp hve)
      ((mem_verts f v).mp hvf)
  show ∑ e ∈ S, (verts e).card ≤ n
  rw [← Finset.card_biUnion hd]
  simpa using Finset.card_le_univ (S.biUnion fun e => verts e)

/-- `Set.ncard` of a set-builder on `Fin k` is the cardinality of the
corresponding filtered finset. -/
theorem ncard_setOf_eq_card_filter {k : ℕ} (p : Fin k → Prop) [DecidablePred p] :
    (({i : Fin k | p i} : Set (Fin k)).ncard) = (Finset.univ.filter p).card := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]


/-! ## The Leftover Colouring Lemma -/

/-- **Lemma `lem:leftover`** (the Leftover Lemma): the remaining edges `𝓗_rem`
are coloured by Kahn's theorem into the buffer colour set, each colour class
being extended (together with the given matching `M_c`) to a matching by the
absorber `R`.  This is the conclusion of `LeftoverStatement`, with the
asymptotic hypotheses made explicit (`HugeMargins`, the Kahn threshold, and
the Chernoff condition for the merging step). -/
theorem leftover_colouring_lemma {n : ℕ} (hK : KahnStatement) {r : ℕ} (hr : 2 ≤ r)
    (𝓜 : MultiHypergraph n) (R : Hypergraph (Fin n)) (𝓗rem : Hypergraph (Fin n))
    {U S : Set (Fin n)} {ρ γ ξ ε : ℝ} {D k : ℕ} (M : Fin k → Set (Set (Fin n)))
    (hlin : 𝓜.IsLinear)
    (hU : U = VplusTwo (MultiHypergraph.pow2 𝓜) (1 - ε))
    (hL1a : γ * (D : ℝ) / 2 ≤ (k : ℝ)) (hL1b : (k : ℝ) ≤ γ * (D : ℝ))
    (hMns : ∀ i, ∀ e ∈ M i, 2 ≤ e.ncard)
    (hMmat : ∀ i, MultiHypergraph.IsMatching 𝓜 (M i))
    (hMdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j))
    (hMsize : ∀ i, ((famVert (M i)).ncard : ℝ) ≤ γ * (n : ℝ) / 2)
    (hRpow : R ⊆ MultiHypergraph.pow2 𝓜)
    (hMR : ∀ i, ∀ e ∈ M i, e ∉ R)
    (hRabs : IsAbsorber (incidentTwo (MultiHypergraph.pow2 𝓜) U) R
      ({(Set.univ : Set (Fin n)), U} : Set (Set (Fin n))) ρ (10 * γ) ξ)
    (hremns : ∀ e ∈ 𝓗rem, 2 ≤ e.ncard)
    (hremsub : 𝓗rem ⊆ 𝓜.edges)
    (hremR : ∀ e ∈ 𝓗rem, e ∉ R)
    (hremM : ∀ e ∈ 𝓗rem, ∀ i, e ∉ M i)
    (hremdeg : ∀ v : Fin n, (MultiHypergraph.hdeg 𝓗rem v : ℝ) ≤ γ ^ 2 * (D : ℝ) / 20)
    (hremsize : ∀ e ∈ 𝓗rem, edgeSize e ≤ r)
    (hremlist : ∀ e ∈ 𝓗rem, (({i : Fin k | ((e : Set (Fin n)) ∩ famVert (M i)).Nonempty}).ncard : ℝ) ≤
      γ ^ 2 * (D : ℝ) / 100)
    (hSsub : S ⊆ U)
    (hSbig : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) → (γ + ε) * (n : ℝ) < (S.ncard : ℝ))
    (hm : HugeMargins n ρ ε γ (1 / 2) ξ) (hn4 : 4 ≤ n) (hDn : (D : ℝ) ≤ (n : ℝ))
    (hkanthr : 20 * kahnD₀ hK r hr ≤ γ ^ 2 * (D : ℝ))
    (hTm : leftoverT γ * leftoverM γ D ≤ k)
    (hcher : (k : ℝ) * (2 * Real.exp (-((γ * (n : ℝ) / 4) ^ 2) /
      (2 * ((r : ℝ) * ((n : ℝ) / (leftoverT γ : ℝ) + γ * (n : ℝ) / 4 / 3))))) < 1) :
    ∃ N : Fin k → Set (Set (Fin n)), LeftoverConcl 𝓜 𝓗rem R U S ε M N := by
  classical
  have hγ0 : 0 < γ := hm.hγ
  have hε0 : 0 < ε := hm.hε
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hD₀pos : 0 < kahnD₀ hK r hr := kahnD₀_pos hK r hr
  have hγD0 : 0 < γ ^ 2 * (D : ℝ) := lt_of_lt_of_le (by linarith) hkanthr
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have h2 : (D : ℝ) = 0 := le_antisymm hcon (Nat.cast_nonneg D)
    rw [h2, mul_zero] at hγD0
    exact lt_irrefl 0 hγD0
  have hD'0 : 0 < γ ^ 2 * (D : ℝ) / 20 := by
    have : 0 < γ ^ 2 := pow_pos hγ0 2
    positivity
  have hkahnD' : kahnD₀ hK r hr ≤ γ ^ 2 * (D : ℝ) / 20 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 20)]
    linarith
  -- ## The leftover hypergraph is linear and has maximum degree `γ²D/20`
  have hlinrem : Hypergraph.IsLinear 𝓗rem :=
    MultiHypergraph.edges_isLinear_of_subset hremsub hlin
  have hmaxrem : ((hypergraphMaxDegree 𝓗rem : ℕ) : ℝ) ≤ γ ^ 2 * (D : ℝ) / 20 := by
    have hmax : ∀ v : Fin n, hypergraphDegree 𝓗rem v ≤ Nat.floor (γ ^ 2 * (D : ℝ) / 20) := by
      intro v
      have h := hremdeg v
      rw [hdeg_eq_hypergraphDegree] at h
      exact Nat.le_floor h
    have hsup : hypergraphMaxDegree 𝓗rem ≤ Nat.floor (γ ^ 2 * (D : ℝ) / 20) := by
      rw [hypergraphMaxDegree]
      exact Finset.sup_le fun v _ => hmax v
    calc ((hypergraphMaxDegree 𝓗rem : ℕ) : ℝ)
        ≤ ((Nat.floor (γ ^ 2 * (D : ℝ) / 20) : ℕ) : ℝ) := by exact_mod_cast hsup
      _ ≤ γ ^ 2 * (D : ℝ) / 20 := Nat.floor_le hD'0.le
  -- ## Partition of the colour set
  obtain ⟨f, hf⟩ := Commons.Combinatorics.Partition.exists_colouring_parts_ge (ι := Fin k)
    (leftoverT γ) (leftoverM γ D) (leftoverT_one_le γ) (by simpa using hTm)
  set P : Fin (leftoverT γ) → Finset (Fin k) := fun j => Finset.univ.filter (fun c => f c = j)
    with hP
  have hPmem : ∀ (j : Fin (leftoverT γ)) (c : Fin k), c ∈ P j ↔ f c = j := by
    intro j c
    simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and]
  -- ## Kahn's theorem for each part
  have hpart : ∀ j : Fin (leftoverT γ),
      ∃ ψ : 𝓗rem.Coloring (Fin k),
        (∀ e : 𝓗rem, ψ.labels e ∈ P j) ∧
        (∀ e : 𝓗rem, ψ.labels e ∉ (P j).filter
          (fun c => ((e : Set (Fin n)) ∩ famVert (M c)).Nonempty)) := by
    intro j
    refine exists_list_colouring_in_part (ι := Fin k) (r := r)
      (D₀ := kahnD₀ hK r hr) (kahnD₀_pos hK r hr) (kahnD₀_body hK r hr)
      (𝓖 := 𝓗rem) (P := P j) (D' := γ ^ 2 * (D : ℝ) / 20)
      hlinrem hmaxrem ?_ ?_ hkahnD' _ (fun e => Finset.filter_subset _ _) ?_
    · intro e
      exact_mod_cast hremsize (e : Set (Fin n)) e.2
    · have h1 : (3 / 2) * (γ ^ 2 * (D : ℝ) / 20) ≤ γ ^ 2 * (D : ℝ) / 10 := by
        nlinarith [hγD0.le]
      have h2 : γ ^ 2 * (D : ℝ) / 10 ≤ (leftoverM γ D : ℝ) := Nat.le_ceil _
      have h3 : (leftoverM γ D : ℝ) ≤ ((P j).card : ℝ) := by exact_mod_cast hf j
      linarith
    · intro e
      have hsub : (P j).filter (fun c => ((e : Set (Fin n)) ∩ famVert (M c)).Nonempty) ⊆
          Finset.univ.filter (fun c : Fin k => ((e : Set (Fin n)) ∩ famVert (M c)).Nonempty) := by
        intro c hc
        rw [Finset.mem_filter] at hc ⊢
        exact ⟨Finset.mem_univ _, hc.2⟩
      have hc1 : (((P j).filter (fun c => ((e : Set (Fin n)) ∩ famVert (M c)).Nonempty)).card : ℝ) ≤
          (({i : Fin k | ((e : Set (Fin n)) ∩ famVert (M i)).Nonempty} : Set (Fin k)).ncard : ℝ) := by
        have h := Finset.card_le_card hsub
        rw [ncard_setOf_eq_card_filter (fun i : Fin k => ((e : Set (Fin n)) ∩ famVert (M i)).Nonempty)]
        exact_mod_cast h
      have hc2 := hremlist (e : Set (Fin n)) e.2
      have hc3 : γ ^ 2 * (D : ℝ) / 100 ≤ (γ ^ 2 * (D : ℝ) / 20) / 4 := by
        nlinarith [hγD0.le]
      linarith
  choose ψ hψP hψL using hpart
  have hPdisj : ∀ j j' : Fin (leftoverT γ), j ≠ j' → Disjoint (P j) (P j') := by
    intro j j' hne
    rw [Finset.disjoint_left]
    intro c hc hc'
    exact hne ((hPmem j c).mp hc ▸ (hPmem j' c).mp hc')
  -- ## The colour classes of `𝓗_rem` are small
  have hW : ∀ (j : Fin (leftoverT γ)) (c : Fin k), c ∈ P j →
      (Finset.univ.filter (fun e : 𝓗rem => (ψ j).labels e = c)).sum
        (fun e => (edgeSize (e : Set (Fin n)) : ℝ)) ≤ (n : ℝ) := by
    intro j c hc
    set S : Finset (Set (Fin n)) :=
      (Finset.univ.filter (fun e : 𝓗rem => (ψ j).labels e = c)).image Subtype.val with hS
    have hSsum : (Finset.univ.filter (fun e : 𝓗rem => (ψ j).labels e = c)).sum
          (fun e => (edgeSize (e : Set (Fin n)) : ℝ)) = ∑ e ∈ S, (edgeSize e : ℝ) := by
      rw [hS]
      exact (Finset.sum_image (f := fun e : Set (Fin n) => (edgeSize e : ℝ))
        (g := Subtype.val) (fun a _ b _ hab => Subtype.ext hab)).symm
    have hSdisj : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint e f := by
      intro e he f hf hef
      rw [hS, Finset.mem_image] at he hf
      obtain ⟨e', he', rfl⟩ := he
      obtain ⟨f', hf', rfl⟩ := hf
      rw [Finset.mem_filter] at he' hf'
      refine Set.disjoint_left.mpr fun x hx hxf => ?_
      exact ((ψ j).isColoring e' f' (fun h => hef (by rw [h])) ⟨x, hx, hxf⟩)
        (he'.2.trans hf'.2.symm)
    rw [hSsum]
    exact_mod_cast sum_edgeSize_le_of_pairwise_disjoint hSdisj
  -- ## Merging the `t` colourings
  obtain ⟨pick, hpick⟩ := exists_merged_colouring (𝓖 := 𝓗rem) (ι := Fin k) (t := leftoverT γ)
    (leftoverT_two_le γ) ψ P hψP hPdisj (C := (r : ℝ)) (W := (n : ℝ)) (τ := γ * (n : ℝ) / 4)
    (Nat.cast_nonneg r) (fun e => by exact_mod_cast hremsize (e : Set (Fin n)) e.2)
    (Nat.cast_nonneg n) (by positivity) hW (by simpa using hcher)
  -- ## The colour classes of the merged colouring
  set clsF : Fin k → Finset (Set (Fin n)) := fun c =>
    (Finset.univ.filter (fun e : 𝓗rem => (ψ (pick e)).labels e = c)).image Subtype.val
    with hclsF
  set cls : Fin k → Set (Set (Fin n)) := fun c => (clsF c : Set (Set (Fin n))) with hcls
  have hclsF_mem_iff : ∀ (c : Fin k) (e : Set (Fin n)),
      e ∈ clsF c ↔ ∃ e' : 𝓗rem, (e' : Set (Fin n)) = e ∧ (ψ (pick e')).labels e' = c := by
    intro c e
    rw [hclsF, Finset.mem_image]
    constructor
    · rintro ⟨e', he', heq⟩
      rw [Finset.mem_filter] at he'
      exact ⟨e', heq, he'.2⟩
    · rintro ⟨e', heq, hlab⟩
      exact ⟨e', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlab⟩, heq⟩
  have hcls_mem_iff : ∀ (c : Fin k) (e : Set (Fin n)),
      e ∈ cls c ↔ ∃ e' : 𝓗rem, (e' : Set (Fin n)) = e ∧ (ψ (pick e')).labels e' = c := by
    intro c e
    rw [hcls]
    exact hclsF_mem_iff c e
  have hmem_cls_sub : ∀ (c : Fin k) {e : Set (Fin n)}, e ∈ cls c → e ∈ 𝓗rem := by
    intro c e he
    rw [hcls_mem_iff] at he
    obtain ⟨e', heq, -⟩ := he
    rw [← heq]
    exact e'.2
  have hcls_label : ∀ (e : Set (Fin n)) (he : e ∈ 𝓗rem),
      e ∈ cls ((ψ (pick ⟨e, he⟩)).labels ⟨e, he⟩) := by
    intro e he
    rw [hcls_mem_iff]
    exact ⟨⟨e, he⟩, rfl, rfl⟩
  have hcls_pick_eq : ∀ (c : Fin k) (e' e'' : 𝓗rem),
      (ψ (pick e')).labels e' = c → (ψ (pick e'')).labels e'' = c → pick e' = pick e'' := by
    intro c e' e'' h1 h2
    have hmem1 : c ∈ P (pick e') := by rw [← h1]; exact hψP (pick e') e'
    have hmem2 : c ∈ P (pick e'') := by rw [← h2]; exact hψP (pick e'') e''
    by_contra hne
    exact (Finset.disjoint_left.mp (hPdisj (pick e') (pick e'') hne) hmem1) hmem2
  have hcls_disj : ∀ c, ∀ e ∈ cls c, ∀ f ∈ cls c, e ≠ f → Disjoint e f := by
    intro c e he f hf hef
    rw [hcls_mem_iff] at he hf
    obtain ⟨e', heq, h1⟩ := he
    obtain ⟨f', hfq, h2⟩ := hf
    have hpe : pick e' = pick f' := hcls_pick_eq c e' f' h1 h2
    have hne : e' ≠ f' := fun h => hef (heq.symm.trans (by rw [h]) |>.trans hfq)
    rw [← heq, ← hfq, Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hcon
    rw [hpe] at h1
    exact (ψ (pick f')).isColoring e' f' hne hcon (h1.trans h2.symm)
  have hcls_disj_M : ∀ (c : Fin k) (f : Set (Fin n)), f ∈ cls c → Disjoint f (famVert (M c)) := by
    intro c f hf
    rw [hcls_mem_iff] at hf
    obtain ⟨e', heq, hlab⟩ := hf
    rw [← heq]
    have hnot : ¬ ((e' : Set (Fin n)) ∩ famVert (M ((ψ (pick e')).labels e'))).Nonempty := by
      intro hcon
      have h1 := hψL (pick e') e'
      refine h1 ?_
      rw [Finset.mem_filter]
      exact ⟨hψP (pick e') e', hcon⟩
    rw [hlab] at hnot
    exact Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hnot)
  have hcls_card : ∀ c : Fin k,
      (∑ e ∈ clsF c, (edgeSize e : ℝ)) ≤ (n : ℝ) / (leftoverT γ : ℝ) + γ * (n : ℝ) / 4 := by
    intro c
    have hsum : (Finset.univ.filter (fun e : 𝓗rem => (ψ (pick e)).labels e = c)).sum
        (fun e => (edgeSize (e : Set (Fin n)) : ℝ)) = ∑ e ∈ clsF c, (edgeSize e : ℝ) := by
      rw [hclsF]
      exact (Finset.sum_image (f := fun e : Set (Fin n) => (edgeSize e : ℝ))
        (g := Subtype.val) (fun a _ b _ hab => Subtype.ext hab)).symm
    rw [← hsum]
    exact hpick c
  have hcls_ncard : ∀ c : Fin k, (famVert (cls c)).ncard ≤ ∑ e ∈ clsF c, edgeSize e := by
    intro c
    rw [hcls]
    exact ncard_famVert_finset_le
  -- ## The inputs of the absorption step
  have hfamVert_union : ∀ A B : Set (Set (Fin n)), famVert (A ∪ B) = famVert A ∪ famVert B := by
    intro A B
    ext v
    simp only [famVert, Set.mem_sUnion, Set.mem_union]
    constructor
    · rintro ⟨s, hs | hs, hv⟩
      · exact Or.inl ⟨s, hs, hv⟩
      · exact Or.inr ⟨s, hs, hv⟩
    · rintro (⟨s, hs, hv⟩ | ⟨s, hs, hv⟩)
      · exact ⟨s, Or.inl hs, hv⟩
      · exact ⟨s, Or.inr hs, hv⟩
  have hns : ∀ i, ∀ e ∈ M i ∪ cls i, 2 ≤ e.ncard := by
    intro i e he
    rcases he with he | he
    · exact hMns i e he
    · exact hremns e (hmem_cls_sub i he)
  have hMcls_sub : ∀ i, M i ∪ cls i ⊆ 𝓜.edgeSet := by
    intro i e he
    rcases he with he | he
    · exact (hMmat i).1 he
    · exact MultiHypergraph.edges_subset_edgeSet 𝓜 (hremsub (hmem_cls_sub i he))
  have hMcls_mat : ∀ i, MultiHypergraph.IsMatching 𝓜 (M i ∪ cls i) := by
    intro i
    refine ⟨hMcls_sub i, ?_⟩
    intro e he f hf hef
    rcases he with he | he <;> rcases hf with hf | hf
    · exact (hMmat i).2 he hf hef
    · have hdis := hcls_disj_M i f hf
      rw [Set.disjoint_iff_inter_eq_empty] at hdis
      refine Set.disjoint_left.mpr fun x hxe hxf => ?_
      have hx : x ∈ famVert (M i) := Set.subset_sUnion_of_mem he hxe
      have h2 : x ∈ f ∩ famVert (M i) := ⟨hxf, hx⟩
      rw [hdis] at h2
      exact h2
    · have hdis := hcls_disj_M i e he
      rw [Set.disjoint_iff_inter_eq_empty] at hdis
      refine Set.disjoint_left.mpr fun x hxe hxf => ?_
      have hx : x ∈ famVert (M i) := Set.subset_sUnion_of_mem hf hxf
      have h2 : x ∈ e ∩ famVert (M i) := ⟨hxe, hx⟩
      rw [hdis] at h2
      exact h2
    · exact hcls_disj i e he f hf hef
  have hMcls_disj : ∀ i j, i ≠ j → EdgeDisjointFam (M i ∪ cls i) (M j ∪ cls j) := by
    intro i j hij
    rw [EdgeDisjointFam, Set.disjoint_left]
    rintro e ⟨he, -⟩ ⟨he', -⟩
    rcases he with he | he <;> rcases he' with he' | he'
    · exact Set.disjoint_left.mp (hMdisj i j hij) he he'
    · exact hremM e (hmem_cls_sub j he') i he
    · exact hremM e (hmem_cls_sub i he) j he'
    · rw [hcls_mem_iff] at he he'
      obtain ⟨e₁, heq₁, hlab₁⟩ := he
      obtain ⟨e₂, heq₂, hlab₂⟩ := he'
      have h12 : e₁ = e₂ := Subtype.ext (heq₁.trans heq₂.symm)
      rw [h12] at hlab₁
      exact hij (hlab₁.symm.trans hlab₂)
  have havoid : ∀ i, ∀ e ∈ M i ∪ cls i, e ∉ R := by
    intro i e he
    rcases he with he | he
    · exact hMR i e he
    · exact hremR e (hmem_cls_sub i he)
  have hsize : ∀ i, ((famVert (M i ∪ cls i)).ncard : ℝ) ≤ γ * (n : ℝ) := by
    intro i
    rw [hfamVert_union]
    have h2 : ((famVert (M i) ∪ famVert (cls i)).ncard : ℝ) ≤
        ((famVert (M i)).ncard : ℝ) + ((famVert (cls i)).ncard : ℝ) := by
      exact_mod_cast Set.ncard_union_le (famVert (M i)) (famVert (cls i))
    have h3 : ((famVert (cls i)).ncard : ℝ) ≤
        (n : ℝ) / (leftoverT γ : ℝ) + γ * (n : ℝ) / 4 :=
      le_trans (by exact_mod_cast hcls_ncard i) (hcls_card i)
    have h4 := hMsize i
    have h5 := div_leftoverT_add_le hγ0 n
    linarith
  have hk : (k : ℝ) ≤ γ * (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hDn (le_of_lt hγ0)
    linarith
  have hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓜.edgeSet U) u : ℝ) := by
    intro u hu
    have h1 : degAt (incidentTwo 𝓜.edgeSet U) u = degAt (MultiHypergraph.pow2 𝓜) u := by
      rw [← MultiHypergraph.incidentTwo_pow2 𝓜 U]
      rw [degAt_incidentTwo_eq (𝓗 := MultiHypergraph.pow2 𝓜) hu]
      rw [MultiHypergraph.pow2_eq_edgeSet_pow2, Hypergraph.pow2_idem]
    rw [h1]
    have h2 : u ∈ VplusTwo (MultiHypergraph.pow2 𝓜) (1 - ε) := by rw [← hU]; exact hu
    exact h2
  have hRpow' : R ⊆ Hypergraph.pow2 𝓜.edgeSet := by
    rw [← MultiHypergraph.pow2_eq_edgeSet_pow2]
    exact hRpow
  have hRabs' : IsAbsorber (incidentTwo 𝓜.edgeSet U) R
      ({(Set.univ : Set (Fin n)), U} : Set (Set (Fin n))) ρ (10 * γ) ξ := by
    rw [← MultiHypergraph.incidentTwo_pow2 𝓜 U]
    exact hRabs
  -- ## The absorption
  obtain ⟨N, hNsub, hNadd, hNmat, hNdisj, hNperf, hNnear⟩ :=
    leftover_absorption (𝓜 := 𝓜) (R := R) (U := U) (S := S) (ρ := ρ) (γ := γ) (ξ := ξ)
      (ε := ε) (k := k) (M := M) (cls := cls) hm hn4 hUdeg hRpow' hRabs'
      hns hMcls_mat hMcls_disj havoid hsize hSsub hSbig hk
  refine ⟨N, ?_, hNmat, ?_, hNdisj, ?_, hNperf, hNnear⟩
  · intro i e he
    exact hNsub i (Or.inl he)
  · intro i e he hne
    by_cases hcl : e ∈ cls i
    · exact Or.inl (hmem_cls_sub i hcl)
    · exact Or.inr (hNadd i e he (fun h => h.elim hne hcl))
  · intro e he
    exact ⟨_, hNsub _ (Or.inr (hcls_label e he))⟩


end

end ErdosFaberLovaszConjecture
