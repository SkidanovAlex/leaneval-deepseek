import Submission.EFL.Absorption

/-!
# Absorption of pseudorandom matchings (§7.1 of the paper)

This module formalises the first absorption lemma of §7 of the
Erdős–Faber–Lovász paper (Lemma `crossing-absorption-lemma`), which says that
a family of edge-disjoint matchings, each of which is `(γ,κ)`-pseudorandom
with respect to the `R`-neighbourhoods of the vertices, can be extended (using
edges of the absorber `R`) so that every matching covers all of `U`, provided
`|U| ≤ n/100`.

The proof is the paper's:
* for each matching `N` we must cover `A = U \ V(N)`;
* every `u ∈ A` has `d_{R\used}(u) ≥ γ(ρ((1-ε) - 1/100)n - 10γn) - 2κn ≥ 2ρ|A|`;
* if `|A| ≥ ξn/ρ` we apply the crossing matching proposition
  (`exists_matching_covering_of_upperRegular`), otherwise the greedy/Hall
  argument (`exists_matching_covering_of_greedy`) applies.

We also collect here the set/finset bridge `sfin` and the numeric margins
`CrossingMargins` used throughout §7.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-! ## Sets of vertices as finsets -/

/-- The finset of the vertices of a set of vertices of `Fin n`. -/
def sfin (S : Set (Fin n)) : Finset (Fin n) := Finset.univ.filter (fun x => x ∈ S)

theorem mem_sfin {S : Set (Fin n)} {x : Fin n} : x ∈ sfin S ↔ x ∈ S := by
  simp [sfin]

theorem card_sfin (S : Set (Fin n)) : (sfin S).card = S.ncard := by
  rw [Set.ncard_eq_toFinset_card' S]
  congr 1
  ext x
  simp [sfin, Set.mem_toFinset]

theorem sfin_mono {S T : Set (Fin n)} (h : S ⊆ T) : sfin S ⊆ sfin T := by
  intro x hx
  rw [mem_sfin] at hx ⊢
  exact h hx

theorem sfin_compl (S : Set (Fin n)) : sfin Sᶜ = Finset.univ \ sfin S := by
  ext x
  simp [sfin, Set.mem_compl_iff]

theorem sfin_union (S T : Set (Fin n)) : sfin (S ∪ T) = sfin S ∪ sfin T := by
  ext x
  rw [mem_sfin, Finset.mem_union, mem_sfin, mem_sfin, Set.mem_union]

theorem sfin_card_le (S : Set (Fin n)) : (sfin S).card ≤ n := by
  rw [card_sfin]
  exact le_trans (Set.ncard_le_ncard (Set.subset_univ S) (Set.toFinite _)) (by simp)

/-- The number of neighbours of `v` outside the set `S` equals the cardinality
of the corresponding finset difference. -/
theorem ncard_nbrs_sdiff {R : Hypergraph (Fin n)} (v : Fin n) (S : Set (Fin n)) :
    (nbrs R v \ S).ncard = (sfin (nbrs R v) \ sfin S).card := by
  rw [← card_sfin (nbrs R v \ S)]
  congr 1
  ext x
  rw [mem_sfin, Finset.mem_sdiff, mem_sfin, mem_sfin, Set.mem_sdiff]

/-! ## Neighbourhoods of 2-edge families -/

theorem mem_nbrs {R : Hypergraph (Fin n)} {v w : Fin n} :
    w ∈ nbrs R v ↔ ({v, w} : Set (Fin n)) ∈ R := Iff.rfl

theorem nbrs_comm {R : Hypergraph (Fin n)} {v w : Fin n} :
    w ∈ nbrs R v ↔ v ∈ nbrs R w := by
  rw [mem_nbrs, mem_nbrs, Set.pair_comm]

theorem nbrs_mono {R R' : Hypergraph (Fin n)} (h : R ⊆ R') (v : Fin n) :
    nbrs R v ⊆ nbrs R' v := fun _ hw => h hw

theorem nbrs_union {R R' : Hypergraph (Fin n)} (v : Fin n) :
    nbrs (R ∪ R') v = nbrs R v ∪ nbrs R' v := by
  ext w
  simp only [nbrs, Set.mem_ofPred_eq, Set.mem_union]

theorem nbrs_sdiff {R R' : Hypergraph (Fin n)} (v : Fin n) :
    nbrs (R \ R') v = nbrs R v \ nbrs R' v := by
  ext w
  simp only [nbrs, Set.mem_ofPred_eq, Set.mem_sdiff]

/-- For `u ∈ U`, the neighbourhood of `u` in `G' = 𝓗^{(2)}[U]` is the whole
2-neighbourhood of `u` in `𝓗`. -/
theorem nbrs_incidentTwo_of_mem {𝓗 : Hypergraph (Fin n)} {U : Set (Fin n)} {u : Fin n}
    (hu : u ∈ U) : nbrs (incidentTwo 𝓗 U) u = nbrs 𝓗.pow2 u := by
  ext w
  rw [mem_nbrs, mem_incidentTwo, mem_nbrs]
  exact ⟨fun h => h.1, fun h => ⟨h, u, by simp, hu⟩⟩

theorem incidentTwo_subset_self {𝓗 : Hypergraph (Fin n)} {U : Set (Fin n)} :
    incidentTwo 𝓗 U ⊆ 𝓗 := fun e he => he.1.1

/-! ## Numeric margins of §7 -/

/-- The numeric margin hierarchy of §7, in the concrete form used by the
crossing absorption lemma: `0 < 1/n ≪ ξ ≪ κ ≪ γ ≪ ρ,ε ≪ 1`, together with
`ξ ≪ γρ²` (needed for the greedy case). -/
structure CrossingMargins (n : ℕ) (ρ ε γ κ ξ : ℝ) : Prop where
  hn : 1 ≤ n
  hρ : 0 < ρ
  hε : 0 < ε
  hγ : 0 < γ
  hκ : 0 < κ
  hξ : 0 < ξ
  hε2 : ε ≤ 1 / 2
  hρ2 : ρ ≤ 1
  hκγ : 1000 * κ ≤ γ * ρ
  hγρ : 1000 * γ ≤ ρ
  hξρ : ξ ≤ ρ
  hξγρ : 1000 * ξ ≤ γ * ρ ^ 2

/-- The main degree estimate of the crossing absorption lemma. -/
theorem crossing_arith_main {ρ ε γ κ ξ : ℝ} {n : ℕ} (hm : CrossingMargins n ρ ε γ κ ξ) :
    2 * ρ * (γ * (n : ℝ) / 100 + κ * (n : ℝ))
      ≤ γ * (ρ * ((1 - ε) * (n : ℝ) - (n : ℝ) / 100) - 10 * γ * (n : ℝ))
        - 2 * κ * (n : ℝ) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hρ0 : (0 : ℝ) ≤ ρ := le_of_lt hm.hρ
  have hγ0 : (0 : ℝ) ≤ γ := le_of_lt hm.hγ
  have hN : (0 : ℝ) ≤ γ * ρ * (n : ℝ) := by positivity
  -- the four monomial bounds
  have hA : 10 * γ * γ * (n : ℝ) ≤ γ * ρ * (n : ℝ) / 100 := by
    have h : 1000 * γ * (n : ℝ) ≤ ρ * (n : ℝ) := by
      have := mul_le_mul_of_nonneg_right hm.hγρ hn
      linarith [this]
    nlinarith [mul_le_mul_of_nonneg_left h hγ0, hN]
  have hB : 2 * κ * (n : ℝ) ≤ γ * ρ * (n : ℝ) / 500 := by
    have h := mul_le_mul_of_nonneg_right hm.hκγ hn
    nlinarith [h]
  have hC : 2 * ρ * κ * (n : ℝ) ≤ γ * ρ * (n : ℝ) / 500 := by
    have h := mul_le_mul_of_nonneg_right hm.hκγ (mul_nonneg hρ0 hn)
    nlinarith [h, hm.hρ2, hN, mul_nonneg hn hγ0]
  have hD : ε * (γ * ρ * (n : ℝ)) ≤ γ * ρ * (n : ℝ) / 2 := by
    have h : ε * (n : ℝ) ≤ (n : ℝ) / 2 := by
      have := mul_le_mul_of_nonneg_right hm.hε2 hn
      linarith [this]
    nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg hρ0 hγ0)]
  nlinarith [hA, hB, hC, hD, hN, mul_nonneg hn hρ0, mul_nonneg hn hγ0]

/-- The greedy-case estimate of the crossing absorption lemma. -/
theorem crossing_arith_greedy {ρ ε γ κ ξ : ℝ} {n : ℕ} (hm : CrossingMargins n ρ ε γ κ ξ) :
    ξ * (n : ℝ) / ρ
      < γ * (ρ * ((1 - ε) * (n : ℝ) - (n : ℝ) / 100) - 10 * γ * (n : ℝ))
        - 2 * κ * (n : ℝ) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hρ0 : (0 : ℝ) ≤ ρ := le_of_lt hm.hρ
  have hγ0 : (0 : ℝ) ≤ γ := le_of_lt hm.hγ
  have hN : (0 : ℝ) ≤ γ * ρ ^ 2 * (n : ℝ) := by positivity
  rw [div_lt_iff₀ hm.hρ]
  have hξn : 1000 * ξ * (n : ℝ) ≤ γ * ρ ^ 2 * (n : ℝ) := by
    have := mul_le_mul_of_nonneg_right hm.hξγρ hn
    linarith [this]
  have hA : 10 * γ * γ * ρ * (n : ℝ) ≤ γ * ρ ^ 2 * (n : ℝ) / 100 := by
    have := mul_le_mul_of_nonneg_right hm.hγρ (by positivity : (0:ℝ) ≤ γ * ρ * (n : ℝ))
    nlinarith [this, hN]
  have hB : 2 * ρ * κ * (n : ℝ) ≤ γ * ρ ^ 2 * (n : ℝ) / 500 := by
    have := mul_le_mul_of_nonneg_right hm.hκγ (by positivity : (0:ℝ) ≤ ρ * (n : ℝ))
    nlinarith [this, hN]
  have hD : ε * (γ * ρ ^ 2 * (n : ℝ)) ≤ γ * ρ ^ 2 * (n : ℝ) / 2 := by
    have h : ε * (n : ℝ) ≤ (n : ℝ) / 2 := by
      have := mul_le_mul_of_nonneg_right hm.hε2 hn
      linarith [this]
    nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ γ * ρ ^ 2)]
  have hmain : γ * ρ ^ 2 * (n : ℝ) * (1 / 2 - 1 / 100 - 1 / 100 - 1 / 500)
      ≤ (γ * (ρ * ((1 - ε) * (n : ℝ) - (n : ℝ) / 100) - 10 * γ * (n : ℝ))
          - 2 * κ * (n : ℝ)) * ρ := by
    ring_nf
    nlinarith [hA, hB, hD, hN, hm.hε2]
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hm.hn
  have hγρn2 : (0 : ℝ) < γ * ρ ^ 2 * (n : ℝ) :=
    mul_pos (mul_pos hm.hγ (pow_pos hm.hρ 2)) hpos
  have hxi : ξ * (n : ℝ) < γ * ρ ^ 2 * (n : ℝ) * (1 / 2 - 1 / 100 - 1 / 100 - 1 / 500) := by
    nlinarith [hξn, hN, hγρn2]
  linarith [hmain, hxi]

/-! ## Counting neighbours through a vertex -/

/-- The vertices adjacent to `v` in a family of 2-edges inject into the edges
of the family through `v`. -/
theorem natCard_subtype_mem_eq_ncard (S : Set (Fin n)) :
    Nat.card {w : Fin n // w ∈ S} = S.ncard := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← card_sfin S]
  rfl

theorem ncard_nbrs_le_ncard_edgesThrough (G : Hypergraph (Fin n)) (v : Fin n) :
    (nbrs G v).ncard ≤ Nat.card {e : G // v ∈ (e : Set (Fin n))} := by
  classical
  rw [← natCard_subtype_mem_eq_ncard (nbrs G v)]
  refine Nat.card_le_card_of_injective
    (f := fun w : {w : Fin n // w ∈ nbrs G v} =>
      (⟨⟨{v, w.1}, w.2⟩, by simp⟩ : {e : G // v ∈ (e : Set (Fin n))})) ?_
  intro w w' heq
  have h1 : ({v, w.1} : Set (Fin n)) = {v, w'.1} :=
    congrArg (fun x : {e : G // v ∈ (e : Set (Fin n))} => (x.1 : Set (Fin n))) heq
  rcases (Set.pair_eq_pair_iff.mp h1) with ⟨_, h⟩ | ⟨h1', h2'⟩
  · exact Subtype.ext h
  · exact Subtype.ext (h2'.trans h1')

/-! ## The union of a family of families of edges -/

/-- A family of edges regarded as a hypergraph on `Fin n`. -/
def famOf {𝓗 : Hypergraph (Fin n)} (M : Set 𝓗) : Hypergraph (Fin n) :=
  {e | ∃ e' ∈ M, (e' : Set (Fin n)) = e}

theorem mem_famOf {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {e : Set (Fin n)} :
    e ∈ famOf M ↔ ∃ e' ∈ M, (e' : Set (Fin n)) = e := Iff.rfl

theorem famOf_mono {𝓗 : Hypergraph (Fin n)} {M M' : Set 𝓗} (h : M ⊆ M') :
    famOf M ⊆ famOf M' := by
  rintro e ⟨e', he', rfl⟩
  exact ⟨e', h he', rfl⟩

theorem mem_famOf_iff {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {G : Hypergraph (Fin n)} :
    famOf M ⊆ G ↔ ∀ e ∈ M, (e : Set (Fin n)) ∈ G := by
  constructor
  · intro h e he
    exact h ⟨e, he, rfl⟩
  · rintro h e ⟨e', he', rfl⟩
    exact h e' he'

theorem famOf_subset_self {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} : ∀ e ∈ M, (e : Set (Fin n)) ∈ famOf M :=
  fun e he => ⟨e, he, rfl⟩

/-- The union of a `Fin k`-indexed family of families of edges. -/
def famUnionIdx {𝓗 : Hypergraph (Fin n)} {k : ℕ} (M : Fin k → Set 𝓗) : Hypergraph (Fin n) :=
  {e | ∃ i : Fin k, e ∈ famOf (M i)}

theorem mem_famUnionIdx {𝓗 : Hypergraph (Fin n)} {k : ℕ} {M : Fin k → Set 𝓗}
    {e : Set (Fin n)} : e ∈ famUnionIdx M ↔ ∃ i : Fin k, e ∈ famOf (M i) := Iff.rfl

theorem famUnionIdx_snoc {𝓗 : Hypergraph (Fin n)} {k : ℕ} (M : Fin k → Set 𝓗) (X : Set 𝓗) :
    famUnionIdx (Fin.snoc M X) = famUnionIdx M ∪ famOf X := by
  ext e
  rw [mem_famUnionIdx, Set.mem_union, mem_famUnionIdx, mem_famOf]
  constructor
  · rintro ⟨i, hi⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Or.inl ⟨j, by rwa [Fin.snoc_castSucc] at hi⟩
    · exact Or.inr (by rwa [Fin.snoc_last] at hi)
  · rintro (⟨i, hi⟩ | hX)
    · exact ⟨i.castSucc, by rwa [Fin.snoc_castSucc]⟩
    · exact ⟨Fin.last k, by rwa [Fin.snoc_last]⟩

/-- The union of `k` matchings has at most `k` edges through any vertex. -/
theorem ncard_nbrs_famUnionIdx_le {𝓗 : Hypergraph (Fin n)} {k : ℕ} {M : Fin k → Set 𝓗}
    (hm : ∀ i, IsMatching 𝓗 (M i)) (v : Fin n) :
    (nbrs (famUnionIdx M) v).ncard ≤ k := by
  classical
  have hex : ∀ w : Fin n, w ∈ nbrs (famUnionIdx M) v →
      ∃ i : Fin k, ∃ e ∈ M i, (e : Set (Fin n)) = ({v, w} : Set (Fin n)) := by
    intro w hw
    rw [mem_nbrs, mem_famUnionIdx] at hw
    obtain ⟨i, e', he', heq⟩ := hw
    exact ⟨i, e', he', heq⟩
  let ch : {w : Fin n // w ∈ nbrs (famUnionIdx M) v} → Fin k :=
    fun w => Classical.choose (hex w.1 w.2)
  have hch : ∀ w : {w : Fin n // w ∈ nbrs (famUnionIdx M) v},
      ∃ e ∈ M (ch w), (e : Set (Fin n)) = ({v, w.1} : Set (Fin n)) :=
    fun w => Classical.choose_spec (hex w.1 w.2)
  have hinj : Function.Injective ch := by
    intro a b hab
    obtain ⟨e, he, heq⟩ := hch a
    obtain ⟨e', he', heq'⟩ := hch b
    rw [hab] at he
    have hv : (v : Fin n) ∈ (e : Set (Fin n)) := by rw [heq]; simp
    have hv' : (v : Fin n) ∈ (e' : Set (Fin n)) := by rw [heq']; simp
    have hee : e = e' := by
      by_contra hne
      exact (Set.disjoint_left.mp (hm (ch b) he he' hne)) hv hv'
    have hsets : ({v, a.1} : Set (Fin n)) = {v, b.1} := by rw [← heq, ← heq', hee]
    rcases (Set.pair_eq_pair_iff.mp hsets) with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact Subtype.ext h
    · exact Subtype.ext (h2.trans h1)
  have hle : Nat.card {w : Fin n // w ∈ nbrs (famUnionIdx M) v} ≤ Nat.card (Fin k) :=
    Nat.card_le_card_of_injective ch hinj
  rwa [natCard_subtype_mem_eq_ncard, Nat.card_eq_fintype_card, Fintype.card_fin] at hle

/-! ## The one-step degree estimate of the crossing absorption lemma -/

/-- For finite sets, `|s| - |t| ≤ |s \ t|` (in `ℝ`, to avoid truncated
subtraction). -/
theorem ncard_sdiff_ge (s t : Set (Fin n)) :
    (s.ncard : ℝ) - (t.ncard : ℝ) ≤ ((s \ t).ncard : ℝ) := by
  have hsub : s ⊆ (s \ t) ∪ t := fun x hx => by
    by_cases h : x ∈ t
    · exact Or.inr h
    · exact Or.inl ⟨hx, h⟩
  have h1 : s.ncard ≤ ((s \ t) ∪ t).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ((s \ t) ∪ t).ncard ≤ (s \ t).ncard + t.ncard := Set.ncard_union_le _ _
  have h3 : (s.ncard : ℝ) ≤ ((s \ t).ncard : ℝ) + (t.ncard : ℝ) := by
    exact_mod_cast le_trans h1 h2
  linarith

/-- The candidate absorbing neighbours of `u` in the crossing step: the
`R`-neighbours of `u` outside `U` and outside the vertices already used, that
are not already covered by the used edges. -/
def crossNbrs (R used : Hypergraph (Fin n)) (U VN : Set (Fin n)) (u : Fin n) : Set (Fin n) :=
  {w : Fin n | ({u, w} : Set (Fin n)) ∈ R ∧ ({u, w} : Set (Fin n)) ∉ used ∧
    w ∉ U ∧ w ∉ VN}

theorem crossNbrs_eq (R used : Hypergraph (Fin n)) (U VN : Set (Fin n)) (u : Fin n) :
    crossNbrs R used U VN u = (nbrs (R \ used) u \ U) \ VN := by
  ext w
  simp only [crossNbrs, nbrs, Set.mem_sdiff, Set.mem_ofPred_eq]
  tauto

theorem crossNbrs_mono_used {R used used' : Hypergraph (Fin n)} (h : used' ⊆ used)
    (U VN : Set (Fin n)) (u : Fin n) :
    crossNbrs R used U VN u ⊆ crossNbrs R used' U VN u := by
  rintro w ⟨h1, h2, h3, h4⟩
  exact ⟨h1, fun hc => h2 (h hc), h3, h4⟩

theorem crossNbrs_subset (R used : Hypergraph (Fin n)) (U VN : Set (Fin n)) (u : Fin n) :
    crossNbrs R used U VN u ⊆ (nbrs R u \ U) \ nbrs used u := by
  rintro w ⟨h1, h2, h3, -⟩
  exact ⟨⟨h1, h3⟩, h2⟩

theorem crossNbrs_used_subset (R used : Hypergraph (Fin n)) (U VN : Set (Fin n)) (u : Fin n) :
    crossNbrs R used U VN u ⊆ nbrs R u \ U := by
  rintro w ⟨h1, -, h3, -⟩
  exact ⟨h1, h3⟩

/-- The size of `A = U \ V(N)` under pseudorandomness: `|A| ≤ γ|U| + κn`. -/
theorem pseudo_U_card_le {𝓗 : Hypergraph (Fin n)} {R used : Hypergraph (Fin n)}
    {U S : Set (Fin n)} {N : Set 𝓗} {γ κ : ℝ} (hγ0 : 0 ≤ γ)
    (hpseudo : PseudoRandom N (absorberFam R U ∪ {U, S}) γ κ)
    (hUcard : (U.ncard : ℝ) ≤ (n : ℝ) / 100) :
    ((U \ matchVert N).ncard : ℝ) ≤ γ * (n : ℝ) / 100 + κ * (n : ℝ) := by
  have hmemU : U ∈ absorberFam R U ∪ {U, S} := by
    refine Set.mem_union_right _ ?_
    exact Set.mem_insert_iff.mpr (Or.inl rfl)
  have h := (abs_le.mp (hpseudo U hmemU)).2
  nlinarith [h, hUcard, hγ0]

/-- **The one-step degree estimate.**  Every vertex of `A = U \ V(N)` has at
least `γ(ρ((1-ε) - 1/100)n - 10γn) - 2κn` available absorbing neighbours. -/
theorem crossing_degree_chain {𝓗 : Hypergraph (Fin n)} {R used : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)} {N : Set 𝓗} {ρ ε γ κ ξ : ℝ}
    (hm : CrossingMargins n ρ ε γ κ ξ)
    (hUcard : (U.ncard : ℝ) ≤ (n : ℝ) / 100)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : IsAbsorber (incidentTwo 𝓗 U) R 𝓥 ρ (10 * γ) ξ) (hU𝓥 : U ∈ 𝓥)
    (hpseudo : PseudoRandom N (absorberFam R U ∪ {U, S}) γ κ)
    (hused : ∀ v : Fin n, ((nbrs used v).ncard : ℝ) ≤ κ * (n : ℝ))
    {u : Fin n} (hu : u ∈ U) :
    γ * (ρ * ((1 - ε) * (n : ℝ) - (n : ℝ) / 100) - 10 * γ * (n : ℝ)) - 2 * κ * (n : ℝ)
      ≤ ((crossNbrs R used U (matchVert N) u).ncard : ℝ) := by
  classical
  obtain ⟨hRsub, htyp, hup⟩ := habs
  have hγ0 : (0 : ℝ) ≤ γ := le_of_lt hm.hγ
  have hρ0 : (0 : ℝ) ≤ ρ := le_of_lt hm.hρ
  -- (1) typicality at `X = U`
  have htypu' := (htyp U hU𝓥 u).2
  have hcomp1 : (Uᶜ ∩ nbrs R u).ncard = (nbrs R u \ U).ncard := by
    congr 1
    ext w
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
    tauto
  have hcomp2 : (Uᶜ ∩ nbrs (incidentTwo 𝓗 U) u).ncard
      = (nbrs (incidentTwo 𝓗 U) u \ U).ncard := by
    congr 1
    ext w
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
    tauto
  rw [hcomp1, hcomp2] at htypu'
  have hNRU : ρ * ((nbrs (incidentTwo 𝓗 U) u \ U).ncard : ℝ) - 10 * γ * (n : ℝ)
      ≤ ((nbrs R u \ U).ncard : ℝ) := by
    have h := (abs_le.mp htypu').1
    linarith [h]
  -- (2) the degree of `u` inside `G'`
  have hnbrsG' : nbrs (incidentTwo 𝓗 U) u = nbrs 𝓗.pow2 u := nbrs_incidentTwo_of_mem hu
  have hdegU : (1 - ε) * (n : ℝ) ≤ ((nbrs 𝓗.pow2 u).ncard : ℝ) := by
    have h := hUdeg u hu
    simp only [degAt, hnbrsG'] at h
    exact h
  have hG'U : ρ * ((1 - ε) * (n : ℝ) - (n : ℝ) / 100) - 10 * γ * (n : ℝ)
      ≤ ((nbrs R u \ U).ncard : ℝ) := by
    have hsd := ncard_sdiff_ge (nbrs 𝓗.pow2 u) U
    have hG'le : (1 - ε) * (n : ℝ) - (n : ℝ) / 100
        ≤ ((nbrs (incidentTwo 𝓗 U) u \ U).ncard : ℝ) := by
      rw [hnbrsG']
      linarith [hsd, hdegU, hUcard]
    have hmul := mul_le_mul_of_nonneg_left hG'le hρ0
    linarith [hmul, hNRU]
  -- (3) pseudorandomness at `S = nbrs R u \ U`
  have hmem : nbrs R u \ U ∈ absorberFam R U ∪ {U, S} := by
    refine Set.mem_union_left _ ?_
    exact Or.inr ⟨u, rfl⟩
  have hpseudo' := hpseudo (nbrs R u \ U) hmem
  have hXeq : ((nbrs R u \ U) \ matchVert N) = (nbrs R u \ U) \ matchVert N := rfl
  have hX : γ * ((nbrs R u \ U).ncard : ℝ) - κ * (n : ℝ)
      ≤ (((nbrs R u \ U) \ matchVert N).ncard : ℝ) := by
    have h := (abs_le.mp hpseudo').1
    linarith [h]
  -- (4) removing the used edges
  have hY : (((nbrs R u \ U) \ matchVert N).ncard : ℝ) - κ * (n : ℝ)
      ≤ ((crossNbrs R used U (matchVert N) u).ncard : ℝ) := by
    have hsub : (nbrs R u \ U) \ matchVert N ⊆
        crossNbrs R used U (matchVert N) u ∪ nbrs used u := by
      rintro w ⟨⟨h1, h3⟩, h4⟩
      by_cases h2 : ({u, w} : Set (Fin n)) ∈ used
      · exact Or.inr h2
      · exact Or.inl ⟨h1, h2, h3, h4⟩
    have h1 : ((nbrs R u \ U) \ matchVert N).ncard
        ≤ (crossNbrs R used U (matchVert N) u ∪ nbrs used u).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : (crossNbrs R used U (matchVert N) u ∪ nbrs used u).ncard
        ≤ (crossNbrs R used U (matchVert N) u).ncard + (nbrs used u).ncard :=
      Set.ncard_union_le _ _
    have h3 : ((nbrs R u \ U) \ matchVert N).ncard
        ≤ (crossNbrs R used U (matchVert N) u).ncard + (nbrs used u).ncard := le_trans h1 h2
    have h4 : (((nbrs R u \ U) \ matchVert N).ncard : ℝ)
        ≤ ((crossNbrs R used U (matchVert N) u).ncard : ℝ) + (nbrs used u).ncard := by
      exact_mod_cast h3
    have h5 := hused u
    linarith [h4, h5]
  -- (5) assembly
  nlinarith [hG'U, hX, hY, hγ0, hρ0]

/-- The `2ρ|A|` form of the one-step degree estimate. -/
theorem crossing_degree {𝓗 : Hypergraph (Fin n)} {R used : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)} {N : Set 𝓗} {ρ ε γ κ ξ : ℝ}
    (hm : CrossingMargins n ρ ε γ κ ξ)
    (hUcard : (U.ncard : ℝ) ≤ (n : ℝ) / 100)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : IsAbsorber (incidentTwo 𝓗 U) R 𝓥 ρ (10 * γ) ξ) (hU𝓥 : U ∈ 𝓥)
    (hpseudo : PseudoRandom N (absorberFam R U ∪ {U, S}) γ κ)
    (hused : ∀ v : Fin n, ((nbrs used v).ncard : ℝ) ≤ κ * (n : ℝ))
    {u : Fin n} (hu : u ∈ U) :
    2 * ρ * ((U \ matchVert N).ncard : ℝ)
      ≤ ((crossNbrs R used U (matchVert N) u).ncard : ℝ) := by
  have h1 := crossing_degree_chain hm hUcard hUdeg habs hU𝓥 hpseudo hused hu
  have h2 := pseudo_U_card_le (𝓗 := 𝓗) (R := R) (used := used) (N := N) (S := S)
    (le_of_lt hm.hγ) hpseudo hUcard
  have h3 := crossing_arith_main hm
  have hρ0 : (0 : ℝ) ≤ ρ := le_of_lt hm.hρ
  nlinarith [h1, h2, h3, hρ0]

/-- The number of `crossNbrs` is at most the corresponding filtered count. -/
theorem crossNbrs_ncard_le_filter {R' used : Hypergraph (Fin n)} {U W : Set (Fin n)}
    {VN : Finset (Fin n)} {u : Fin n} {Af : Finset (Fin n)}
    (hAf : ∀ x : Fin n, x ∈ Af ↔ x ∈ U ∧ x ∉ W) (hVN : ∀ x : Fin n, x ∈ VN ↔ x ∈ W) :
    (crossNbrs R' used U W u).ncard ≤
      ((Finset.univ \ Af).filter
        (fun b => ({u, b} : Set (Fin n)) ∈ R' ∧ b ∉ VN)).card := by
  classical
  set T : Set (Fin n) := {b : Fin n | b ∉ Af ∧ ({u, b} : Set (Fin n)) ∈ R' ∧ b ∉ VN}
    with hT
  have hsub : crossNbrs R' used U W u ⊆ T := by
    rintro w ⟨h1, h2, h3, h4⟩
    refine ⟨?_, h1, ?_⟩
    · intro hw
      exact h3 ((hAf w).mp hw).1
    · intro hw
      exact h4 ((hVN w).mp hw)
  have hcard : (T).ncard = ((Finset.univ \ Af).filter
      (fun b => ({u, b} : Set (Fin n)) ∈ R' ∧ b ∉ VN)).card := by
    rw [← card_sfin T, hT]
    congr 1
    ext b
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, mem_sfin,
      Set.mem_ofPred_eq]
  calc (crossNbrs R' used U W u).ncard ≤ (T).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = _ := hcard

theorem edgeCount_mono {R R' : Hypergraph (Fin n)} (h : R ⊆ R') (S T : Finset (Fin n)) :
    edgeCount R S T ≤ edgeCount R' S T := by
  classical
  unfold edgeCount
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, h hp.2⟩

theorem edgeCount_le_card_mul (R : Hypergraph (Fin n)) (S T : Finset (Fin n)) :
    edgeCount R S T ≤ S.card * T.card := by
  classical
  unfold edgeCount
  calc ((S.product T).filter (fun p => ({p.1, p.2} : Set (Fin n)) ∈ R)).card
      ≤ (S.product T).card := Finset.card_filter_le _ _
    _ = S.card * T.card := by
        rw [show S.product T = S ×ˢ T from rfl, Finset.card_product]

/-- **The one-step crossing absorption.**  Given an absorber `R` and a family
`N` of matchings that is pseudorandom with respect to the `R`-neighbourhoods,
there is a matching `Nabs` of edges of `R` not meeting the already used edges
that covers all of `U \ V(N)`, and whose vertex set avoids `V(N)`.

Here `R' = R \ used` is the subfamily of the absorber consisting of the edges
that are still available; it is passed as a parameter so that the *instances*
of the decidability predicates below match those of the matching propositions
with the family substituted. -/
theorem crossing_step_aux {𝓗 : Hypergraph (Fin n)} {R R' used : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)} {N : Set 𝓗} {ρ ε γ κ ξ : ℝ}
    (hm : CrossingMargins n ρ ε γ κ ξ)
    (hUcard : (U.ncard : ℝ) ≤ (n : ℝ) / 100)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : IsAbsorber (incidentTwo 𝓗 U) R 𝓥 ρ (10 * γ) ξ) (hU𝓥 : U ∈ 𝓥)
    (hpseudo : PseudoRandom N (absorberFam R U ∪ {U, S}) γ κ)
    (hused : ∀ v : Fin n, ((nbrs used v).ncard : ℝ) ≤ κ * (n : ℝ))
    (hR'eq : R' = R \ used) :
    ∃ Nabs : Set 𝓗,
      IsMatching 𝓗 Nabs ∧
      (∀ e ∈ Nabs, (e : Set (Fin n)) ∈ R) ∧
      (∀ e ∈ Nabs, (e : Set (Fin n)) ∉ used) ∧
      Covers Nabs (U \ matchVert N) ∧
      Disjoint (matchVert Nabs) (matchVert N) := by
  classical
  have hRsub : R ⊆ incidentTwo 𝓗 U := habs.1
  have hup : UpperRegular (incidentTwo 𝓗 U) R ρ ξ := habs.2.2
  have hR'sub : R' ⊆ R := by rw [hR'eq]; exact fun e he => he.1
  have hR'notmem : ∀ e : Set (Fin n), e ∈ R' → e ∉ used := by
    intro e he
    rw [hR'eq] at he
    exact he.2
  set Af : Finset (Fin n) := sfin (U \ matchVert N) with hAfdef
  set VN : Finset (Fin n) := sfin (matchVert N) with hVNdef
  have hmemAf : ∀ x : Fin n, x ∈ Af ↔ x ∈ U ∧ x ∉ matchVert N := by
    intro x
    rw [hAfdef, mem_sfin, Set.mem_sdiff]
  have hmemVN : ∀ x : Fin n, x ∈ VN ↔ x ∈ matchVert N := by
    intro x
    rw [hVNdef, mem_sfin]
  have hcardAf : (Af.card : ℝ) = ((U \ matchVert N).ncard : ℝ) := by
    rw [hAfdef, card_sfin]
  -- upper regularity of `R'`
  have hreg : ∀ S T : Finset (Fin n), Disjoint S T →
      ξ * (n : ℝ) ≤ (S.card : ℝ) → ξ * (n : ℝ) ≤ (T.card : ℝ) →
      (edgeCount R' S T : ℝ) ≤ (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ) := by
    intro S T hdisj hS hT
    have h1 : (edgeCount R' S T : ℝ) ≤ (edgeCount R S T : ℝ) := by
      exact_mod_cast edgeCount_mono hR'sub S T
    have h2 := hup S T hdisj hS hT
    have h3 : (edgeCount (incidentTwo 𝓗 U) S T : ℝ) ≤ (S.card : ℝ) * (T.card : ℝ) := by
      have := edgeCount_le_card_mul (incidentTwo 𝓗 U) S T
      exact_mod_cast this
    have hρ0 : (0 : ℝ) ≤ ρ := le_of_lt hm.hρ
    nlinarith [h1, h2, h3]
  -- the degree hypothesis of the matching propositions
  have hdeg : ∀ a ∈ Af, 2 * ρ * (Af.card : ℝ) ≤
      ((((Finset.univ \ Af) : Finset (Fin n)).filter
        (fun b => ({a, b} : Set (Fin n)) ∈ R' ∧ b ∉ VN)).card : ℝ) := by
    intro a ha
    have hu : (a : Fin n) ∈ U := ((hmemAf a).mp ha).1
    have hc := crossing_degree hm hUcard hUdeg habs hU𝓥 hpseudo hused hu
    rw [← hcardAf] at hc
    have heq : (crossNbrs R' used U (matchVert N) a).ncard
        = (crossNbrs R used U (matchVert N) a).ncard := by
      rw [hR'eq]
      congr 1
      ext w
      simp only [crossNbrs, Set.mem_ofPred_eq, Set.mem_sdiff]
      tauto
    rw [← heq] at hc
    have hle := crossNbrs_ncard_le_filter (R' := R') (used := used) (U := U) (W := matchVert N)
      (VN := VN) (u := a) (Af := Af) hmemAf hmemVN
    have hcast : ((crossNbrs R' used U (matchVert N) a).ncard : ℝ) ≤
        ((((Finset.univ \ Af) : Finset (Fin n)).filter
          (fun b => ({a, b} : Set (Fin n)) ∈ R' ∧ b ∉ VN)).card : ℝ) := by
      exact_mod_cast hle
    linarith [hc, hcast]
  -- the common construction of the absorbing matching
  have build : ∀ (f : {a : Fin n // a ∈ Af} → {b : Fin n // b ∉ U ∧ b ∉ matchVert N}),
      Function.Injective f →
      (∀ a : {a : Fin n // a ∈ Af}, ({a.1, (f a).1} : Set (Fin n)) ∈ R') →
      ∃ Nabs : Set 𝓗,
        IsMatching 𝓗 Nabs ∧
        (∀ e ∈ Nabs, (e : Set (Fin n)) ∈ R) ∧
        (∀ e ∈ Nabs, (e : Set (Fin n)) ∉ used) ∧
        Covers Nabs (U \ matchVert N) ∧
        Disjoint (matchVert Nabs) (matchVert N) := by
    intro f hfinj hfm
    refine ⟨{e : 𝓗 | ∃ a : {a : Fin n // a ∈ Af},
        (e : Set (Fin n)) = ({a.1, (f a).1} : Set (Fin n))}, ?_, ?_, ?_, ?_, ?_⟩
    · intro e₁ he₁ e₂ he₂ hne
      obtain ⟨a₁, ha₁⟩ := he₁
      obtain ⟨a₂, ha₂⟩ := he₂
      refine Set.disjoint_left.mpr (fun x hx₁ hx₂ => ?_)
      have hx₁' : x ∈ ({a₁.1, (f a₁).1} : Set (Fin n)) := by rw [← ha₁]; exact hx₁
      have hx₂' : x ∈ ({a₂.1, (f a₂).1} : Set (Fin n)) := by rw [← ha₂]; exact hx₂
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx₁' hx₂'
      have hUa₁ : (a₁.1 : Fin n) ∈ U := ((hmemAf a₁.1).mp a₁.2).1
      have hUa₂ : (a₂.1 : Fin n) ∈ U := ((hmemAf a₂.1).mp a₂.2).1
      rcases hx₁' with h | h <;> rcases hx₂' with h' | h'
      · have haeq : a₁ = a₂ := Subtype.ext (h.symm.trans h')
        exact hne (Subtype.ext (by rw [ha₁, ha₂, haeq]))
      · exact (f a₂).2.1 ((h.symm.trans h') ▸ hUa₁)
      · exact (f a₁).2.1 ((h.symm.trans h') ▸ hUa₂)
      · have hfeq : (f a₁).1 = (f a₂).1 := h.symm.trans h'
        have haeq : a₁ = a₂ := hfinj (Subtype.ext hfeq)
        exact hne (Subtype.ext (by rw [ha₁, ha₂, haeq]))
    · rintro e ⟨a, ha⟩
      rw [ha]
      exact hR'sub (hfm a)
    · rintro e ⟨a, ha⟩
      rw [ha]
      exact hR'notmem _ (hfm a)
    · intro x hx
      have hxAf : x ∈ Af := (hmemAf x).mpr hx
      rw [mem_matchVert]
      refine ⟨⟨({x, (f ⟨x, hxAf⟩).1} : Set (Fin n)),
        incidentTwo_subset_self (hRsub (hR'sub (hfm ⟨x, hxAf⟩)))⟩, ⟨⟨x, hxAf⟩, rfl⟩, ?_⟩
      simp
    · rw [Set.disjoint_left]
      intro x hx hxN
      rw [mem_matchVert] at hx
      obtain ⟨e, he, hxe⟩ := hx
      obtain ⟨a, ha⟩ := he
      have hx' : x ∈ ({a.1, (f a).1} : Set (Fin n)) := by rw [← ha]; exact hxe
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
      rcases hx' with h | h
      · rw [h] at hxN
        exact ((hmemAf a.1).mp a.2).2 hxN
      · rw [h] at hxN
        exact (f a).2.2 hxN
  by_cases hbig : ξ * (n : ℝ) ≤ ρ * (Af.card : ℝ)
  · -- the upper-regular case
    obtain ⟨f, hfinj, hf⟩ := exists_matching_covering_of_upperRegular (R := R')
      (A := Af) (VN := VN) hm.hρ (le_of_lt hm.hξ) hm.hξρ hdeg hbig hreg
    have hconv : ∀ a : {a : Fin n // a ∈ Af}, (f a).1 ∉ U ∧ (f a).1 ∉ matchVert N := by
      intro a
      have hb := (f a).2
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hb
      refine ⟨?_, fun hd => (hf a).2 ((hmemVN _).mpr hd)⟩
      intro hc
      exact hb ((hmemAf _).mpr ⟨hc, fun hd => (hf a).2 ((hmemVN _).mpr hd)⟩)
    let g : {a : Fin n // a ∈ Af} → {b : Fin n // b ∉ U ∧ b ∉ matchVert N} :=
      fun a => ⟨(f a).1, hconv a⟩
    have hg : ∀ a, (g a : Fin n) = (f a).1 := fun a => rfl
    have hinj : Function.Injective g := by
      intro a b hab
      have h2 : (g a : Fin n) = (g b : Fin n) := congrArg Subtype.val hab
      rw [hg a, hg b] at h2
      exact hfinj (Subtype.ext h2)
    exact build g hinj (fun a => (hf a).1)
  · -- the small case: Hall's condition holds trivially
    have hsmall : ρ * (Af.card : ℝ) < ξ * (n : ℝ) := not_le.mp hbig
    have hgr : ∀ a ∈ Af, Af.card <
        (((((Finset.univ \ Af) : Finset (Fin n)) \ VN)).filter
          (fun b => ({a, b} : Set (Fin n)) ∈ R')).card := by
      intro a ha
      have hu : (a : Fin n) ∈ U := ((hmemAf a).mp ha).1
      have hc := crossing_degree_chain hm hUcard hUdeg habs hU𝓥 hpseudo hused hu
      have hsub : crossNbrs R' used U (matchVert N) a ⊆
          {b : Fin n | b ∈ (((Finset.univ \ Af) : Finset (Fin n)) \ VN) ∧
            ({a, b} : Set (Fin n)) ∈ R'} := by
        rintro w ⟨h1, h2, h3, h4⟩
        refine ⟨?_, h1⟩
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact ⟨fun hw => h3 ((hmemAf w).mp hw).1, fun hw => h4 ((hmemVN w).mp hw)⟩
      have hcard : (crossNbrs R' used U (matchVert N) a).ncard ≤
          (((((Finset.univ \ Af) : Finset (Fin n)) \ VN)).filter
            (fun b => ({a, b} : Set (Fin n)) ∈ R')).card := by
        have h1 : (crossNbrs R' used U (matchVert N) a).ncard ≤
            ({b : Fin n | b ∈ (((Finset.univ \ Af) : Finset (Fin n)) \ VN) ∧
              ({a, b} : Set (Fin n)) ∈ R'} : Set (Fin n)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
        have h2 : ({b : Fin n | b ∈ (((Finset.univ \ Af) : Finset (Fin n)) \ VN) ∧
              ({a, b} : Set (Fin n)) ∈ R'} : Set (Fin n)).ncard =
            (((((Finset.univ \ Af) : Finset (Fin n)) \ VN)).filter
              (fun b => ({a, b} : Set (Fin n)) ∈ R')).card := by
          rw [← card_sfin ({b : Fin n | b ∈ (((Finset.univ \ Af) : Finset (Fin n)) \ VN) ∧
              ({a, b} : Set (Fin n)) ∈ R'} : Set (Fin n))]
          congr 1
          ext b
          simp only [Finset.mem_filter, mem_sfin, Set.mem_ofPred_eq]
        rw [← h2]
        exact h1
      have hchain := crossing_arith_greedy hm
      have hA_lt : (Af.card : ℝ) < ((crossNbrs R' used U (matchVert N) a).ncard : ℝ) := by
        have hlt : (Af.card : ℝ) < ξ * (n : ℝ) / ρ := by
          rw [lt_div_iff₀ hm.hρ]
          linarith [hsmall]
        have heq : (crossNbrs R' used U (matchVert N) a).ncard
            = (crossNbrs R used U (matchVert N) a).ncard := by
          rw [hR'eq]
          congr 1
          ext w
          simp only [crossNbrs, Set.mem_ofPred_eq, Set.mem_sdiff]
          tauto
        rw [← heq] at hc
        linarith [hlt, hchain, hc]
      have hnat : Af.card < (crossNbrs R' used U (matchVert N) a).ncard := by
        exact_mod_cast hA_lt
      exact lt_of_lt_of_le hnat hcard
    obtain ⟨f, hfinj, hfm⟩ := exists_matching_covering_of_greedy (R := R')
      (A := Af) (B := (((Finset.univ \ Af) : Finset (Fin n)) \ VN)) hgr
    have hconv : ∀ a : {a : Fin n // a ∈ Af}, (f a).1 ∉ U ∧ (f a).1 ∉ matchVert N := by
      intro a
      have hb := (f a).2
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hb
      refine ⟨?_, fun hd => hb.2 ((hmemVN _).mpr hd)⟩
      intro hc
      exact hb.1 ((hmemAf _).mpr ⟨hc, fun hd => hb.2 ((hmemVN _).mpr hd)⟩)
    let g : {a : Fin n // a ∈ Af} → {b : Fin n // b ∉ U ∧ b ∉ matchVert N} :=
      fun a => ⟨(f a).1, hconv a⟩
    have hg : ∀ a, (g a : Fin n) = (f a).1 := fun a => rfl
    have hinj : Function.Injective g := by
      intro a b hab
      have h2 : (g a : Fin n) = (g b : Fin n) := congrArg Subtype.val hab
      rw [hg a, hg b] at h2
      exact hfinj (Subtype.ext h2)
    exact build g hinj (fun a => hfm a)

/-- **The one-step crossing absorption** (Lemma `crossing-absorption-lemma`'s
one-step engine). -/
theorem crossing_step {𝓗 : Hypergraph (Fin n)} {R used : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)} {N : Set 𝓗} {ρ ε γ κ ξ : ℝ}
    (hm : CrossingMargins n ρ ε γ κ ξ)
    (hUcard : (U.ncard : ℝ) ≤ (n : ℝ) / 100)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : IsAbsorber (incidentTwo 𝓗 U) R 𝓥 ρ (10 * γ) ξ) (hU𝓥 : U ∈ 𝓥)
    (hpseudo : PseudoRandom N (absorberFam R U ∪ {U, S}) γ κ)
    (hused : ∀ v : Fin n, ((nbrs used v).ncard : ℝ) ≤ κ * (n : ℝ)) :
    ∃ Nabs : Set 𝓗,
      IsMatching 𝓗 Nabs ∧
      (∀ e ∈ Nabs, (e : Set (Fin n)) ∈ R) ∧
      (∀ e ∈ Nabs, (e : Set (Fin n)) ∉ used) ∧
      Covers Nabs (U \ matchVert N) ∧
      Disjoint (matchVert Nabs) (matchVert N) :=
  crossing_step_aux (R' := R \ used) hm hUcard hUdeg habs hU𝓥 hpseudo hused rfl

/-! ## The crossing absorption lemma

Iterating the one-step lemma over `k ≤ κn` edge-disjoint matchings and adding
the resulting absorbing matchings to the original ones yields the paper's
Lemma `crossing-absorption-lemma`.
-/

theorem mem_famOf_of_mem {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {e : 𝓗} (he : e ∈ M) :
    (e : Set (Fin n)) ∈ famOf M := ⟨e, he, rfl⟩

theorem famOf_subset_famUnionIdx {𝓗 : Hypergraph (Fin n)} {k : ℕ} {M : Fin k → Set 𝓗}
    {j : Fin k} : famOf (M j) ⊆ famUnionIdx M :=
  fun e he => ⟨j, he⟩

/-- **The iteration of the one-step crossing absorption.** -/
theorem crossing_iter {𝓗 : Hypergraph (Fin n)} {R : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U : Set (Fin n)} {ρ ε γ κ ξ : ℝ}
    (hm : CrossingMargins n ρ ε γ κ ξ)
    (hUcard : (U.ncard : ℝ) ≤ (n : ℝ) / 100)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : IsAbsorber (incidentTwo 𝓗 U) R 𝓥 ρ (10 * γ) ξ) (hU𝓥 : U ∈ 𝓥) :
    ∀ (k : ℕ) (N : Fin k → Set 𝓗),
      (∀ i, PseudoRandom (N i) (absorberFam R U ∪ {U, ∅}) γ κ) →
      (k : ℝ) ≤ κ * (n : ℝ) →
      ∃ Nabs : Fin k → Set 𝓗,
        (∀ i, IsMatching 𝓗 (Nabs i)) ∧
        (∀ i j, i ≠ j → Disjoint (Nabs i) (Nabs j)) ∧
        (∀ i, Nabs i ⊆ {e : 𝓗 | (e : Set (Fin n)) ∈ R}) ∧
        (∀ i, Covers (Nabs i) (U \ matchVert (N i))) ∧
        (∀ i, Disjoint (matchVert (Nabs i)) (matchVert (N i))) := by
  intro k
  induction k with
  | zero =>
      intro N _ _
      exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
      intro N hpseudo hk
      let N0 : Fin k → Set 𝓗 := fun i => N i.castSucc
      have hpseudo0 : ∀ i, PseudoRandom (N0 i) (absorberFam R U ∪ {U, ∅}) γ κ :=
        fun i => hpseudo i.castSucc
      have hk0 : (k : ℝ) ≤ κ * (n : ℝ) := by
        have h : ((k : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
        linarith [hk, h]
      obtain ⟨Nabs0, hmat0, hdisj0, hR0, hcov0, hdisjN0⟩ := ih N0 hpseudo0 hk0
      set used : Hypergraph (Fin n) := famUnionIdx Nabs0 with huseddef
      have huseddeg : ∀ v : Fin n, ((nbrs used v).ncard : ℝ) ≤ κ * (n : ℝ) := by
        intro v
        have h1 : (nbrs used v).ncard ≤ k := by
          rw [huseddef]
          exact ncard_nbrs_famUnionIdx_le hmat0 v
        have h2 : ((nbrs used v).ncard : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
        linarith [h2, hk0]
      obtain ⟨NabsL, hmatL, hRL, hnotusedL, hcovL, hdisjNL⟩ :=
        crossing_step hm hUcard hUdeg habs hU𝓥 (hpseudo (Fin.last k)) huseddeg
      refine ⟨Fin.snoc Nabs0 NabsL, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · rw [Fin.snoc_castSucc]; exact hmat0 j
        · rw [Fin.snoc_last]; exact hmatL
      · intro i j hij
        rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl <;>
          rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
        · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hdisj0 a b (fun h => hij (congrArg Fin.castSucc h))
        · rw [Fin.snoc_castSucc, Fin.snoc_last, Set.disjoint_left]
          intro e he1 he2
          rw [huseddef] at hnotusedL
          exact hnotusedL e he2 (famOf_subset_famUnionIdx (mem_famOf_of_mem he1))
        · rw [Fin.snoc_last, Fin.snoc_castSucc, Set.disjoint_left]
          intro e he1 he2
          rw [huseddef] at hnotusedL
          exact hnotusedL e he1 (famOf_subset_famUnionIdx (mem_famOf_of_mem he2))
        · exact absurd rfl hij
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · rw [Fin.snoc_castSucc]; exact hR0 j
        · rw [Fin.snoc_last]; exact hRL
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · rw [Fin.snoc_castSucc]
          exact hcov0 j
        · rw [Fin.snoc_last]
          exact hcovL
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · rw [Fin.snoc_castSucc]
          exact hdisjN0 j
        · rw [Fin.snoc_last]
          exact hdisjNL

/-- **Lemma `crossing-absorption-lemma`** (the case `|U| ≤ n/100`).  If the
absorbable (by pseudorandomness) matchings `N_i` satisfy `k ≤ κn`, they can be
extended, using the edges of `R`, to a family of edge-disjoint matchings with
perfect coverage of `U`. -/
theorem crossing_absorption {𝓗 : Hypergraph (Fin n)} {R : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U : Set (Fin n)} {k : ℕ} {N : Fin k → Set 𝓗} {ρ ε γ κ ξ : ℝ}
    (hm : CrossingMargins n ρ ε γ κ ξ)
    (hUcard : (U.ncard : ℝ) ≤ (n : ℝ) / 100)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ))
    (habs : IsAbsorber (incidentTwo 𝓗 U) R 𝓥 ρ (10 * γ) ξ) (hU𝓥 : U ∈ 𝓥)
    (hpseudo : ∀ i, PseudoRandom (N i) (absorberFam R U ∪ {U, ∅}) γ κ)
    (hNm : ∀ i, IsMatching 𝓗 (N i))
    (hNdisj : ∀ i j, i ≠ j → Disjoint (N i) (N j))
    (hNR : ∀ i, ∀ e ∈ N i, (e : Set (Fin n)) ∉ R)
    (hk : (k : ℝ) ≤ κ * (n : ℝ)) :
    ∃ N' : Fin k → Set 𝓗,
      (∀ i, N i ⊆ N' i) ∧
      (∀ i, ∀ e ∈ N' i, e ∉ N i → (e : Set (Fin n)) ∈ R) ∧
      (∀ i, IsMatching 𝓗 (N' i)) ∧
      (∀ i j, i ≠ j → Disjoint (N' i) (N' j)) ∧
      PerfectCoverage N' U := by
  classical
  obtain ⟨Nabs, hmat, hdisj, hR, hcov, hdisjN⟩ :=
    crossing_iter hm hUcard hUdeg habs hU𝓥 k N hpseudo hk
  refine ⟨fun i => N i ∪ Nabs i, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Set.subset_union_left
  · intro i e he hnot
    rw [Set.mem_union] at he
    rcases he with h | h
    · exact absurd h hnot
    · exact hR i h
  · intro i
    refine isMatching_union (hNm i) (hmat i) ?_
    exact (hdisjN i).symm
  · intro i j hij
    rw [Set.disjoint_left]
    intro e hei hej
    rw [Set.mem_union] at hei hej
    rcases hei with hi | hi <;> rcases hej with hj | hj
    · exact (Set.disjoint_left.mp (hNdisj i j hij)) hi hj
    · exact (hNR i e hi) (hR j hj)
    · exact (hNR j e hj) (hR i hi)
    · exact (Set.disjoint_left.mp (hdisj i j hij)) hi hj
  · intro i x hx
    rw [matchVert_union]
    by_cases h : x ∈ matchVert (N i)
    · exact Or.inl h
    · exact Or.inr (hcov i ⟨hx, h⟩)

end

end ErdosFaberLovaszConjecture