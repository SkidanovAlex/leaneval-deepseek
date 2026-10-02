import Submission.EFL.GFactor

/-!
# Lemma 11.2: the existence of a regularising reservoir

This module proves the paper's Lemma `lem:reg_reservoir` (Lemma 11.2): if
`𝓗` is a linear `n`-vertex hypergraph whose 2-graph `G = 𝓗^{(2)}` is
`(ρ,ε)`-full and `Rabs` is a `(ρ/2, ξ, ξ, ε)`-absorber for the family `𝓥`,
then there is a `(ρ, ξ, ε, Rabs, 𝓥)`-regularising reservoir
`Rreg ⊆ E(G) ∖ Rabs`.

The proof follows the paper: pick a set `S ⊆ V^{(n-1)}(G)` of size
`⌈(ρ-20ε)n⌉` (a clique in `G`), reserve for each vertex `w` outside
`U ∪ U'` exactly `⌈(ρ-20ε)n - d_{Rabs}(w)⌉` edges of `E_{G'}(S,{w}) ∖ Rabs`
(call their union `R'`), and obtain `R''` from Lovász's `(g,f)`-factor
theorem applied to `G[U∪U'] - Rabs` with
`f(w) = ⌊ρ d_G(w) + ξn - d_{Rabs}(w) - d_{R'}(w)⌋`, `g = f - 1`.
Then `Rreg := R' ∪ R''` works.

The only deep input is `GFactorStatement` (Lovász's `(g,f)`-factor theorem).
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Elementary facts about 2-edge families -/

theorem pow2_two (𝓗 : Hypergraph (Fin n)) : ∀ e ∈ 𝓗.pow2, edgeSize e = 2 :=
  fun _ he => he.2

theorem nbrs_mono {R R' : Hypergraph (Fin n)} (h : R ⊆ R') (v : Fin n) :
    nbrs R v ⊆ nbrs R' v := fun w hw => h hw

theorem degAt_mono {R R' : Hypergraph (Fin n)} (h : R ⊆ R') (v : Fin n) :
    degAt R v ≤ degAt R' v := Set.ncard_le_ncard (nbrs_mono h v) (Set.toFinite _)

theorem nbrs_union (A B : Hypergraph (Fin n)) (v : Fin n) :
    nbrs (A ∪ B) v = nbrs A v ∪ nbrs B v := by
  ext w
  simp only [nbrs, Set.mem_setOf_eq, Set.mem_union]

/-- The degree in a union of two edge-disjoint families is the sum of the
degrees. -/
theorem degAt_union {A B : Hypergraph (Fin n)} (h : Disjoint A B) (v : Fin n) :
    degAt (A ∪ B) v = degAt A v + degAt B v := by
  have hdj : Disjoint (nbrs A v) (nbrs B v) := by
    rw [Set.disjoint_left]
    intro w hwa hwb
    exact (Set.disjoint_left.mp h) hwa hwb
  simp only [degAt, nbrs_union]
  rw [Set.ncard_union_eq hdj (Set.toFinite _) (Set.toFinite _)]

/-- A vertex of degree `n-1` in the 2-graph is adjacent to every other
vertex. -/
theorem clique_of_degAt (𝓗 : Hypergraph (Fin n)) {s t : Fin n}
    (hs : degAt 𝓗.pow2 s = n - 1) (ht : t ≠ s) : ({s, t} : Set (Fin n)) ∈ 𝓗.pow2 := by
  have hsub : nbrs (𝓗.pow2) s ⊆ (Set.univ \ {s} : Set (Fin n)) := by
    intro x hx
    simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    intro hxs
    have h2 : edgeSize ({s, x} : Set (Fin n)) = 2 := hx.2
    rw [hxs] at h2
    have hp : ({s, s} : Set (Fin n)) = ({s} : Set (Fin n)) := by ext y; simp
    rw [hp, edgeSize_eq_ncard, Set.ncard_singleton] at h2
    omega
  have hcard : ((Set.univ \ {s} : Set (Fin n)).ncard) = n - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (Set.mem_univ s), Set.ncard_univ, Nat.card_fin]
  have heq : nbrs (𝓗.pow2) s = (Set.univ \ {s} : Set (Fin n)) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [hcard]; exact le_of_eq hs.symm
  have ht' : t ∈ nbrs (𝓗.pow2) s := by
    rw [heq]
    simp [ht]
  exact ht'

/-! ## The induced `2`-graph on a vertex set minus an absorber -/

/-- The family of 2-edges of `𝓗` with both endpoints in `W`, minus `Rabs`:
the paper's `G[U ∪ U'] - Rabs`. -/
def inducedSub (𝓗 Rabs : Hypergraph (Fin n)) (W : Set (Fin n)) : Hypergraph (Fin n) :=
  {e | e ∈ 𝓗.pow2 ∧ e ⊆ W ∧ e ∉ Rabs}

@[simp]
theorem mem_inducedSub {𝓗 Rabs : Hypergraph (Fin n)} {W : Set (Fin n)} {e : Set (Fin n)} :
    e ∈ inducedSub 𝓗 Rabs W ↔ e ∈ 𝓗.pow2 ∧ e ⊆ W ∧ e ∉ Rabs := Iff.rfl

theorem inducedSub_subset (𝓗 Rabs : Hypergraph (Fin n)) (W : Set (Fin n)) :
    inducedSub 𝓗 Rabs W ⊆ 𝓗.pow2 := fun _ h => h.1

/-- On `W`, the degree in `inducedSub 𝓗 Rabs W` agrees with the full degree
(its edges stay inside `W`). -/
theorem degIn_inducedSub_eq (𝓗 Rabs : Hypergraph (Fin n)) {W : Set (Fin n)} {v : Fin n}
    (hv : v ∈ W) : degIn (inducedSub 𝓗 Rabs W) W v = degAt (inducedSub 𝓗 Rabs W) v := by
  simp only [degIn, degAt]
  congr 1
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    refine ⟨?_, hx⟩
    have hxsub : ({v, x} : Set (Fin n)) ⊆ W := hx.2.1
    exact hxsub (by simp)

/-- **Lower bound for the degree in `G[W] - Rabs`**: deleting the edges leaving
`W` and the edges of `Rabs` costs at most `|Wᶜ| + d_{Rabs}(v)` at `v`. -/
theorem degAt_inducedSub_lower (𝓗 Rabs : Hypergraph (Fin n)) (W : Set (Fin n)) (v : Fin n)
    (hv : v ∈ W) :
    degAt 𝓗.pow2 v ≤ degAt (inducedSub 𝓗 Rabs W) v + (Wᶜ).ncard + degAt Rabs v := by
  classical
  have hsub : nbrs (𝓗.pow2) v ⊆ (nbrs (inducedSub 𝓗 Rabs W) v ∪ nbrs Rabs v) ∪ Wᶜ := by
    intro x hx
    by_cases hxW : x ∈ W
    · by_cases hxR : ({v, x} : Set (Fin n)) ∈ Rabs
      · exact Or.inl (Or.inr hxR)
      · refine Or.inl (Or.inl ⟨hx, ?_, hxR⟩)
        intro y hy
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with h | h
        · rw [h]; exact hv
        · rw [h]; exact hxW
    · exact Or.inr hxW
  have h1 : (nbrs (𝓗.pow2) v).ncard ≤
      ((nbrs (inducedSub 𝓗 Rabs W) v ∪ nbrs Rabs v) ∪ Wᶜ).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ((nbrs (inducedSub 𝓗 Rabs W) v ∪ nbrs Rabs v) ∪ Wᶜ).ncard ≤
      (nbrs (inducedSub 𝓗 Rabs W) v).ncard + (nbrs Rabs v).ncard + (Wᶜ).ncard := by
    have h3 := Set.ncard_union_le (nbrs (inducedSub 𝓗 Rabs W) v ∪ nbrs Rabs v) (Wᶜ)
    have h4 := Set.ncard_union_le (nbrs (inducedSub 𝓗 Rabs W) v) (nbrs Rabs v)
    omega
  simp only [degAt] at h1 ⊢
  omega

/-! ## Counting the edges between two vertex sets, fibre by fibre -/

/-- Membership in `s.product t` (the `Finset.product` version of
`Finset.mem_product`). -/
theorem mem_product_iff {α β : Type*} {s : Finset α} {t : Finset β} {p : α × β} :
    p ∈ s.product t ↔ p.1 ∈ s ∧ p.2 ∈ t := by
  rw [show s.product t = s ×ˢ t from rfl, Finset.mem_product]

/-- The number of edges of `R` through `t` whose other endpoint lies in `S`. -/
noncomputable def fibreCount (R : Hypergraph (Fin n)) (S : Finset (Fin n)) (t : Fin n) : ℕ := by
  classical
  exact (S.filter (fun s => ({s, t} : Set (Fin n)) ∈ R)).card

/-- The number of `R`-edges from `S` to `T` is the sum over `t ∈ T` of the
number of `s ∈ S` with `{s,t} ∈ R`. -/
theorem edgeCount_eq_sum_fiber (R : Hypergraph (Fin n)) (S T : Finset (Fin n)) :
    edgeCount R S T = ∑ t ∈ T, fibreCount R S t := by
  classical
  rw [edgeCount]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Fin n × Fin n => p.2) (t := T)]
  swap
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter, mem_product_iff] at hp
    exact hp.1.2
  refine Finset.sum_congr rfl (fun t ht => ?_)
  unfold fibreCount
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpX, hpt⟩ := hp
    rw [Finset.mem_filter, mem_product_iff] at hpX
    obtain ⟨⟨hpS, _⟩, hpR⟩ := hpX
    rw [hpt] at hpR
    rw [Finset.mem_filter]
    exact ⟨hpS, hpR⟩
  · intro p hp q hq hpq
    rw [Finset.mem_filter] at hp hq
    exact Prod.ext hpq (hp.2.trans hq.2.symm)
  · intro s hs
    rw [Finset.mem_filter] at hs
    refine ⟨(s, t), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_filter, mem_product_iff]
    exact ⟨⟨⟨hs.1, ht⟩, by simpa using hs.2⟩, rfl⟩

/-! ## The degree bound furnished by an absorber -/

/-- **(cond:deg_abs)**.  An absorber `Rabs` with typicality parameter `ρ` has
degree at most `ρ d_G(v) + ξn` at every vertex, provided the whole vertex set
belongs to `𝓥`. -/
theorem absorber_degAt_le {𝓗 G' Rabs : Hypergraph (Fin n)} {𝓥 : Set (Set (Fin n))}
    {ρ ξ : ℝ} (hρ : 0 ≤ ρ) (hVuniv : (Set.univ : Set (Fin n)) ∈ 𝓥) (hsub : G' ⊆ 𝓗.pow2)
    (htyp : Typical G' Rabs ρ ξ 𝓥) (v : Fin n) :
    (degAt Rabs v : ℝ) ≤ ρ * (degAt 𝓗.pow2 v : ℝ) + ξ * n := by
  have h1 := (htyp Set.univ hVuniv v).1
  simp only [Set.univ_inter] at h1
  have h3 := (abs_le.mp h1).2
  have h2 : ((nbrs Rabs v).ncard : ℝ) ≤ ρ * ((nbrs G' v).ncard : ℝ) + ξ * (n : ℝ) := by
    linarith
  have h4 : ((nbrs G' v).ncard : ℝ) ≤ ((nbrs (𝓗.pow2) v).ncard : ℝ) := by
    exact_mod_cast degAt_mono hsub v
  have h5 : ρ * ((nbrs G' v).ncard : ℝ) ≤ ρ * ((nbrs (𝓗.pow2) v).ncard : ℝ) :=
    mul_le_mul_of_nonneg_left h4 hρ
  simp only [degAt]
  linarith

/-! ## Vertices of degree exactly `n-1` -/

/-- The vertices of `G = 𝓗^{(2)}` of degree exactly `d`, as a finset. -/
noncomputable def degExactly (𝓗 : Hypergraph (Fin n)) (d : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v : Fin n => degAt 𝓗.pow2 v = d)

theorem coe_degExactly (𝓗 : Hypergraph (Fin n)) (d : ℕ) :
    (degExactly 𝓗 d : Set (Fin n)) = VeqNat 𝓗 d := by
  classical
  ext v
  simp [degExactly, VeqNat]

/-- **The set `S` of Lemma 11.2**: `(ρ,ε)`-fullness supplies `⌈(ρ-20ε)n⌉`
vertices of degree `n-1` in `G`. -/
theorem exists_clique_finset (𝓗 : Hypergraph (Fin n)) {k : ℕ}
    (hcard : k ≤ (degExactly 𝓗 (n - 1)).card) :
    ∃ S : Finset (Fin n), (∀ s ∈ S, degAt 𝓗.pow2 s = n - 1) ∧ S.card = k := by
  classical
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (s := degExactly 𝓗 (n - 1)) hcard
  refine ⟨S, ?_, hScard⟩
  intro s hs
  have h1 : s ∈ degExactly 𝓗 (n - 1) := hSsub hs
  simpa only [degExactly, Finset.mem_filter, Finset.mem_univ, true_and] using h1

/-! ## The family `R'` of reserved edges -/

theorem mem_canonFinset {G : Hypergraph (Fin n)} {e : Set (Fin n)} :
    e ∈ canonFinset G ↔ e ∈ G := by
  classical
  simp [canonFinset]

/-- The number of edges of `R` through `w` with other endpoint in `S` is at
most the degree of `w`. -/
theorem fibreCount_le_degAt (R : Hypergraph (Fin n)) (S : Finset (Fin n)) (w : Fin n) :
    fibreCount R S w ≤ degAt R w := by
  classical
  unfold fibreCount
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro s hs
  rw [Finset.mem_coe, Finset.mem_filter] at hs
  show ({w, s} : Set (Fin n)) ∈ R
  rw [Set.pair_comm]
  exact hs.2

/-- `s ↦ {s,w}` is injective on a set not containing `w`. -/
theorem pair_injOn (S : Finset (Fin n)) {w : Fin n} (hw : w ∉ S) :
    Set.InjOn (fun s : Fin n => ({s, w} : Set (Fin n))) ↑S := by
  intro a ha b _ hab
  have haS : a ∈ S := ha
  have hab' : ({a, w} : Set (Fin n)) = ({b, w} : Set (Fin n)) := hab
  have hba : a ∈ ({b, w} : Set (Fin n)) := by rw [← hab']; simp
  rcases hba with h | h
  · exact h
  · exact absurd (h ▸ haS) hw

/-- The `w`-fibre of the pairs through the vertices of `S`. -/
theorem card_pairImage_inter_canon (R : Hypergraph (Fin n)) (S : Finset (Fin n))
    {w : Fin n} (hw : w ∉ S) :
    ((S.image (fun s => ({s, w} : Set (Fin n)))) ∩ canonFinset R).card = fibreCount R S w := by
  classical
  rw [fibreCount]
  refine (Finset.card_bij (fun s _ => ({s, w} : Set (Fin n))) ?_ ?_ ?_).symm
  · intro s hs
    rw [Finset.mem_filter] at hs
    rw [Finset.mem_inter, Finset.mem_image]
    exact ⟨⟨s, hs.1, rfl⟩, mem_canonFinset.mpr hs.2⟩
  · intro a ha b hb hab
    exact pair_injOn S hw (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab
  · intro e he
    rw [Finset.mem_inter, Finset.mem_image] at he
    obtain ⟨⟨s, hsS, hse⟩, heR⟩ := he
    refine ⟨s, ?_, hse⟩
    rw [Finset.mem_filter]
    exact ⟨hsS, mem_canonFinset.mp (hse.symm ▸ heR)⟩

/-- **The family `R'` of Lemma 11.2.**  Given a set `S` of pairwise adjacent
vertices and, for each `w ∈ W0`, a prescribed number `m w` of edges `{s,w}`
(`s ∈ S`) that is affordable, there is a family `R' ⊆ 𝓗^{(2)}` of 2-edges,
disjoint from `Rabs`, realising exactly `m w` edges at each `w ∈ W0` and at
most `|W0|` edges at each vertex outside `W0`. -/
theorem exists_reservoir_subfamily (𝓗 Rabs : Hypergraph (Fin n)) (S W0 : Finset (Fin n))
    (m : Fin n → ℕ)
    (hclique : ∀ s ∈ S, ∀ t : Fin n, t ≠ s → ({s, t} : Set (Fin n)) ∈ 𝓗.pow2)
    (hW0 : ∀ w ∈ W0, w ∉ S)
    (havail : ∀ w ∈ W0, m w + degAt Rabs w ≤ S.card) :
    ∃ R' : Hypergraph (Fin n), R' ⊆ 𝓗.pow2 ∧ Disjoint R' Rabs ∧
      (∀ w ∈ W0, degAt R' w = m w) ∧
      (∀ x : Fin n, x ∉ W0 → degAt R' x ≤ W0.card) := by
  classical
  have key : ∀ w : Fin n, ∃ A : Finset (Set (Fin n)),
      (w ∈ W0 → A.card = m w ∧ (∀ e ∈ A, ∃ s ∈ S, e = ({s, w} : Set (Fin n))) ∧
        (∀ e ∈ A, e ∉ Rabs)) ∧ (w ∉ W0 → A = ∅) := by
    intro w
    by_cases hw : w ∈ W0
    · have hwS : w ∉ S := hW0 w hw
      have havl : m w ≤
          (S.image (fun s => ({s, w} : Set (Fin n))) \ canonFinset Rabs).card := by
        have h1 : (S.image (fun s => ({s, w} : Set (Fin n))) \ canonFinset Rabs).card =
            (S.image (fun s => ({s, w} : Set (Fin n)))).card -
              (canonFinset Rabs ∩ S.image (fun s => ({s, w} : Set (Fin n)))).card :=
          Finset.card_sdiff
        have h2 : (S.image (fun s => ({s, w} : Set (Fin n)))).card = S.card :=
          Finset.card_image_of_injOn (pair_injOn S hwS)
        have h3 : (canonFinset Rabs ∩ S.image (fun s => ({s, w} : Set (Fin n)))).card ≤
            degAt Rabs w := by
          rw [Finset.inter_comm, card_pairImage_inter_canon Rabs S hwS]
          exact fibreCount_le_degAt Rabs S w
        have h4 := havail w hw
        omega
      obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq
        (s := S.image (fun s => ({s, w} : Set (Fin n))) \ canonFinset Rabs) (n := m w) havl
      refine ⟨A, ?_, fun h => absurd hw h⟩
      intro _
      refine ⟨hAcard, ?_, ?_⟩
      · intro e he
        have h1 : e ∈ S.image (fun s => ({s, w} : Set (Fin n))) ∧ e ∉ canonFinset Rabs :=
          Finset.mem_sdiff.mp (hAsub he)
        obtain ⟨s, hsS, hse⟩ := Finset.mem_image.mp h1.1
        exact ⟨s, hsS, hse.symm⟩
      · intro e he heR
        have h1 : e ∈ S.image (fun s => ({s, w} : Set (Fin n))) ∧ e ∉ canonFinset Rabs :=
          Finset.mem_sdiff.mp (hAsub he)
        exact h1.2 (mem_canonFinset.mpr heR)
    · exact ⟨∅, fun h => absurd h hw, fun _ => rfl⟩
  choose A hA using key
  set R'F : Finset (Set (Fin n)) := W0.biUnion A with hR'F
  have hR'Fmem : ∀ e : Set (Fin n), e ∈ R'F ↔ ∃ w ∈ W0, e ∈ A w := by
    intro e; rw [hR'F, Finset.mem_biUnion]
  have hpairs : ∀ (w : Fin n), w ∈ W0 → ∀ e ∈ A w, ∃ s ∈ S, e = ({s, w} : Set (Fin n)) :=
    fun w hw e he => ((hA w).1 hw).2.1 e he
  have hnotRabs : ∀ (w : Fin n), w ∈ W0 → ∀ e ∈ A w, e ∉ Rabs :=
    fun w hw e he => ((hA w).1 hw).2.2 e he
  have hAcard : ∀ (w : Fin n), w ∈ W0 → (A w).card = m w :=
    fun w hw => ((hA w).1 hw).1
  have hAempty : ∀ (w : Fin n), w ∉ W0 → A w = ∅ := fun w hw => (hA w).2 hw
  have hpow : (R'F : Set (Set (Fin n))) ⊆ 𝓗.pow2 := by
    intro e he
    rw [Finset.mem_coe, hR'Fmem] at he
    obtain ⟨w, hw, heA⟩ := he
    obtain ⟨s, hsS, rfl⟩ := hpairs w hw e heA
    exact hclique s hsS w (fun h => hW0 w hw (h ▸ hsS))
  have hAmat : ∀ (w : Fin n), w ∈ W0 → A w ⊆ R'F := by
    intro w hw e he
    rw [hR'Fmem]; exact ⟨w, hw, he⟩
  refine ⟨(R'F : Set (Set (Fin n))), hpow, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro e he1 he2
    rw [Finset.mem_coe, hR'Fmem] at he1
    obtain ⟨w, hw, heA⟩ := he1
    exact hnotRabs w hw e heA he2
  · intro w hw
    have hwS : w ∉ S := hW0 w hw
    have hseteq : nbrs (R'F : Set (Set (Fin n))) w =
        {t : Fin n | ({t, w} : Set (Fin n)) ∈ A w} := by
      ext t
      constructor
      · intro ht
        have ht1 : ({w, t} : Set (Fin n)) ∈ R'F := ht
        rw [Set.pair_comm] at ht1
        rw [hR'Fmem] at ht1
        obtain ⟨w', hw', htw'⟩ := ht1
        obtain ⟨s, hsS, hsw⟩ := hpairs w' hw' _ htw'
        have hww' : w' = w := by
          by_contra hne
          have hwmem : w ∈ ({s, w'} : Set (Fin n)) := by rw [← hsw]; simp
          rcases hwmem with h | h
          · exact hW0 w hw (h ▸ hsS)
          · exact hne h.symm
        subst hww'
        exact htw'
      · intro ht
        have h1 : ({t, w} : Set (Fin n)) ∈ R'F := hAmat w hw ht
        have h2 : ({w, t} : Set (Fin n)) ∈ (R'F : Set (Set (Fin n))) := by
          rw [Finset.mem_coe, Set.pair_comm]; exact h1
        exact h2
    have hcard2 : ({t : Fin n | ({t, w} : Set (Fin n)) ∈ A w}).ncard = (A w).card := by
      rw [← Set.ncard_coe_finset (s := A w)]
      refine Set.ncard_congr (fun t _ => ({t, w} : Set (Fin n))) ?_ ?_ ?_
      · intro t ht; exact ht
      · intro a b ha hb hab
        have hpa : ({a, w} : Set (Fin n)) ∈ 𝓗.pow2 := hpow (Finset.mem_coe.mpr (hAmat w hw ha))
        have hpb : ({b, w} : Set (Fin n)) ∈ 𝓗.pow2 := hpow (Finset.mem_coe.mpr (hAmat w hw hb))
        have haw : a ≠ w := by
          intro h
          have h1 : edgeSize ({a, w} : Set (Fin n)) = 2 := hpa.2
          rw [h] at h1
          have hp : ({w, w} : Set (Fin n)) = ({w} : Set (Fin n)) := by ext y; simp
          rw [hp, edgeSize_eq_ncard, Set.ncard_singleton] at h1
          omega
        have hbw : b ≠ w := by
          intro h
          have h1 : edgeSize ({b, w} : Set (Fin n)) = 2 := hpb.2
          rw [h] at h1
          have hp : ({w, w} : Set (Fin n)) = ({w} : Set (Fin n)) := by ext y; simp
          rw [hp, edgeSize_eq_ncard, Set.ncard_singleton] at h1
          omega
        have hab' : ({a, w} : Set (Fin n)) = ({b, w} : Set (Fin n)) := hab
        have hamem : a ∈ ({b, w} : Set (Fin n)) := by rw [← hab']; simp
        rcases hamem with h | h
        · exact h
        · exact absurd h haw
      · intro e he
        obtain ⟨s, hsS, hse⟩ := hpairs w hw e (Finset.mem_coe.mp he)
        refine ⟨s, ?_, hse.symm⟩
        rw [hse] at he
        exact he
    simp only [degAt]
    rw [hseteq, hcard2, hAcard w hw]
  · intro x hx
    have hsub : nbrs (R'F : Set (Set (Fin n))) x ⊆ (↑W0 : Set (Fin n)) := by
      intro t ht
      have ht1 : ({x, t} : Set (Fin n)) ∈ R'F := ht
      rw [hR'Fmem] at ht1
      obtain ⟨w', hw', htw'⟩ := ht1
      obtain ⟨s, hsS, hsw⟩ := hpairs w' hw' _ htw'
      have hxmem : x ∈ ({s, w'} : Set (Fin n)) := by rw [← hsw]; simp
      have hxs : x = s := by
        rcases hxmem with h | h
        · exact h
        · exact absurd (h ▸ hw') hx
      have htmem : t ∈ ({s, w'} : Set (Fin n)) := by rw [← hsw]; simp
      rw [← hxs] at htmem
      have htx : t ≠ x := by
        intro h
        have hpow' : ({x, t} : Set (Fin n)) ∈ 𝓗.pow2 :=
          hpow (Finset.mem_coe.mpr (hAmat w' hw' htw'))
        have h2 : edgeSize ({x, t} : Set (Fin n)) = 2 := hpow'.2
        rw [h] at h2
        have hp : ({x, x} : Set (Fin n)) = ({x} : Set (Fin n)) := by ext y; simp
        rw [hp, edgeSize_eq_ncard, Set.ncard_singleton] at h2
        omega
      rcases htmem with h | h
      · exact absurd h htx
      · rw [h]; exact hw'
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    simp only [degAt]
    rw [Set.ncard_coe_finset] at this
    exact this

/-! ## Complements as finsets, and the vertices of `V_+` -/

/-- The complement of a vertex set, as a finset. -/
noncomputable def complFinset (X : Set (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun x : Fin n => x ∉ X)

theorem mem_complFinset {X : Set (Fin n)} {x : Fin n} :
    x ∈ complFinset X ↔ x ∉ X := by
  classical
  simp [complFinset]

theorem coe_complFinset (X : Set (Fin n)) : (complFinset X : Set (Fin n)) = Xᶜ := by
  classical
  ext x
  simp [complFinset]

theorem card_complFinset (X : Set (Fin n)) : (complFinset X).card = (Xᶜ).ncard := by
  rw [← Set.ncard_coe_finset, coe_complFinset]

/-- Every vertex of degree exactly `n-1` in `G` lies in `V_+^{(1-ε)}(G)` when
`1 ≤ εn`. -/
theorem VeqNat_subset_Vplus (𝓗 : Hypergraph (Fin n)) {ε : ℝ} (hεn : 1 ≤ ε * n) :
    VeqNat 𝓗 (n - 1) ⊆ Vplus 𝓗 (1 - ε) := by
  intro v hv
  simp only [Vplus, Set.mem_setOf_eq]
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h] at hεn
      simp only [Nat.cast_zero, mul_zero] at hεn
      linarith
    · exact h
  have hn1 : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
    push_cast [hn]; ring
  have hv' : ((degAt 𝓗.pow2 v : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) := by rw [hv]
  rw [hv', ← hn1]
  nlinarith [hεn]

/-- **Lower bound for `f`**: the floor `⌊ρ d_G(w) + ξn - d_{Rabs}(w) - d_{R'}(w)⌋`
is at least `ρn/4` for every `w ∈ U ∪ U'`. -/
theorem floor_ge_quarter {dG dA dR ρ ξ N : ℝ} (hρ : 0 < ρ)
    (hdG : (1 - ρ) * N ≤ dG) (hA : dA ≤ (ρ / 2 + ξ) * N) (hR : dR ≤ ρ * N / 10)
    (hρ1 : ρ ≤ 1 / 100) (hρn : 25 ≤ ρ * N) :
    ρ * N / 4 ≤ (⌊ρ * dG + ξ * N - dA - dR⌋ : ℝ) := by
  have hx : ρ * N / 4 + 1 ≤ ρ * dG + ξ * N - dA - dR := by
    have h1 : ρ * ((1 - ρ) * N) ≤ ρ * dG := mul_le_mul_of_nonneg_left hdG hρ.le
    have h2 : 1 ≤ ρ * N * (3 / 20 - ρ) := by nlinarith [hρ.le, hρ1, hρn]
    nlinarith [h1, h2]
  have h1 : (⌊ρ * dG + ξ * N - dA - dR⌋ : ℝ) > ρ * dG + ξ * N - dA - dR - 1 := by
    have := Int.lt_floor_add_one (ρ * dG + ξ * N - dA - dR)
    push_cast
    linarith
  linarith

/-- **Upper bound for `f`**: the floor is at most `3ρn/2`. -/
theorem floor_le_three_halves {dG dA dR ρ ξ N : ℝ} (hρ : 0 ≤ ρ) (hN : 0 ≤ N) (hdG : dG ≤ N)
    (hA : 0 ≤ dA) (hR : 0 ≤ dR) (hξ : ξ ≤ ρ / 2) :
    (⌊ρ * dG + ξ * N - dA - dR⌋ : ℝ) ≤ 3 * ρ * N / 2 := by
  have h1 : (⌊ρ * dG + ξ * N - dA - dR⌋ : ℝ) ≤ ρ * dG + ξ * N - dA - dR := by
    have := Int.floor_le (ρ * dG + ξ * N - dA - dR)
    push_cast
    linarith
  have h2 : ρ * dG ≤ ρ * N := mul_le_mul_of_nonneg_left hdG hρ
  have h3 : ξ * N ≤ ρ / 2 * N := mul_le_mul_of_nonneg_right hξ hN
  linarith


/-- Subadditivity of the degree: `d_{A ∪ B}(v) ≤ d_A(v) + d_B(v)`. -/
theorem degAt_union_le (A B : Hypergraph (Fin n)) (v : Fin n) :
    degAt (A ∪ B) v ≤ degAt A v + degAt B v := by
  simp only [degAt, nbrs_union]
  exact Set.ncard_union_le _ _

/-- `fibreCount` is at most the degree inside any vertex set containing `S`. -/
theorem fibreCount_le_degIn (H : Hypergraph (Fin n)) {W : Set (Fin n)} {S : Finset (Fin n)}
    (hSW : ∀ s ∈ S, s ∈ W) (t : Fin n) : fibreCount H S t ≤ degIn H W t := by
  classical
  unfold fibreCount degIn
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro s hs
  rw [Finset.mem_coe, Finset.mem_filter] at hs
  refine ⟨hSW s hs.1, ?_⟩
  show ({t, s} : Set (Fin n)) ∈ H
  rw [Set.pair_comm]
  exact hs.2

/-- **The Lovász condition** of Theorem `thm:gf_factor` holds for the functions
`f, g` of Lemma 11.2: two cases, according to whether `|S|` is small. -/
theorem lovasz_condition (H : Hypergraph (Fin n)) (W : Set (Fin n)) (f g : Fin n → ℤ)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ45 : ρ ≤ 1 / 45) (hρn : 4 ≤ ρ * n)
    (hg : ∀ x, g x = f x - 1)
    (hf_lo : ∀ x ∈ W, ρ * (n : ℝ) / 4 ≤ (f x : ℝ))
    (hf_hi : ∀ x ∈ W, (f x : ℝ) ≤ 3 * ρ * (n : ℝ) / 2)
    (hdH : ∀ x ∈ W, (1 - 3 * ρ) * (n : ℝ) ≤ (degIn H W x : ℝ)) :
    ∀ S T : Finset (Fin n), (∀ x ∈ S, x ∈ W) → (∀ x ∈ T, x ∈ W) → Disjoint S T →
      (edgeCount H S T : ℤ) ≤ (∑ s ∈ S, f s) + ∑ t ∈ T, ((degIn H W t : ℤ) - g t) := by
  classical
  intro S T hSW hTW hdisj
  have hfpos : ∀ x ∈ W, 0 < ρ * (n : ℝ) / 4 := by
    intro x _
    have : (0 : ℝ) < ρ * n := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    linarith
  have hfnonneg : ∀ x ∈ W, 0 ≤ f x := by
    intro x hx
    have h1 := hf_lo x hx
    have h2 := hfpos x hx
    have : (0 : ℝ) ≤ (f x : ℝ) := le_trans h2.le h1
    exact_mod_cast this
  have hsum_eq : (edgeCount H S T : ℤ) = ∑ t ∈ T, (fibreCount H S t : ℤ) := by
    rw [edgeCount_eq_sum_fiber, Nat.cast_sum]
  have hfib_le_deg : ∀ t : Fin n, fibreCount H S t ≤ degIn H W t :=
    fun t => fibreCount_le_degIn H hSW t
  have hcard_le : S.card + T.card ≤ n := by
    have h1 : S.card + T.card = (S ∪ T).card := (Finset.card_union_of_disjoint hdisj).symm
    have h2 : (S ∪ T).card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ (S ∪ T))
    omega
  by_cases hcase : (S.card : ℝ) ≤ (1 - 5 * ρ) * (n : ℝ)
  · -- Case A: `|S|` is small, so each fibre can be compared with `g`.
    have hper : ∀ t ∈ T, (fibreCount H S t : ℤ) ≤ (degIn H W t : ℤ) - g t := by
      intro t ht
      have h1 : (fibreCount H S t : ℝ) ≤ (S.card : ℝ) := by
        unfold fibreCount
        exact_mod_cast Finset.card_filter_le S (fun s => ({s, t} : Set (Fin n)) ∈ H)
      have h2 : (g t : ℝ) ≤ 3 * ρ * (n : ℝ) / 2 - 1 := by
        have h3 := hf_hi t (hTW t ht)
        have h4 : g t = f t - 1 := hg t
        rw [h4]
        push_cast
        linarith
      have h5 : (1 - 3 * ρ) * (n : ℝ) ≤ (degIn H W t : ℝ) := hdH t (hTW t ht)
      have h6 : ((fibreCount H S t : ℤ) + g t : ℝ) ≤ (degIn H W t : ℝ) := by
        push_cast
        linarith
      have h7 : (fibreCount H S t : ℤ) + g t ≤ (degIn H W t : ℤ) := by exact_mod_cast h6
      linarith
    have h8 := Finset.sum_le_sum hper
    have h9 : 0 ≤ ∑ s ∈ S, f s := Finset.sum_nonneg (fun s hs => hfnonneg s (hSW s hs))
    rw [hsum_eq]
    linarith
  · -- Case B: `|S|` is large, so `|T|` is small and `∑_{s} f s` dominates `∑_t g t`.
    push_neg at hcase
    have hTlt : (T.card : ℝ) < 5 * ρ * (n : ℝ) := by
      have h1 : (T.card : ℝ) ≤ (n : ℝ) - (S.card : ℝ) := by
        have h0 : ((S.card + T.card : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard_le
        push_cast at h0
        linarith
      linarith
    have hsum_g : (∑ t ∈ T, g t : ℝ) ≤ (T.card : ℝ) * (2 * ρ * (n : ℝ)) := by
      have hper : ∀ t ∈ T, (g t : ℝ) ≤ 2 * ρ * (n : ℝ) := by
        intro t ht
        have h3 := hf_hi t (hTW t ht)
        have h4 : g t = f t - 1 := hg t
        rw [h4]
        push_cast
        linarith
      calc (∑ t ∈ T, (g t : ℝ)) ≤ ∑ t ∈ T, (2 * ρ * (n : ℝ)) := Finset.sum_le_sum hper
        _ = (T.card : ℝ) * (2 * ρ * (n : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hsum_f : ((S.card : ℝ)) * (ρ * (n : ℝ) / 4) ≤ (∑ s ∈ S, f s : ℝ) := by
      calc ((S.card : ℝ)) * (ρ * (n : ℝ) / 4) = ∑ s ∈ S, (ρ * (n : ℝ) / 4) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ s ∈ S, ((f s : ℝ)) := Finset.sum_le_sum (fun s hs => hf_lo s (hSW s hs))
    have hnum : (T.card : ℝ) * (2 * ρ * (n : ℝ)) ≤ (S.card : ℝ) * (ρ * (n : ℝ) / 4) := by
      have h1 : (0 : ℝ) ≤ ρ * n := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have h2 : (T.card : ℝ) * (2 * ρ * n) ≤ (5 * ρ * n) * (2 * ρ * n) := by
        apply mul_le_mul_of_nonneg_right hTlt.le
        linarith
      have h3 : (5 * ρ * n) * (2 * ρ * n) ≤ ((1 - 5 * ρ) * n) * (ρ * n / 4) := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hρn2 : 0 ≤ ρ * n * n := mul_nonneg (mul_nonneg hρ0.le hn) hn
        have h45 : 0 ≤ 1 - 45 * ρ := by linarith
        nlinarith [mul_nonneg hρn2 h45]
      have h4 : ((1 - 5 * ρ) * n) * (ρ * n / 4) ≤ (S.card : ℝ) * (ρ * n / 4) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        linarith
      linarith
    have hsum_g_le : (∑ t ∈ T, g t : ℝ) ≤ (∑ s ∈ S, f s : ℝ) := by linarith
    have hsplit : (∑ s ∈ S, f s) + ∑ t ∈ T, ((degIn H W t : ℤ) - g t) =
        (∑ t ∈ T, (degIn H W t : ℤ)) + ((∑ s ∈ S, f s) - ∑ t ∈ T, g t) := by
      rw [Finset.sum_sub_distrib]
      ring
    have hsum_le : (∑ t ∈ T, (fibreCount H S t : ℤ)) ≤ ∑ t ∈ T, (degIn H W t : ℤ) :=
      Finset.sum_le_sum (fun t _ => by exact_mod_cast hfib_le_deg t)
    have hgsum : (∑ t ∈ T, g t : ℤ) ≤ ∑ s ∈ S, f s := by exact_mod_cast hsum_g_le
    rw [hsum_eq, hsplit]
    linarith


/-- The complement of a vertex set has at most `c n` vertices when `U` contains
at least `(1-c)n` of them. -/
theorem ncard_compl_le (U : Set (Fin n)) {c : ℝ} (h : (1 - c) * n ≤ (U.ncard : ℝ)) :
    ((Uᶜ).ncard : ℝ) ≤ c * n := by
  have h1 : ((U.ncard : ℕ) : ℝ) + ((Uᶜ).ncard : ℝ) = (n : ℝ) := by
    have h2 := Set.ncard_add_ncard_compl U (Set.toFinite _) (Set.toFinite _)
    rw [Nat.card_fin] at h2
    exact_mod_cast h2
  linarith

/-- Degrees in a `2`-graph on `Fin n` are at most `n`. -/
theorem degAt_le_n (R : Hypergraph (Fin n)) (v : Fin n) : degAt R v ≤ n := by
  have h := degIn_le_card R Set.univ v
  rw [degIn_univ] at h
  rwa [Set.ncard_univ, Nat.card_fin] at h

/-- When all edges of `R` lie inside `W` and `v ∈ W`, the degree inside `W`
agrees with the full degree. -/
theorem degIn_eq_degAt_of_subset {R : Hypergraph (Fin n)} {W : Set (Fin n)}
    (h : ∀ e ∈ R, e ⊆ W) {v : Fin n} (hv : v ∈ W) : degIn R W v = degAt R v := by
  simp only [degIn, degAt]
  congr 1
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact ⟨h _ hx (by simp), hx⟩


/-! ## The data of Lemma 11.2: the sets `U'`, `W`, `W₀` and the functions `f`, `g` -/

/-- The paper's `U'` of (eq:defU'). -/
def UpSet (𝓗 : Hypergraph (Fin n)) (ε ρ : ℝ) : Set (Fin n) :=
  {w | w ∉ Vplus 𝓗 (1 - ε) ∧ (1 - 20 * ε / ρ) * (n : ℝ) ≤ (degAt 𝓗.pow2 w : ℝ)}

theorem mem_UpSet {𝓗 : Hypergraph (Fin n)} {ε ρ : ℝ} {w : Fin n} :
    w ∈ UpSet 𝓗 ε ρ ↔
      w ∉ Vplus 𝓗 (1 - ε) ∧ (1 - 20 * ε / ρ) * (n : ℝ) ≤ (degAt 𝓗.pow2 w : ℝ) :=
  Iff.rfl

/-- `W = U ∪ U'`. -/
def WsetOf (𝓗 : Hypergraph (Fin n)) (ε ρ : ℝ) : Set (Fin n) :=
  Vplus 𝓗 (1 - ε) ∪ UpSet 𝓗 ε ρ

theorem mem_WsetOf {𝓗 : Hypergraph (Fin n)} {ε ρ : ℝ} {w : Fin n} :
    w ∈ WsetOf 𝓗 ε ρ ↔ w ∈ Vplus 𝓗 (1 - ε) ∨ w ∈ UpSet 𝓗 ε ρ := Iff.rfl

/-- `W₀ = V ∖ W`. -/
noncomputable def W0F (𝓗 : Hypergraph (Fin n)) (ε ρ : ℝ) : Finset (Fin n) :=
  complFinset (WsetOf 𝓗 ε ρ)

theorem mem_W0F {𝓗 : Hypergraph (Fin n)} {ε ρ : ℝ} {w : Fin n} :
    w ∈ W0F 𝓗 ε ρ ↔ w ∉ WsetOf 𝓗 ε ρ := mem_complFinset

/-- The number of edges reserved at `w ∈ W₀`: `⌈(ρ-20ε)n⌉ - d_{Rabs}(w)`. -/
noncomputable def mval (Rabs : Hypergraph (Fin n)) (ε ρ : ℝ) (w : Fin n) : ℕ :=
  ⌈(ρ - 20 * ε) * (n : ℝ)⌉₊ - degAt Rabs w

/-- The function `f` of Lemma 11.2:
`f(w) = ⌊ρ d_G(w) + ξn - d_{Rabs}(w) - d_{R'}(w)⌋`. -/
noncomputable def fval (𝓗 Rabs R' : Hypergraph (Fin n)) (ρ ξ : ℝ) (w : Fin n) : ℤ :=
  ⌊ρ * (degAt 𝓗.pow2 w : ℝ) + ξ * (n : ℝ) - (degAt Rabs w : ℝ) - (degAt R' w : ℝ)⌋

/-- The upper bound `f ≤ ρ d_G + ξn - d_{Rabs} - d_{R'}`. -/
theorem fval_le (𝓗 Rabs R' : Hypergraph (Fin n)) (ρ ξ : ℝ) (v : Fin n) :
    (fval 𝓗 Rabs R' ρ ξ v : ℝ) ≤
      ρ * (degAt 𝓗.pow2 v : ℝ) + ξ * (n : ℝ) - (degAt Rabs v : ℝ) - (degAt R' v : ℝ) := by
  unfold fval
  have h := Int.floor_le (ρ * (degAt 𝓗.pow2 v : ℝ) + ξ * (n : ℝ)
    - (degAt Rabs v : ℝ) - (degAt R' v : ℝ))
  push_cast
  linarith

/-- The lower bound `f ≥ ρ d_G + ξn - d_{Rabs} - d_{R'} - 1`. -/
theorem fval_ge (𝓗 Rabs R' : Hypergraph (Fin n)) (ρ ξ : ℝ) (v : Fin n) :
    ρ * (degAt 𝓗.pow2 v : ℝ) + ξ * (n : ℝ) - (degAt Rabs v : ℝ) - (degAt R' v : ℝ) - 1 ≤
      (fval 𝓗 Rabs R' ρ ξ v : ℝ) := by
  unfold fval
  have h := Int.lt_floor_add_one (ρ * (degAt 𝓗.pow2 v : ℝ) + ξ * (n : ℝ)
    - (degAt Rabs v : ℝ) - (degAt R' v : ℝ))
  push_cast
  linarith

theorem sub_add_eq_of_le {a b : ℕ} (h : b ≤ a) : a - b + b = a := Nat.sub_add_cancel h

/-! ## The pointwise estimates -/

/-- The degree of `x ∈ W` in `G[W] - Rabs - R'` is at least `(1-3ρ)n`. -/
theorem degIn_inducedSub_ge (𝓗 Rabs R' : Hypergraph (Fin n)) (W : Set (Fin n)) {ρ ξ : ℝ}
    (hξε : ξ ≤ ρ / 2) (x : Fin n) (hx : x ∈ W)
    (hdG : (1 - ρ) * (n : ℝ) ≤ (degAt 𝓗.pow2 x : ℝ))
    (hRA : (degAt Rabs x : ℝ) ≤ (ρ / 2 + ξ) * (n : ℝ))
    (hR' : (degAt R' x : ℝ) ≤ ρ * (n : ℝ) / 10)
    (hcW : ((Wᶜ).ncard : ℝ) ≤ ρ * (n : ℝ) / 10) :
    (1 - 3 * ρ) * (n : ℝ) ≤ (degIn (inducedSub 𝓗 (Rabs ∪ R') W) W x : ℝ) := by
  have h1 := degAt_inducedSub_lower 𝓗 (Rabs ∪ R') W x hx
  have h1' : (degAt 𝓗.pow2 x : ℝ) ≤
      (degAt (inducedSub 𝓗 (Rabs ∪ R') W) x : ℝ) + ((Wᶜ).ncard : ℝ) +
        (degAt (Rabs ∪ R') x : ℝ) := by exact_mod_cast h1
  have h2 : (degAt (Rabs ∪ R') x : ℝ) ≤ (degAt Rabs x : ℝ) + (degAt R' x : ℝ) := by
    have := degAt_union_le Rabs R' x
    exact_mod_cast this
  have h3 : (degIn (inducedSub 𝓗 (Rabs ∪ R') W) W x : ℝ) =
      (degAt (inducedSub 𝓗 (Rabs ∪ R') W) x : ℝ) := by
    rw [degIn_inducedSub_eq 𝓗 (Rabs ∪ R') hx]
  rw [h3]
  linarith [mul_le_mul_of_nonneg_right hξε (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]

/-- **The arithmetic of `(R1)`.** -/
theorem reg_R1_arith {dG dA dR1 dR2 fv gv ρ ξ N : ℝ}
    (hf_le : fv ≤ ρ * dG + ξ * N - dA - dR1)
    (hf_ge : ρ * dG + ξ * N - dA - dR1 - 1 ≤ fv)
    (hgv : gv = fv - 1) (hlo : gv ≤ dR2) (hup : dR2 ≤ fv) (h2 : 2 ≤ ξ * N) :
    |dA + dR1 + dR2 - ρ * dG| ≤ ξ * N := by
  rw [abs_le]
  constructor <;> linarith

/-- **The arithmetic of `(R2)` at a vertex of `U'`.** -/
theorem reg_R2_up_arith {dG dA dR1 dR2 fv gv ρ ξ N ε : ℝ}
    (hρ : 0 ≤ ρ) (hdGlo : (ρ - 20 * ε) * N ≤ ρ * dG)
    (hf_le : fv ≤ ρ * dG + ξ * N - dA - dR1)
    (hf_ge : ρ * dG + ξ * N - dA - dR1 - 1 ≤ fv)
    (hgv : gv = fv - 1) (hlo : gv ≤ dR2) (hup : dR2 ≤ fv) (h2 : 2 ≤ ξ * N)
    (hdGup : dG ≤ (1 - ε) * N) :
    max (ρ * dG) ((ρ - 20 * ε) * N) ≤ dA + dR1 + dR2 ∧
      dA + dR1 + dR2 ≤ ρ * (1 - ε) * N + ξ * N := by
  have h1 : ρ * dG + ξ * N - 2 ≤ dA + dR1 + dR2 := by linarith
  have h2' : dA + dR1 + dR2 ≤ ρ * dG + ξ * N := by linarith
  have h3 : ρ * dG ≤ ρ * ((1 - ε) * N) := mul_le_mul_of_nonneg_left hdGup hρ
  constructor
  · exact max_le (by linarith) (by linarith)
  · nlinarith [h2']

/-- **The arithmetic of `(R2)` at a vertex of `W₀`.** -/
theorem reg_R2_W0_arith {dG dA dR1 dR2 c ρ ξ N ε : ℝ}
    (hdR2 : dR2 = 0) (hsum : dA + dR1 = c) (hdG : ρ * dG ≤ c)
    (hlo : (ρ - 20 * ε) * N ≤ c) (hhi : c ≤ ρ * (1 - ε) * N + ξ * N) :
    max (ρ * dG) ((ρ - 20 * ε) * N) ≤ dA + dR1 + dR2 ∧
      dA + dR1 + dR2 ≤ ρ * (1 - ε) * N + ξ * N := by
  constructor
  · rw [hdR2, add_zero, hsum]; exact max_le hdG hlo
  · rw [hdR2, add_zero, hsum]; exact hhi

/-- The arithmetic of the ceiling `⌈(ρ-20ε)n⌉`. -/
theorem ceil_bounds {ε ρ N : ℝ} (hpos : 0 ≤ (ρ - 20 * ε) * N) (hεN : 1 ≤ ε * N)
    (hN : 0 ≤ N) (hρ100 : ρ ≤ 1 / 100) (hρ0 : 0 < ρ) :
    (ρ - 20 * ε) * N ≤ ((⌈(ρ - 20 * ε) * N⌉₊ : ℕ) : ℝ) ∧
      ((⌈(ρ - 20 * ε) * N⌉₊ : ℕ) : ℝ) ≤ (ρ - 20 * ε) * N + 1 ∧
      (ρ - 20 * ε) * N + 1 ≤ ρ * (1 - ε) * N := by
  refine ⟨Nat.le_ceil _, ?_, ?_⟩
  · have h := Nat.ceil_lt_add_one hpos
    push_cast at h
    linarith
  · nlinarith [hεN, hN, hρ100]

/-- `ρ * ((1 - 20ε/ρ) N) = (ρ - 20ε) N`. -/
theorem mul_one_sub_div (ρ ε N : ℝ) (hρ : 0 < ρ) :
    ρ * ((1 - 20 * ε / ρ) * N) = (ρ - 20 * ε) * N := by
  have h1 : ρ * (20 * ε / ρ) = 20 * ε := by field_simp
  rw [← mul_assoc, mul_sub, mul_one, h1]


/-- **Lemma 11.2 (`lem:reg_reservoir`)**: the existence of a regularising
reservoir.  If `𝓗` is an `n`-vertex hypergraph whose 2-graph is `(ρ,ε)`-full
and `Rabs` is a `(ρ/2, ξ, ξ, ε)`-absorber for `𝓥` (with `V(𝓗) ∈ 𝓥`), then
there is a `(ρ, ξ, ε, Rabs, 𝓥)`-regularising reservoir `Rreg ⊆ E(G) ∖ Rabs`,
where `G = 𝓗^{(2)}`. -/
theorem exists_regularising_reservoir (hgf : GFactorStatement)
    (𝓗 Rabs : Hypergraph (Fin n)) (𝓥 : Set (Set (Fin n)))
    (hVuniv : (Set.univ : Set (Fin n)) ∈ 𝓥)
    {ε ρ ξ : ℝ} (hε0 : 0 < ε) (hρ0 : 0 < ρ) (hξ0 : 0 < ξ)
    (hfull : IsFull 𝓗 ρ ε)
    (habs : IsAbsorber (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) Rabs 𝓥 (ρ / 2) ξ ξ)
    (hn1 : 1 ≤ n) (hεn : 1 ≤ ε * n) (h5εn : 1 ≤ 5 * ε * n)
    (hρ100 : ρ ≤ 1 / 100) (hρn : 25 ≤ ρ * n)
    (hερ : 20 * ε ≤ ρ ^ 2) (h20 : 20 * ε + ξ ≤ ρ / 2) (hξε : ξ ≤ ρ / 2)
    (hξn : 2 ≤ ξ * n) :
    ∃ Rreg : Hypergraph (Fin n), Rreg ⊆ 𝓗.pow2 ∧ Disjoint Rreg Rabs ∧
      IsRegularising 𝓗 Rabs Rreg ρ ξ ε := by
  classical
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hξε' : ε ≤ ρ := by linarith
  -- #### The absorber's degree bound (cond:deg_abs)
  have hdegabs : ∀ v : Fin n,
      (degAt Rabs v : ℝ) ≤ (ρ / 2) * (degAt 𝓗.pow2 v : ℝ) + ξ * (n : ℝ) := by
    intro v
    refine absorber_degAt_le (ρ := ρ / 2) (by linarith) hVuniv ?_ habs.2.1 v
    intro e he
    exact he.1
  have hRA0 : ∀ w : Fin n, (degAt Rabs w : ℝ) ≤ (ρ / 2 + ξ) * (n : ℝ) := by
    intro w
    have h1 := hdegabs w
    have h2 : (degAt 𝓗.pow2 w : ℝ) ≤ (n : ℝ) := by exact_mod_cast degAt_le_n (𝓗.pow2) w
    nlinarith [h1, h2, hρ0]
  -- #### `|W₀| ≤ ρn/10`
  have hUncard : (1 - 10 * ε) * (n : ℝ) ≤ ((Vplus 𝓗 (1 - ε)).ncard : ℝ) := hfull.1
  have hW0le : ((W0F 𝓗 ε ρ).card : ℝ) ≤ ρ * (n : ℝ) / 10 := by
    have h1 : ((W0F 𝓗 ε ρ).card : ℝ) = (((WsetOf 𝓗 ε ρ)ᶜ).ncard : ℝ) := by
      rw [W0F, card_complFinset]
    have h2 : ((WsetOf 𝓗 ε ρ)ᶜ).ncard ≤ ((Vplus 𝓗 (1 - ε))ᶜ).ncard := by
      refine Set.ncard_le_ncard ?_ (Set.toFinite _)
      intro x hx
      rw [Set.mem_compl_iff] at hx ⊢
      intro hxU
      exact hx ((mem_WsetOf).mpr (Or.inl hxU))
    have h3 : (((Vplus 𝓗 (1 - ε))ᶜ).ncard : ℝ) ≤ 10 * ε * (n : ℝ) :=
      ncard_compl_le _ hUncard
    have h4 : 10 * ε * (n : ℝ) ≤ ρ * (n : ℝ) / 10 := by
      have h5 : 10 * ε ≤ ρ / 10 := by nlinarith [hερ, hρ100, hρ0]
      nlinarith [h5, hnR]
    have h5 : (((WsetOf 𝓗 ε ρ)ᶜ).ncard : ℝ) ≤ (((Vplus 𝓗 (1 - ε))ᶜ).ncard : ℝ) := by
      exact_mod_cast h2
    rw [h1]
    linarith
  have hWcW : (((WsetOf 𝓗 ε ρ)ᶜ).ncard : ℝ) ≤ ρ * (n : ℝ) / 10 := by
    have h1 : ((W0F 𝓗 ε ρ).card : ℝ) = (((WsetOf 𝓗 ε ρ)ᶜ).ncard : ℝ) := by
      rw [W0F, card_complFinset]
    rw [h1] at hW0le
    exact hW0le
  -- #### The clique `S`
  have hcardS : ⌈(ρ - 20 * ε) * (n : ℝ)⌉₊ ≤ (degExactly 𝓗 (n - 1)).card := by
    rw [← Set.ncard_coe_finset (s := degExactly 𝓗 (n - 1)), coe_degExactly]
    refine Nat.ceil_le.mpr ?_
    have h2 : (ρ - 15 * ε) * (n : ℝ) ≤ ((VeqNat 𝓗 (n - 1)).ncard : ℝ) := hfull.2
    nlinarith [h2, hnR, h5εn]
  obtain ⟨S, hSdeg, hScard⟩ := exists_clique_finset 𝓗 hcardS
  have hSsubU : ∀ s ∈ S, s ∈ Vplus 𝓗 (1 - ε) := by
    intro s hs
    refine VeqNat_subset_Vplus 𝓗 hεn ?_
    simp only [VeqNat, Set.mem_setOf_eq]
    exact hSdeg s hs
  have hW0S : ∀ w ∈ W0F 𝓗 ε ρ, w ∉ S := by
    intro w hw hs
    have h1 : w ∉ WsetOf 𝓗 ε ρ := (mem_W0F).mp hw
    exact h1 ((mem_WsetOf).mpr (Or.inl (hSsubU w hs)))
  have hclique : ∀ s ∈ S, ∀ t : Fin n, t ≠ s → ({s, t} : Set (Fin n)) ∈ 𝓗.pow2 :=
    fun s hs t ht => clique_of_degAt 𝓗 (hSdeg s hs) ht
  have havil : ∀ w ∈ W0F 𝓗 ε ρ, mval Rabs ε ρ w + degAt Rabs w ≤ S.card := by
    intro w hw
    have h1 : (degAt Rabs w : ℝ) ≤ ((⌈(ρ - 20 * ε) * (n : ℝ)⌉₊ : ℕ) : ℝ) := by
      have h2 := hRA0 w
      have h3 : (ρ / 2 + ξ) * (n : ℝ) ≤ (ρ - 20 * ε) * (n : ℝ) := by
        have h4 : ρ / 2 + ξ ≤ ρ - 20 * ε := by linarith
        nlinarith [h4, hnR]
      linarith [Nat.le_ceil ((ρ - 20 * ε) * (n : ℝ))]
    have h5 : degAt Rabs w ≤ ⌈(ρ - 20 * ε) * (n : ℝ)⌉₊ := by exact_mod_cast h1
    rw [mval, sub_add_eq_of_le h5]
    omega
  obtain ⟨R', hR'sub, hR'disj, hR'deg, hR'far⟩ :=
    exists_reservoir_subfamily 𝓗 Rabs S (W0F 𝓗 ε ρ) (mval Rabs ε ρ) hclique hW0S havil
  -- #### Pointwise estimates on `W`
  have hdGet : ∀ x ∈ WsetOf 𝓗 ε ρ, (1 - ρ) * (n : ℝ) ≤ (degAt 𝓗.pow2 x : ℝ) := by
    intro x hx
    rcases (mem_WsetOf).mp hx with hxU | hxUp
    · have h1 : (1 - ε) * (n : ℝ) ≤ (degAt 𝓗.pow2 x : ℝ) := hxU
      nlinarith [h1, hnR, hξε', hρ0]
    · have h1 : (1 - 20 * ε / ρ) * (n : ℝ) ≤ (degAt 𝓗.pow2 x : ℝ) := (mem_UpSet).mp hxUp |>.2
      have h2 : 20 * ε / ρ ≤ ρ := by
        rw [div_le_iff₀ hρ0]
        nlinarith [hερ]
      nlinarith [h1, hnR, h2]
  have hRAet : ∀ x ∈ WsetOf 𝓗 ε ρ, (degAt Rabs x : ℝ) ≤ (ρ / 2 + ξ) * (n : ℝ) :=
    fun x _ => hRA0 x
  have hR'et : ∀ x ∈ WsetOf 𝓗 ε ρ, (degAt R' x : ℝ) ≤ ρ * (n : ℝ) / 10 := by
    intro x hx
    have h1 : x ∉ W0F 𝓗 ε ρ := fun h => (mem_W0F).mp h hx
    have h2 : (degAt R' x : ℝ) ≤ ((W0F 𝓗 ε ρ).card : ℝ) := by exact_mod_cast hR'far x h1
    linarith [hW0le]
  have hf_lo : ∀ x ∈ WsetOf 𝓗 ε ρ, ρ * (n : ℝ) / 4 ≤ (fval 𝓗 Rabs R' ρ ξ x : ℝ) :=
    fun x hx => floor_ge_quarter hρ0 (hdGet x hx) (hRAet x hx) (hR'et x hx) hρ100 hρn
  have hf_hi : ∀ x ∈ WsetOf 𝓗 ε ρ, (fval 𝓗 Rabs R' ρ ξ x : ℝ) ≤ 3 * ρ * (n : ℝ) / 2 :=
    fun x hx => floor_le_three_halves hρ0.le hnR
      (by exact_mod_cast degAt_le_n (𝓗.pow2) x) (by positivity) (by positivity) hξε
  have hdH : ∀ x ∈ WsetOf 𝓗 ε ρ,
      (1 - 3 * ρ) * (n : ℝ) ≤
        (degIn (inducedSub 𝓗 (Rabs ∪ R') (WsetOf 𝓗 ε ρ)) (WsetOf 𝓗 ε ρ) x : ℝ) :=
    fun x hx => degIn_inducedSub_ge 𝓗 Rabs R' (WsetOf 𝓗 ε ρ) hξε x hx
      (hdGet x hx) (hRAet x hx) (hR'et x hx) hWcW
  -- #### Applying Lovász's `(g,f)`-factor theorem
  have htwo : ∀ e ∈ inducedSub 𝓗 (Rabs ∪ R') (WsetOf 𝓗 ε ρ), edgeSize e = 2 := by
    intro e he
    exact he.1.2
  have hgnonneg : ∀ x ∈ WsetOf 𝓗 ε ρ, 0 ≤ fval 𝓗 Rabs R' ρ ξ x - 1 := by
    intro x hx
    have h1 := hf_lo x hx
    have h2 : (1 : ℝ) ≤ (fval 𝓗 Rabs R' ρ ξ x : ℝ) := by
      have h3 : (1 : ℝ) ≤ ρ * (n : ℝ) / 4 := by
        have h4 : (1 : ℝ) ≤ ρ * (n : ℝ) := by linarith [hρn]
        linarith
      linarith
    have h5 : (1 : ℤ) ≤ fval 𝓗 Rabs R' ρ ξ x := by exact_mod_cast h2
    linarith
  have hglt : ∀ x ∈ WsetOf 𝓗 ε ρ, fval 𝓗 Rabs R' ρ ξ x - 1 < fval 𝓗 Rabs R' ρ ξ x :=
    fun x _ => by linarith
  have hfle : ∀ x ∈ WsetOf 𝓗 ε ρ,
      fval 𝓗 Rabs R' ρ ξ x ≤
        (degIn (inducedSub 𝓗 (Rabs ∪ R') (WsetOf 𝓗 ε ρ)) (WsetOf 𝓗 ε ρ) x : ℤ) := by
    intro x hx
    have h1 := hf_hi x hx
    have h2 := hdH x hx
    have h3 : 3 * ρ * (n : ℝ) / 2 ≤ (1 - 3 * ρ) * (n : ℝ) := by nlinarith [hnR, hρ100]
    exact_mod_cast (show (fval 𝓗 Rabs R' ρ ξ x : ℝ) ≤
      (degIn (inducedSub 𝓗 (Rabs ∪ R') (WsetOf 𝓗 ε ρ)) (WsetOf 𝓗 ε ρ) x : ℝ) by linarith)
  have hcond : ∀ S' T' : Finset (Fin n),
      (∀ x ∈ S', x ∈ WsetOf 𝓗 ε ρ) → (∀ x ∈ T', x ∈ WsetOf 𝓗 ε ρ) → Disjoint S' T' →
      (edgeCount (inducedSub 𝓗 (Rabs ∪ R') (WsetOf 𝓗 ε ρ)) S' T' : ℤ) ≤
        (∑ s ∈ S', fval 𝓗 Rabs R' ρ ξ s) +
          ∑ t ∈ T', ((degIn (inducedSub 𝓗 (Rabs ∪ R') (WsetOf 𝓗 ε ρ))
            (WsetOf 𝓗 ε ρ) t : ℤ) - (fval 𝓗 Rabs R' ρ ξ t - 1)) :=
    lovasz_condition (inducedSub 𝓗 (Rabs ∪ R') (WsetOf 𝓗 ε ρ)) (WsetOf 𝓗 ε ρ)
      (fval 𝓗 Rabs R' ρ ξ) (fun w => fval 𝓗 Rabs R' ρ ξ w - 1)
      hρ0 (by linarith) (by linarith) (fun _ => rfl) hf_lo hf_hi hdH
  obtain ⟨R'', hR''sub, hR''edges, hR''deg⟩ :=
    hgf (inducedSub 𝓗 (Rabs ∪ R') (WsetOf 𝓗 ε ρ)) (WsetOf 𝓗 ε ρ)
      (fval 𝓗 Rabs R' ρ ξ) (fun w => fval 𝓗 Rabs R' ρ ξ w - 1)
      htwo hgnonneg hglt hfle hcond
  -- #### Assembly
  have hR''disj : ∀ e ∈ R'', e ∉ Rabs ∪ R' := fun e he => (hR''sub he).2.2
  have hdisjR'R'' : Disjoint R' R'' := by
    rw [Set.disjoint_left]
    intro e he1 he2
    exact hR''disj e he2 (Or.inr he1)
  have hdisjAbsR'' : Disjoint Rabs R'' := by
    rw [Set.disjoint_left]
    intro e he1 he2
    exact hR''disj e he2 (Or.inl he1)
  have hdisjAbsR' : Disjoint Rabs R' := hR'disj.symm
  have hdisjAbsReg : Disjoint Rabs (R' ∪ R'') := by
    rw [Set.disjoint_left]
    intro e he1 he2
    rcases he2 with he2 | he2
    · exact Set.disjoint_left.mp hdisjAbsR' he1 he2
    · exact hR''disj e he2 (Or.inl he1)
  have hadd : ∀ v : Fin n, degAt (Rabs ∪ (R' ∪ R'')) v = degAt Rabs v + degAt R' v + degAt R'' v := by
    intro v
    rw [degAt_union hdisjAbsReg v, degAt_union hdisjR'R'' v]
    ring
  refine ⟨(R' ∪ R''), ?_, hdisjAbsReg.symm, ?_⟩
  · intro e he
    rcases he with he | he
    · exact hR'sub he
    · exact inducedSub_subset 𝓗 (Rabs ∪ R') (WsetOf 𝓗 ε ρ) (hR''sub he)
  · refine ⟨?_, ?_⟩
    · -- (R1)
      intro v hv
      have hvW : v ∈ WsetOf 𝓗 ε ρ := (mem_WsetOf).mpr (Or.inl hv)
      have hReq : degIn R'' (WsetOf 𝓗 ε ρ) v = degAt R'' v :=
        degIn_eq_degAt_of_subset hR''edges hvW
      have hup := (hR''deg v hvW).2
      have hup' : (degAt R'' v : ℝ) ≤ (fval 𝓗 Rabs R' ρ ξ v : ℝ) := by
        rw [← hReq]; exact_mod_cast hup
      have hlo := (hR''deg v hvW).1
      have hlo' : ((fval 𝓗 Rabs R' ρ ξ v - 1 : ℤ) : ℝ) ≤ (degAt R'' v : ℝ) := by
        rw [← hReq]; exact_mod_cast hlo
      have h2 : (2 : ℝ) ≤ ξ * (n : ℝ) := by exact_mod_cast hξn
      rw [hadd v]
      push_cast
      refine reg_R1_arith (fv := (fval 𝓗 Rabs R' ρ ξ v : ℝ))
        (gv := ((fval 𝓗 Rabs R' ρ ξ v - 1 : ℤ) : ℝ)) ?_ ?_ ?_ hlo' hup' h2
      · exact fval_le 𝓗 Rabs R' ρ ξ v
      · exact fval_ge 𝓗 Rabs R' ρ ξ v
      · push_cast; ring
    · -- (R2)
      intro w hwU
      have hwUp_or : w ∈ UpSet 𝓗 ε ρ ∨ w ∉ UpSet 𝓗 ε ρ := em _
      rcases hwUp_or with hwUp | hwUp
      · -- `w ∈ U'`
        have hwW : w ∈ WsetOf 𝓗 ε ρ := (mem_WsetOf).mpr (Or.inr hwUp)
        have hdGv : (1 - 20 * ε / ρ) * (n : ℝ) ≤ (degAt 𝓗.pow2 w : ℝ) :=
          (mem_UpSet).mp hwUp |>.2
        have hReq : degIn R'' (WsetOf 𝓗 ε ρ) w = degAt R'' w :=
          degIn_eq_degAt_of_subset hR''edges hwW
        have hup := (hR''deg w hwW).2
        have hup' : (degAt R'' w : ℝ) ≤ (fval 𝓗 Rabs R' ρ ξ w : ℝ) := by
          rw [← hReq]; exact_mod_cast hup
        have hlo := (hR''deg w hwW).1
        have hlo' : ((fval 𝓗 Rabs R' ρ ξ w - 1 : ℤ) : ℝ) ≤ (degAt R'' w : ℝ) := by
          rw [← hReq]; exact_mod_cast hlo
        have h2 : (2 : ℝ) ≤ ξ * (n : ℝ) := by exact_mod_cast hξn
        have hdGlo : (ρ - 20 * ε) * (n : ℝ) ≤ ρ * (degAt 𝓗.pow2 w : ℝ) := by
          rw [← mul_one_sub_div ρ ε (n : ℝ) hρ0]
          exact mul_le_mul_of_nonneg_left hdGv hρ0.le
        have hdGup : (degAt 𝓗.pow2 w : ℝ) ≤ (1 - ε) * (n : ℝ) := by
          by_contra hcon
          exact hwU (le_of_lt (not_le.mp hcon))
        rw [hadd w]
        push_cast
        refine reg_R2_up_arith (hρ := hρ0.le) (fv := (fval 𝓗 Rabs R' ρ ξ w : ℝ))
          (gv := ((fval 𝓗 Rabs R' ρ ξ w - 1 : ℤ) : ℝ)) hdGlo ?_ ?_ ?_ hlo' hup' h2 hdGup
        · exact fval_le 𝓗 Rabs R' ρ ξ w
        · exact fval_ge 𝓗 Rabs R' ρ ξ w
        · push_cast; ring
      · -- `w ∈ W₀`
        have hw0 : w ∈ W0F 𝓗 ε ρ := (mem_W0F).mpr (fun h => h.elim hwU hwUp)
        have hdGlt : (degAt 𝓗.pow2 w : ℝ) < (1 - 20 * ε / ρ) * (n : ℝ) := by
          by_contra hcon
          exact hwUp ((mem_UpSet).mpr ⟨hwU, not_lt.mp hcon⟩)
        have hR''zero : degAt R'' w = 0 := by
          have hempty : nbrs R'' w = ∅ := by
            ext x
            constructor
            · intro hx
              have h1 : ({w, x} : Set (Fin n)) ∈ R'' := hx
              exact absurd (hR''edges _ h1 (by simp)) ((mem_W0F).mp hw0)
            · intro hx
              exact absurd hx (by simp)
          simp only [degAt, hempty, Set.ncard_empty]
        have hR'w : degAt R' w = mval Rabs ε ρ w := hR'deg w hw0
        have hceil := ceil_bounds (ε := ε) (ρ := ρ) (N := (n : ℝ)) ?_ hεn hnR hρ100 hρ0
        · obtain ⟨hc1, hc2, hc3⟩ := hceil
          have hdAceil : (degAt Rabs w : ℝ) ≤ ((⌈(ρ - 20 * ε) * (n : ℝ)⌉₊ : ℕ) : ℝ) := by
            have h2 := hRA0 w
            have h3 : (ρ / 2 + ξ) * (n : ℝ) ≤ (ρ - 20 * ε) * (n : ℝ) := by
              have h4 : ρ / 2 + ξ ≤ ρ - 20 * ε := by linarith
              nlinarith [h4, hnR]
            linarith [hc1]
          have hdAceilN : degAt Rabs w ≤ ⌈(ρ - 20 * ε) * (n : ℝ)⌉₊ := by exact_mod_cast hdAceil
          have hsum : (degAt Rabs w : ℝ) + (mval Rabs ε ρ w : ℝ) =
              ((⌈(ρ - 20 * ε) * (n : ℝ)⌉₊ : ℕ) : ℝ) := by
            rw [mval, Nat.cast_sub hdAceilN]
            ring
          have hdGlo : ρ * (degAt 𝓗.pow2 w : ℝ) ≤
              ((⌈(ρ - 20 * ε) * (n : ℝ)⌉₊ : ℕ) : ℝ) := by
            have h4 : ρ * (degAt 𝓗.pow2 w : ℝ) < (ρ - 20 * ε) * (n : ℝ) := by
              rw [← mul_one_sub_div ρ ε (n : ℝ) hρ0]
              exact mul_lt_mul_of_pos_left hdGlt hρ0
            linarith [hc1]
          have hhi : ((⌈(ρ - 20 * ε) * (n : ℝ)⌉₊ : ℕ) : ℝ) ≤
              ρ * (1 - ε) * (n : ℝ) + ξ * (n : ℝ) := by
            have hξn0 : (0 : ℝ) ≤ ξ * (n : ℝ) := mul_nonneg hξ0.le hnR
            linarith [hc2, hc3]
          have hgoal := reg_R2_W0_arith (dG := (degAt 𝓗.pow2 w : ℝ))
            (dA := (degAt Rabs w : ℝ)) (dR1 := (mval Rabs ε ρ w : ℝ))
            (dR2 := (0 : ℝ)) (c := ((⌈(ρ - 20 * ε) * (n : ℝ)⌉₊ : ℕ) : ℝ))
            rfl hsum hdGlo hc1 hhi
          rw [hadd w, hR'w, hR''zero]
          push_cast
          exact hgoal
        · have : (0 : ℝ) ≤ (ρ - 20 * ε) * (n : ℝ) := by nlinarith [h20, hnR, hρ0]
          exact this


end

end ErdosFaberLovaszConjecture
