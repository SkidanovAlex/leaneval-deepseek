import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.EFL.EmbedProof
import Submission.Work.Deep.Nibble.exists_linear_regular_uniform
import Submission.Work.Deep.Kahn.sum_edgeSize_eq_sum_degree
import Submission.Work.Deep.Nibble.EmbedUnif

/-!
# The embedding lemma `lem:embed`: auxiliary vocabulary

This module sets up the vocabulary for the proof of
`ErdosFaberLovaszConjecture.EmbedStatement` (Lemma `lem:embed` of
Kang–Kelly–Kühn–Methuku–Osthus, §8), in the multi-hypergraph language of
`Submission.EFL.Embed`.

The construction has three layers.

* `Clone` — the **generic gluing** (`Clone.glue`): given a hypergraph `𝓗` on a
  finite type `V` and, for each `u : V`, a hypergraph `des u` on the `T` clones
  of `u`, the family on `Fin T × V` consisting of the `T` copies of every edge
  of `𝓗` together with the glued designs.  `Clone.glue_ncard`,
  `Clone.glue_linear` and `Clone.glue_deg` give uniformity, linearity and the
  exact degrees.

* `UnifData` — the output of the *uniformisation step*
  (`ErdosFaberLovaszConjecture.exists_uniform_extension`): an `r`-uniform linear
  `𝓖` on `Fin U.M` with an injection `ι : Fin N ↪ Fin U.M`, an embedding
  `e ↦ ext e` of the proper edges of `𝓗` with `ext e ∩ range ι = ι '' e`, and
  `U.M ≤ N + r·#𝓗.edges`.

* `SC`, `Vstar`, `old`, `ext`, `extS`, `Hstar` — the multi-hypergraph `𝓗*` of
  step 1 of the proof: the vertex set is `Vstar 𝓗 r U.M = Fin U.M ⊕ Σ p : SC 𝓗,
  Fin (r-1)`, where `SC 𝓗` indexes the *copies* of the singleton edges
  (`p : SC 𝓗` is a pair `(v,k)` with `k < 𝓗.singles v`); the edges are the
  uniform extensions `ext e` of the proper edges of `𝓗` (living in `Fin U.M`)
  together with the `r`-edges `extS p = {old p.1.1} ∪ (r-1 fresh vertices)`.

-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

variable {V : Type*}

/-! ## The generic gluing construction -/

/-- The `T` **copies** of a hypergraph `𝓗` on `V`, as a hypergraph on
`Fin T × V`: the image of every edge under the embeddings `u ↦ (i,u)`. -/
def Clone.copies (T : ℕ) (𝓗 : Set (Set V)) : Set (Set (Fin T × V)) :=
  {f | ∃ g ∈ 𝓗, ∃ i : Fin T, f = (fun u => (i, u)) '' g}

/-- The **designs** glued at the vertices of `V`: for every `u`, the edges of
`des u` (a hypergraph on the `T` clones of `u`) transported to `Fin T × {u}`. -/
def Clone.glued (T : ℕ) (des : V → Set (Set (Fin T))) : Set (Set (Fin T × V)) :=
  {f | ∃ u : V, ∃ E ∈ des u, f = (fun i : Fin T => (i, u)) '' E}

/-- The **gluing** of the copies of `𝓗` with the designs `des`. -/
def Clone.glue (T : ℕ) (𝓗 : Set (Set V)) (des : V → Set (Set (Fin T))) :
    Set (Set (Fin T × V)) := Clone.copies T 𝓗 ∪ Clone.glued T des

theorem Clone.mem_glue {T : ℕ} {𝓗 : Set (Set V)} {des : V → Set (Set (Fin T))}
    {f : Set (Fin T × V)} :
    f ∈ Clone.glue T 𝓗 des ↔
      (∃ g ∈ 𝓗, ∃ i : Fin T, f = (fun u => (i, u)) '' g) ∨
      (∃ u : V, ∃ E ∈ des u, f = (fun i : Fin T => (i, u)) '' E) := Iff.rfl

theorem Clone.image_inj (T : ℕ) (i : Fin T) : Function.Injective (fun u : V => (i, u)) :=
  fun a b hab => (Prod.ext_iff.mp hab).2

theorem Clone.image_inj' {T : ℕ} (u : V) : Function.Injective (fun i : Fin T => (i, u)) :=
  fun a b hab => (Prod.ext_iff.mp hab).1

/-- Every edge of a copy has the size of the copied edge. -/
theorem Clone.copies_ncard {T r : ℕ} {𝓗 : Set (Set V)} (h : ∀ g ∈ 𝓗, g.ncard = r)
    {f : Set (Fin T × V)} (hf : f ∈ Clone.copies T 𝓗) : f.ncard = r := by
  obtain ⟨g, hg, i, rfl⟩ := hf
  rw [Set.ncard_image_of_injective _ (Clone.image_inj T i), h g hg]

/-- Every glued design edge has the size of the design edge. -/
theorem Clone.glued_ncard {T r : ℕ} {des : V → Set (Set (Fin T))}
    (h : ∀ u, ∀ E ∈ des u, E.ncard = r)
    {f : Set (Fin T × V)} (hf : f ∈ Clone.glued T des) : f.ncard = r := by
  obtain ⟨u, E, hE, rfl⟩ := hf
  rw [Set.ncard_image_of_injective _ (Clone.image_inj' u), h u E hE]

/-- **Uniformity of the gluing.** -/
theorem Clone.glue_ncard {T r : ℕ} {𝓗 : Set (Set V)} {des : V → Set (Set (Fin T))}
    (h𝓗 : ∀ g ∈ 𝓗, g.ncard = r) (hdes : ∀ u, ∀ E ∈ des u, E.ncard = r) :
    ∀ f ∈ Clone.glue T 𝓗 des, f.ncard = r := by
  intro f hf
  rcases hf with h | h
  · exact Clone.copies_ncard h𝓗 h
  · exact Clone.glued_ncard hdes h

/-- **Linearity of the gluing.** -/
theorem Clone.glue_linear {T : ℕ} {𝓗 : Set (Set V)} {des : V → Set (Set (Fin T))}
    (h𝓗 : ∀ ⦃g⦄, g ∈ 𝓗 → ∀ ⦃g'⦄, g' ∈ 𝓗 → g ≠ g' → (g ∩ g').Subsingleton)
    (hdes : ∀ u, ∀ ⦃E⦄, E ∈ des u → ∀ ⦃E'⦄, E' ∈ des u → E ≠ E' →
      (E ∩ E').Subsingleton) :
    ∀ ⦃f⦄, f ∈ Clone.glue T 𝓗 des → ∀ ⦃f'⦄, f' ∈ Clone.glue T 𝓗 des → f ≠ f' →
      (f ∩ f').Subsingleton := by
  intro f hf f' hf' hne
  rcases hf with ⟨g, hg, i, rfl⟩ | ⟨u, E, hE, rfl⟩
  · rcases hf' with ⟨g', hg', j, rfl⟩ | ⟨u', E', hE', rfl⟩
    · by_cases hij : i = j
      · subst hij
        by_cases hgg : g = g'
        · subst hgg; exact absurd rfl hne
        · rw [← Set.image_inter (f := fun u => (i, u)) (Clone.image_inj T i)]
          exact (h𝓗 hg hg' hgg).image _
      · intro x hx y hy
        exfalso
        obtain ⟨a, _, ha⟩ := hx.1
        obtain ⟨b, _, hb⟩ := hx.2
        have h1 : i = x.1 := congrArg Prod.fst ha
        have h2 : j = x.1 := congrArg Prod.fst hb
        exact hij (h1.trans h2.symm)
    · intro x hx y hy
      have hsub : ∀ z ∈ (fun u' : V => (i, u')) '' g ∩ (fun i' : Fin T => (i', u')) '' E',
          z = (i, u') := by
        rintro _ ⟨⟨a, _, rfl⟩, ⟨b, _, hb⟩⟩
        have h2 : u' = a := congrArg Prod.snd hb
        simp [h2]
      exact (hsub x hx).trans (hsub y hy).symm
  · rcases hf' with ⟨g', hg', j, rfl⟩ | ⟨u', E', hE', rfl⟩
    · intro x hx y hy
      have hsub : ∀ z ∈ (fun i' : Fin T => (i', u)) '' E ∩ (fun u' : V => (j, u')) '' g',
          z = (j, u) := by
        rintro _ ⟨⟨b, _, hb⟩, ⟨a, _, rfl⟩⟩
        have h2 : u = a := congrArg Prod.snd hb
        simp [h2]
      exact (hsub x hx).trans (hsub y hy).symm
    · by_cases hu : u = u'
      · subst hu
        by_cases hEE : E = E'
        · subst hEE; exact absurd rfl hne
        · rw [← Set.image_inter (f := fun i' : Fin T => (i', u)) (Clone.image_inj' u)]
          exact (hdes u hE hE' hEE).image _
      · intro x hx y hy
        exfalso
        obtain ⟨a, _, ha⟩ := hx.1
        obtain ⟨b, _, hb⟩ := hx.2
        have h1 : u = x.2 := congrArg Prod.snd ha
        have h2 : u' = x.2 := congrArg Prod.snd hb
        exact hu (h1.trans h2.symm)

/-- A copy edge through `(i,u)` and a design edge through `(i,u)` are never the
same set, when both families are `r`-uniform with `r ≥ 2`. -/
theorem Clone.not_coincide {T r : ℕ} {g : Set V} {i : Fin T} {u : V}
    (hg : g.ncard = r) (hr : 2 ≤ r)
    {E : Set (Fin T)} (h : (fun u' : V => (i, u')) '' g = (fun i' : Fin T => (i', u)) '' E) :
    False := by
  have hsub : (fun u' : V => (i, u')) '' g ⊆ ({(i, u)} : Set (Fin T × V)) := by
    rintro _ ⟨u', hu', rfl⟩
    have hmem : (i, u') ∈ (fun i' : Fin T => (i', u)) '' E := by
      rw [← h]; exact ⟨u', hu', rfl⟩
    obtain ⟨i', _, hi'⟩ := hmem
    have hu'' : u' = u := (congrArg Prod.snd hi').symm
    simp [hu'']
  have hle : ((fun u' : V => (i, u')) '' g).ncard ≤ 1 := by
    have h2 := Set.ncard_le_ncard hsub (Set.finite_singleton _)
    have h1 : ({(i, u)} : Set (Fin T × V)).ncard = 1 := by simp
    rwa [h1] at h2
  have heq : ((fun u' : V => (i, u')) '' g).ncard = r := by
    rw [Set.ncard_image_of_injective _ (Clone.image_inj T i), hg]
  omega

/-- **The degrees of the gluing.**  Every vertex `(i,u)` of `Clone.glue T 𝓗 des`
lies in exactly `d_𝓗(u) + d_{des u}(i)` edges: the copies of the edges of `𝓗`
through `u`, plus the design edges at `u` through `i`.  The two contributions do
not overlap by `Clone.not_coincide`. -/
theorem Clone.glue_deg {T r : ℕ} [Fintype V] {𝓗 : Set (Set V)} {des : V → Set (Set (Fin T))}
    (hr : 2 ≤ r) (h𝓗 : ∀ g ∈ 𝓗, g.ncard = r) (hdes : ∀ u, ∀ E ∈ des u, E.ncard = r)
    (i : Fin T) (u : V) :
    ({f ∈ Clone.glue T 𝓗 des | (i, u) ∈ f} : Set (Set (Fin T × V))).ncard
      = ({g ∈ 𝓗 | u ∈ g} : Set (Set V)).ncard
        + ({E ∈ des u | i ∈ E} : Set (Set (Fin T))).ncard := by
  classical
  have hset : ({f ∈ Clone.glue T 𝓗 des | (i, u) ∈ f} : Set (Set (Fin T × V)))
      = ((fun g : Set V => (fun u' : V => (i, u')) '' g) '' {g ∈ 𝓗 | u ∈ g})
        ∪ ((fun E : Set (Fin T) => (fun i' : Fin T => (i', u)) '' E)
            '' {E ∈ des u | i ∈ E}) := by
    ext f
    constructor
    · rintro ⟨hf, hm⟩
      rcases hf with ⟨g, hg, j, rfl⟩ | ⟨u', E, hE, rfl⟩
      · left
        obtain ⟨a, ha, ha'⟩ := hm
        have h1 : j = i := congrArg Prod.fst ha'
        have h2 : a = u := congrArg Prod.snd ha'
        subst h1
        exact ⟨g, ⟨hg, by rwa [h2] at ha⟩, rfl⟩
      · right
        obtain ⟨b, hb, hb'⟩ := hm
        have h1 : b = i := congrArg Prod.fst hb'
        have h2 : u' = u := congrArg Prod.snd hb'
        subst h2
        exact ⟨E, ⟨hE, by rwa [h1] at hb⟩, rfl⟩
    · rintro (⟨g, ⟨hg, hug⟩, rfl⟩ | ⟨E, ⟨hE, hiE⟩, rfl⟩)
      · exact ⟨Or.inl ⟨g, hg, i, rfl⟩, ⟨u, hug, rfl⟩⟩
      · exact ⟨Or.inr ⟨u, E, hE, rfl⟩, ⟨i, hiE, rfl⟩⟩
  have hdisj : Disjoint ((fun g : Set V => (fun u' : V => (i, u')) '' g) '' {g ∈ 𝓗 | u ∈ g})
      ((fun E : Set (Fin T) => (fun i' : Fin T => (i', u)) '' E) '' {E ∈ des u | i ∈ E}) := by
    rw [Set.disjoint_left]
    rintro f ⟨g, ⟨hg, -⟩, rfl⟩ ⟨E, -, hEq⟩
    exact Clone.not_coincide (h𝓗 g hg) hr hEq.symm
  rw [hset, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ (Set.image_injective.mpr (Clone.image_inj (V := V) T i)),
    Set.ncard_image_of_injective _ (Set.image_injective.mpr (Clone.image_inj' u))]

variable {N r M : ℕ}

/-! ## The uniformisation datum -/

/-- The output of the uniformisation step of `lem:embed`
(`ErdosFaberLovaszConjecture.exists_uniform_extension`): an `r`-uniform linear
hypergraph `𝓖` on `Fin M` in which every proper edge `e` of `𝓗` has a unique
"extension" `e'` with `e' ∩ range ι = ι '' e`. -/
structure UnifData (N r : ℕ) (𝓗 : MultiHypergraph N) where
  /-- The number of vertices. -/
  M : ℕ
  /-- The embedding of the old vertices. -/
  ι : Fin N ↪ Fin M
  /-- The uniform extension of the proper edges. -/
  𝓖 : Set (Set (Fin M))
  /-- `𝓖` is `r`-uniform. -/
  unif : ∀ e ∈ 𝓖, edgeSize e = r
  /-- `𝓖` is linear. -/
  lin : Hypergraph.IsLinear 𝓖
  /-- Every proper edge of `𝓗` has a unique extension meeting `ι '' Fin N`. -/
  uniq : ∀ e ∈ 𝓗.edges, ∃! e' ∈ 𝓖, e' ∩ Set.range ι = ι '' e
  /-- Every fresh vertex (one outside `Set.range ι`) lies in at most one edge of
  `𝓖`.  This is not implied by the other fields (a family of edges all meeting
  `range ι` with the prescribed degrees at the old vertices may still have a
  fresh vertex of degree two), but is a property of the *construction*; it is
  what makes the degree of `𝓗*` at a fresh vertex controllable. -/
  freshdeg : ∀ w : Fin M, w ∉ Set.range ι →
    ({g : Set (Fin M) | g ∈ 𝓖 ∧ w ∈ g} : Set (Set (Fin M))).ncard ≤ 1
  /-- The vertex bound `M ≤ N + r·#E(𝓗)`. -/
  bound : (M : ℝ) ≤ (N : ℝ) + (r : ℝ) * ((𝓗.edges).ncard : ℝ)

/-- **The uniformisation step** of `lem:embed` (imported from the cone). -/
theorem exists_unifData {N r : ℕ} (𝓗 : MultiHypergraph N) (hr : 2 ≤ r)
    (hlin : 𝓗.IsLinear) (hsize : ∀ e ∈ 𝓗.edges, edgeSize e ≤ r) :
    Nonempty (UnifData N r 𝓗) := by
  obtain ⟨M, ι, 𝓖, hunif, hlin', huniq, hmeet, hdeg, hfresh, hbound⟩ :=
    exists_uniform_extension' (𝓗 := 𝓗.edges) (r := r) hr hlin.2 hlin.1 hsize
  exact ⟨⟨M, ι, 𝓖, hunif, hlin', huniq, hfresh, hbound⟩⟩

/-! ## The vertex set of `𝓗*` -/

/-- The index set of the **copies** of the singleton edges of `𝓗`: a pair
`(v,k)` with `k < 𝓗.singles v` indexes one copy of the singleton `{v}`. -/
abbrev SC {N : ℕ} (𝓗 : MultiHypergraph N) : Type := {p : Fin N × ℕ // p.2 < 𝓗.singles p.1}

/-- `SC 𝓗` is the `Σ`-type of the singleton multiplicities. -/
def SC.equiv {N : ℕ} (𝓗 : MultiHypergraph N) :
    SC 𝓗 ≃ (Σ v : Fin N, Fin (𝓗.singles v)) where
  toFun p := ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  invFun q := ⟨(q.1, q.2.1), q.2.2⟩
  left_inv := by rintro ⟨⟨v, k⟩, hk⟩; rfl
  right_inv := by rintro ⟨v, ⟨k, hk⟩⟩; rfl

instance {N : ℕ} (𝓗 : MultiHypergraph N) : Fintype (SC 𝓗) :=
  Fintype.ofEquiv _ (SC.equiv 𝓗).symm

/-- The number of singleton copies is the sum of the multiplicities. -/
theorem SC.card {N : ℕ} (𝓗 : MultiHypergraph N) :
    Nat.card (SC 𝓗) = ∑ v : Fin N, 𝓗.singles v := by
  rw [Nat.card_congr (SC.equiv 𝓗), Nat.card_sigma]
  exact Finset.sum_congr rfl fun v _ => Nat.card_fin _

/-- The vertex set of `𝓗*`: the vertices of `𝓖` (old vertices and the fresh
vertices of the proper-edge extensions), together with `r - 1` fresh vertices
for every singleton copy. -/
abbrev Vstar {N : ℕ} (𝓗 : MultiHypergraph N) (r M : ℕ) : Type :=
  Fin M ⊕ (Σ _p : SC 𝓗, Fin (r - 1))

instance {N : ℕ} (𝓗 : MultiHypergraph N) (r M : ℕ) : Fintype (Vstar 𝓗 r M) :=
  inferInstanceAs (Fintype (Fin M ⊕ (Σ _p : SC 𝓗, Fin (r - 1))))

/-- The cardinality of `Vstar`. -/
theorem Vstar.card {N r M : ℕ} (𝓗 : MultiHypergraph N) :
    Nat.card (Vstar 𝓗 r M) = M + Nat.card (SC 𝓗) * (r - 1) := by
  have h1 : Nat.card (Σ _p : SC 𝓗, Fin (r - 1)) = ∑ _p : SC 𝓗, (r - 1) := by
    rw [Nat.card_sigma]
    exact Finset.sum_congr rfl fun p _ => Nat.card_fin _
  rw [Vstar, Nat.card_sum, h1, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card]
  simp only [Fintype.card_fin, Nat.card_eq_fintype_card]

/-- The embedding of the old vertices in `Vstar 𝓗 r U.M`. -/
def old {N r : ℕ} {𝓗 : MultiHypergraph N} (U : UnifData N r 𝓗) :
    Fin N → Vstar 𝓗 r U.M := fun v => Sum.inl (U.ι v)

/-- The **uniform extension** of a proper edge of `𝓗`, as a subset of
`Vstar 𝓗 r U.M`. -/
def ext {N r : ℕ} {𝓗 : MultiHypergraph N} (U : UnifData N r 𝓗)
    (e : {e : Set (Fin N) // e ∈ 𝓗.edges}) : Set (Vstar 𝓗 r U.M) :=
  Sum.inl '' (Classical.choose (U.uniq e.1 e.2))

/-- The defining properties of the chosen extension. -/
theorem ext_spec {N r : ℕ} {𝓗 : MultiHypergraph N} (U : UnifData N r 𝓗)
    (e : {e : Set (Fin N) // e ∈ 𝓗.edges}) :
    Classical.choose (U.uniq e.1 e.2) ∈ U.𝓖 ∧
      Classical.choose (U.uniq e.1 e.2) ∩ Set.range U.ι = U.ι '' e.1 :=
  (Classical.choose_spec (U.uniq e.1 e.2)).1

/-- The extension map is injective. -/
theorem ext_inj {N r : ℕ} {𝓗 : MultiHypergraph N} (U : UnifData N r 𝓗) :
    Function.Injective (ext U) := by
  intro e e' h
  simp only [ext] at h
  have h3 : Classical.choose (U.uniq e.1 e.2) = Classical.choose (U.uniq e'.1 e'.2) :=
    Set.image_injective.mpr Sum.inl_injective h
  have h4 : U.ι '' e.1 = U.ι '' e'.1 := by
    rw [← (ext_spec U e).2, ← (ext_spec U e').2, h3]
  exact Subtype.ext (Set.image_injective.mpr U.ι.injective h4)

theorem range_old {N r : ℕ} {𝓗 : MultiHypergraph N} (U : UnifData N r 𝓗) :
    Set.range (old U) = (Sum.inl : Fin U.M → Vstar 𝓗 r U.M) '' Set.range U.ι := by
  ext x; constructor
  · rintro ⟨v, rfl⟩; exact ⟨U.ι v, ⟨v, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨v, rfl⟩, rfl⟩; exact ⟨v, rfl⟩

theorem image_old {N r : ℕ} {𝓗 : MultiHypergraph N} (U : UnifData N r 𝓗) (S : Set (Fin N)) :
    old U '' S = (Sum.inl : Fin U.M → Vstar 𝓗 r U.M) '' (U.ι '' S) := by
  ext x; constructor
  · rintro ⟨v, hv, rfl⟩; exact ⟨U.ι v, ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩; exact ⟨v, hv, rfl⟩

/-- **The identification (E1) of a proper edge**: `ext e` meets the old
vertices exactly in `old '' e`. -/
theorem ext_inter_old {N r : ℕ} {𝓗 : MultiHypergraph N} (U : UnifData N r 𝓗)
    (e : {e : Set (Fin N) // e ∈ 𝓗.edges}) :
    ext U e ∩ Set.range (old U) = old U '' e.1 := by
  rw [range_old U, image_old U e.1, ext, ← Set.image_inter Sum.inl_injective, (ext_spec U e).2]

/-- The **extension of a singleton copy** `p = (v,k)`: `v` together with
`r - 1` fresh vertices private to `p`. -/
def extS {N r : ℕ} {𝓗 : MultiHypergraph N} (U : UnifData N r 𝓗) (p : SC 𝓗) :
    Set (Vstar 𝓗 r U.M) :=
  {old U p.1.1} ∪ Set.range (fun j : Fin (r - 1) => (Sum.inr ⟨p, j⟩ : Vstar 𝓗 r U.M))

theorem mem_extS {N r : ℕ} {𝓗 : MultiHypergraph N} (U : UnifData N r 𝓗) (p : SC 𝓗)
    {x : Vstar 𝓗 r U.M} :
    x ∈ extS U p ↔
      x = old U p.1.1 ∨ ∃ j : Fin (r - 1), (Sum.inr ⟨p, j⟩ : Vstar 𝓗 r U.M) = x := by
  simp only [extS, Set.mem_union, Set.mem_singleton_iff, Set.mem_range]

/-- `extS p` meets the old vertices exactly in `old p.1.1`. -/
theorem extS_inter_old {N r : ℕ} {𝓗 : MultiHypergraph N} (U : UnifData N r 𝓗) (p : SC 𝓗) :
    extS U p ∩ Set.range (old U) = {old U p.1.1} := by
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨⟨Or.inl rfl, Set.mem_range_self _⟩, ?_⟩
  rintro x ⟨hx, v, hv⟩
  have hx' : old U v ∈ extS U p := hv ▸ hx
  rcases (mem_extS U p).mp hx' with h | ⟨j, hj⟩
  · rw [← hv]; exact h
  · exact nomatch hj

/-- `extS p ∩ range Sum.inl = {old p.1.1}`. -/
theorem extS_inter_inl {N r : ℕ} {𝓗 : MultiHypergraph N} (U : UnifData N r 𝓗) (p : SC 𝓗) :
    extS U p ∩ Set.range (Sum.inl : Fin U.M → Vstar 𝓗 r U.M) = {old U p.1.1} := by
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨⟨Or.inl rfl, ⟨U.ι p.1.1, rfl⟩⟩, ?_⟩
  rintro x ⟨hx, y, hy⟩
  have hx' : (Sum.inl y : Vstar 𝓗 r U.M) ∈ extS U p := hy ▸ hx
  rcases (mem_extS U p).mp hx' with h | ⟨j, hj⟩
  · rw [← hy]; exact h
  · exact nomatch hj

/-- The singleton extensions are pairwise distinct. -/
theorem extS_inj {N r : ℕ} {𝓗 : MultiHypergraph N} (U : UnifData N r 𝓗) (hr : 2 ≤ r) :
    Function.Injective (extS U) := by
  intro p p' h
  have h0 : Fin (r - 1) := ⟨0, by omega⟩
  have hmem : (Sum.inr (⟨p, h0⟩ : Σ _p : SC 𝓗, Fin (r - 1)) : Vstar 𝓗 r U.M) ∈ extS U p :=
    Or.inr (Set.mem_range_self h0)
  rw [h] at hmem
  rcases (mem_extS U p').mp hmem with hc | ⟨j, hj⟩
  · exact nomatch hc
  · have h2 : (⟨p', j⟩ : Σ _p : SC 𝓗, Fin (r - 1)) = ⟨p, h0⟩ := Sum.inr_injective hj
    exact (Sigma.mk.inj_iff.mp h2).1.symm

/-- The **multi-hypergraph `𝓗*`** of step 1 of `lem:embed`: the extensions of
the proper edges and of the singleton copies. -/
def Hstar {N r : ℕ} {𝓗 : MultiHypergraph N} (U : UnifData N r 𝓗) :
    Set (Set (Vstar 𝓗 r U.M)) := Set.range (ext U) ∪ Set.range (extS U)

theorem mem_Hstar {N r : ℕ} {𝓗 : MultiHypergraph N} (U : UnifData N r 𝓗)
    {f : Set (Vstar 𝓗 r U.M)} :
    f ∈ Hstar U ↔ (∃ e, ext U e = f) ∨ (∃ p, extS U p = f) := by
  simp only [Hstar, Set.mem_union, Set.mem_range]

/-! ## The prescribed degrees and the glued designs -/

/-- The degree `d_{𝓗*}(u)` of a vertex `u` of `𝓗*`. -/
def HstarDeg {N r : ℕ} {𝓗 : MultiHypergraph N} (U : UnifData N r 𝓗)
    (u : Vstar 𝓗 r U.M) : ℕ := ({f ∈ Hstar U | u ∈ f} : Set (Set (Vstar 𝓗 r U.M))).ncard

/-- The prescribed degree of `𝓖` at every clone of `u`: `max d_{𝓗*}(u) ⌈D - C⌉₊`.
It is chosen so that it lies in `[D - C, D]` while never decreasing the degree of
`𝓗*` (so that no design is glued at a non-isolated old vertex strong enough to
disturb the degree there: those vertices already have `d_{𝓗*}(v) = d_𝓗(v) ≥ D - C`). -/
def mdeg {N r : ℕ} {𝓗 : MultiHypergraph N} (D C : ℝ) (U : UnifData N r 𝓗)
    (u : Vstar 𝓗 r U.M) : ℕ := max (HstarDeg U u) ⌈D - C⌉₊

/-- The degree of the design glued at the clones of `u`. -/
def dprime {N r : ℕ} {𝓗 : MultiHypergraph N} (D C : ℝ) (U : UnifData N r 𝓗)
    (u : Vstar 𝓗 r U.M) : ℕ := mdeg D C U u - HstarDeg U u

/-- The largest design degree over the vertices of `𝓗*`. -/
def dmax {N r : ℕ} {𝓗 : MultiHypergraph N} (D C : ℝ) (U : UnifData N r 𝓗) : ℕ :=
  (Finset.univ : Finset (Vstar 𝓗 r U.M)).sup fun u => dprime D C U u

theorem HstarDeg_def {N r : ℕ} {𝓗 : MultiHypergraph N} (U : UnifData N r 𝓗)
    (u : Vstar 𝓗 r U.M) :
    HstarDeg U u = ({f ∈ Hstar U | u ∈ f} : Set (Set (Vstar 𝓗 r U.M))).ncard := rfl

theorem dprime_le_dmax {N r : ℕ} {𝓗 : MultiHypergraph N} (D C : ℝ) (U : UnifData N r 𝓗)
    (u : Vstar 𝓗 r U.M) : dprime D C U u ≤ dmax D C U :=
  Finset.le_sup (Finset.mem_univ u)

theorem dmax_eq_zero_iff {N r : ℕ} {𝓗 : MultiHypergraph N} (D C : ℝ) (U : UnifData N r 𝓗) :
    dmax D C U = 0 ↔ ∀ u, dprime D C U u = 0 := by
  constructor
  · intro h u
    have := dprime_le_dmax D C U u
    omega
  · intro h
    have : dmax D C U ≤ 0 := Finset.sup_le_iff.mpr fun u _ => le_of_eq (h u)
    omega

theorem dprime_eq_zero_iff {N r : ℕ} {𝓗 : MultiHypergraph N} (D C : ℝ) (U : UnifData N r 𝓗)
    (u : Vstar 𝓗 r U.M) :
    dprime D C U u = 0 ↔ ⌈D - C⌉₊ ≤ HstarDeg U u := by
  rw [dprime, Nat.sub_eq_zero_iff_le, mdeg, max_le_iff]
  exact ⟨fun h => h.2, fun h => ⟨le_rfl, h⟩⟩

theorem mdeg_eq_hstarDeg_of_le {N r : ℕ} {𝓗 : MultiHypergraph N} (D C : ℝ)
    (U : UnifData N r 𝓗) {u : Vstar 𝓗 r U.M} (h : ⌈D - C⌉₊ ≤ HstarDeg U u) :
    mdeg D C U u = HstarDeg U u := max_eq_left h

/-- A prime strictly larger than `max r dmax`. -/
theorem max_r_dmax_ne_zero {N r : ℕ} {𝓗 : MultiHypergraph N} (hr : 3 ≤ r) (D C : ℝ)
    (U : UnifData N r 𝓗) : max r (dmax D C U) ≠ 0 := by
  have : 1 ≤ max r (dmax D C U) := le_trans (by omega) (le_max_left _ _)
  omega

def designPrime {N r : ℕ} {𝓗 : MultiHypergraph N} (hr : 3 ≤ r) (D C : ℝ)
    (U : UnifData N r 𝓗) : ℕ :=
  Classical.choose (Nat.exists_prime_lt_and_le_two_mul (max r (dmax D C U))
    (max_r_dmax_ne_zero hr D C U))

theorem designPrime_prime {N r : ℕ} {𝓗 : MultiHypergraph N} (hr : 3 ≤ r) (D C : ℝ)
    (U : UnifData N r 𝓗) : Nat.Prime (designPrime hr D C U) :=
  (Classical.choose_spec (Nat.exists_prime_lt_and_le_two_mul (max r (dmax D C U))
    (max_r_dmax_ne_zero hr D C U))).1

theorem dmax_lt_designPrime {N r : ℕ} {𝓗 : MultiHypergraph N} (hr : 3 ≤ r) (D C : ℝ)
    (U : UnifData N r 𝓗) : dmax D C U < designPrime hr D C U :=
  lt_of_le_of_lt (le_max_right _ _)
    (Classical.choose_spec (Nat.exists_prime_lt_and_le_two_mul (max r (dmax D C U))
      (max_r_dmax_ne_zero hr D C U))).2.1

theorem r_lt_designPrime {N r : ℕ} {𝓗 : MultiHypergraph N} (hr : 3 ≤ r) (D C : ℝ)
    (U : UnifData N r 𝓗) : r < designPrime hr D C U :=
  lt_of_le_of_lt (le_max_left _ _)
    (Classical.choose_spec (Nat.exists_prime_lt_and_le_two_mul (max r (dmax D C U))
      (max_r_dmax_ne_zero hr D C U))).2.1

theorem designPrime_le {N r : ℕ} {𝓗 : MultiHypergraph N} (hr : 3 ≤ r) (D C : ℝ)
    (U : UnifData N r 𝓗) : designPrime hr D C U ≤ 2 * max r (dmax D C U) :=
  (Classical.choose_spec (Nat.exists_prime_lt_and_le_two_mul (max r (dmax D C U))
    (max_r_dmax_ne_zero hr D C U))).2.2

/-- The number of clones: `1` when no design is needed, and `r * p` (`p` a prime
`> max r dmax`) otherwise. -/
def T {N r : ℕ} {𝓗 : MultiHypergraph N} (hr : 3 ≤ r) (D C : ℝ) (U : UnifData N r 𝓗) : ℕ :=
  if dmax D C U = 0 then 1 else r * designPrime hr D C U

theorem T_pos {N r : ℕ} {𝓗 : MultiHypergraph N} (hr : 3 ≤ r) (D C : ℝ)
    (U : UnifData N r 𝓗) : 0 < T hr D C U := by
  rw [T]
  split
  · omega
  · have h := r_lt_designPrime hr D C U
    exact Nat.mul_pos (by omega) (by omega)

theorem T_eq_of_ne {N r : ℕ} {𝓗 : MultiHypergraph N} (hr : 3 ≤ r) (D C : ℝ)
    (U : UnifData N r 𝓗) (h : dmax D C U ≠ 0) : T hr D C U = r * designPrime hr D C U := by
  rw [T]
  split_ifs with h'
  · exact absurd h' h
  · rfl

/-- The design glued at the clones of `u`: an `r`-uniform linear family on
`Fin (T hr D C U)` in which every clone of `u` has degree `dprime D C U u`
(empty when `dprime D C U u = 0`). -/
def designOn {N r : ℕ} {𝓗 : MultiHypergraph N} (hr : 3 ≤ r) (D C : ℝ) (U : UnifData N r 𝓗)
    (u : Vstar 𝓗 r U.M) : Set (Set (Fin (r * designPrime hr D C U))) :=
  Classical.choose (exists_linear_regular_uniform r (designPrime hr D C U) (dprime D C U u)
    (by omega) (designPrime_prime hr D C U) (le_of_lt (r_lt_designPrime hr D C U))
    (le_of_lt (lt_of_le_of_lt (dprime_le_dmax D C U u) (dmax_lt_designPrime hr D C U))))

def des {N r : ℕ} {𝓗 : MultiHypergraph N} (hr : 3 ≤ r) (D C : ℝ) (U : UnifData N r 𝓗)
    (u : Vstar 𝓗 r U.M) : Set (Set (Fin (T hr D C U))) :=
  if h : dmax D C U = 0 then ∅
  else Set.image (fun E : Set (Fin (r * designPrime hr D C U)) =>
        (finCongr (T_eq_of_ne hr D C U h).symm) '' E) (designOn hr D C U u)


end

end Work.Deep.Nibble
