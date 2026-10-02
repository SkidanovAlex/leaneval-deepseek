import Submission.Work.Deep.Nibble.Defs

/-!
# Edge objects: multiplicities in the Nibble Lemma (defect 6)

The paper's `𝓗'` is a **multi**-hypergraph, and its matchings are families of
*edges of the multi-hypergraph*, i.e. they select at most one **copy** of each
singleton `{w}`.  A formalisation in which the matchings of the Nibble Lemma are
families of *vertex sets* loses the copy information, and the resulting statement
is not strong enough for the §7 assembly: for a vertex `w` the paper's induction
register `(ii)_j` — "all but `γ n_i` of the batch matchings cover `w`" — is
derived by counting *copies* through `w` (the proper edges through `w` plus the
`𝓗'.singles w` copies of `{w}`), and one vertex set `{w}` occurring in a single
matching may not be charged to `𝓗'.singles w` different colours.

This module introduces the vocabulary of the paper's reading:

* `EdgeObj 𝓜` — the edge objects of `𝓜`: its proper edges (each once) plus the
  `𝓜.singles v` copies of the singleton `{v}`.  This is the same index type as
  the edge bijection `κ` of `EmbedStatement` (see `EmbedAtR` below), so
  `lem:embed` transports objects to *distinct* edges of `𝓖`.
* `EdgeObj.toSet`, `objThrough 𝓜 w` (all `𝓜.deg w` objects through `w`),
  `objVert`, `objFam` (the projection onto vertex sets), `IsObjMatching`,
  `ObjDisjoint`, `LeftoverFamObj` (NB3 over families of *sets of objects*).
* `PseudorandomMatchingAtObj` — the instance of `lem:pseudorandom_matching` used
  by the §7 assembly, whose witness is a family of **object matchings**
  `N i : Set (EdgeObj 𝓗')`, each extending the corresponding seed `M i`
  (every edge of `M i` is the vertex set of some object of `N i`).
* `EmbedAtR` — `lem:embed` with the explicit constant `C₀ = r` (the value
  produced by `Work.Deep.Nibble.embedStatement`), which is the form in which the
  §8 reduction consumes the embedding lemma.

The counting step that the cone's `NibbleStatement` needs in its §7 register is
`objCover`: for object matchings, each colour covers `w` through at most one
object, and distinct covered objects are covered by *distinct* colours, hence
`#{c : w ∉ V(N c)} ≤ (D - d_{𝓗'}(w)) + #{objects through w uncovered}`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- **The edge objects of a multi-hypergraph**: its proper edges (each once),
together with the `𝓜.singles v` copies of the singleton edge `{v}`.

This is exactly the index type of `EmbedStatement`'s edge bijection
`κ : ({e // e ∈ 𝓜.edges} ⊕ {p // p.2 < 𝓜.singles p.1}) ≃ {f // f ∈ 𝓖 ∧ ...}`,
so every use of `lem:embed` below transports objects to distinct edges. -/
def EdgeObj (𝓜 : MultiHypergraph n) : Type :=
  ({e : Set (Fin n) // e ∈ 𝓜.edges}) ⊕ {p : Fin n × ℕ // p.2 < 𝓜.singles p.1}

namespace EdgeObj

variable {𝓜 : MultiHypergraph n}

/-- The vertex set of an edge object. -/
def toSet : EdgeObj 𝓜 → Set (Fin n)
  | Sum.inl e => e.1
  | Sum.inr p => {p.1.1}

@[simp] theorem toSet_inl (e : {e : Set (Fin n) // e ∈ 𝓜.edges}) :
    EdgeObj.toSet (Sum.inl e) = e.1 := rfl

@[simp] theorem toSet_inr (p : {p : Fin n × ℕ // p.2 < 𝓜.singles p.1}) :
    EdgeObj.toSet (Sum.inr p) = {p.1.1} := rfl

/-- Every object is an edge of the multi-hypergraph in the sense of
`edgeSet` (proper edges and singletons with multiplicity at least one). -/
theorem toSet_mem_edgeSet (x : EdgeObj 𝓜) : EdgeObj.toSet x ∈ 𝓜.edgeSet := by
  rcases x with e | p
  · exact Or.inl e.2
  · refine Or.inr ⟨p.1.1, rfl, ?_⟩
    have := p.2
    omega

/-- The two summands give injective maps into the objects. -/
theorem inl_injective : Function.Injective (fun e : {e : Set (Fin n) // e ∈ 𝓜.edges} =>
    (Sum.inl e : EdgeObj 𝓜)) := fun _ _ h => Sum.inl.inj h

theorem inr_injective : Function.Injective
    (fun p : {p : Fin n × ℕ // p.2 < 𝓜.singles p.1} => (Sum.inr p : EdgeObj 𝓜)) :=
  fun _ _ h => Sum.inr.inj h

end EdgeObj

/-- **All the edge objects through a vertex `w`**: the `𝓜.deg w` copies of the
edges of `𝓜` that contain `w`. -/
def objThrough (𝓜 : MultiHypergraph n) (w : Fin n) : Set (EdgeObj 𝓜) :=
  {x | w ∈ EdgeObj.toSet x}

/-- The vertex set covered by a family of edge objects. -/
def objVert {𝓜 : MultiHypergraph n} (N : Set (EdgeObj 𝓜)) : Set (Fin n) :=
  ⋃ x ∈ N, EdgeObj.toSet x

/-- The projection of a family of edge objects onto a family of vertex sets. -/
def objFam {𝓜 : MultiHypergraph n} (N : Set (EdgeObj 𝓜)) : Set (Set (Fin n)) :=
  {e | ∃ x ∈ N, EdgeObj.toSet x = e}

/-- An **object matching**: pairwise disjoint vertex sets.  Since two copies of
the singleton `{w}` have the same vertex set, this selects at most one copy of
each singleton. -/
def IsObjMatching {𝓜 : MultiHypergraph n} (N : Set (EdgeObj 𝓜)) : Prop :=
  ∀ x ∈ N, ∀ y ∈ N, x ≠ y → Disjoint (EdgeObj.toSet x) (EdgeObj.toSet y)

/-- **NB3 with multiplicities**: `𝓕E` is a family of *sets of edge objects* of
`𝓜` (e.g. `objThrough 𝓜 w`), and the conclusion bounds the number of objects
that are used by none of the object matchings `N i`. -/
def LeftoverFamObj {n : ℕ} {D : ℕ} {𝓜 : MultiHypergraph n} (N : Fin D → Set (EdgeObj 𝓜))
    (𝓕E : Set (Set (EdgeObj 𝓜))) (γ κ : ℝ) : Prop :=
  ∀ F ∈ 𝓕E, (({x ∈ F | ∀ c : Fin D, x ∉ N c}).ncard : ℝ) ≤
    γ * (F.ncard : ℝ) + κ * max (F.ncard : ℝ) (D : ℝ)

/-- **`lem:pseudorandom_matching` with multiplicities** (the instance used by
the §7 assembly), at a fixed vertex count.

The witness is a family `N : Fin D → Set (EdgeObj 𝓗')` of **object matchings** of
`𝓗'` (the paper's `N_i'`): each `N i` is an object matching, the `N i` are
pairwise *edge*-disjoint as object families (a given object of `𝓗'` is used by at
most one colour), each `N i` avoids the vertices of the seed `M i`, each `N i` is
`(γ,κ)`-pseudorandom with respect to `𝓕V` (NB2), and NB3 (over the objects of the
family `𝓕E`) holds.  The caller forms the paper's `N_i := N_i' ∪ M_i`. -/
def PseudorandomMatchingAtObj (n : ℕ) (r : ℕ) (β κ γ : ℝ) : Prop :=
  ∀ (𝓗 𝓗' : MultiHypergraph n) (𝓕V : Set (Set (Fin n))) (𝓕E : Set (Set (EdgeObj 𝓗')))
    {D : ℕ} (M : Fin D → Set (Set (Fin n))),
    (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) → (D : ℝ) ≤ (n : ℝ) →
    𝓗.IsLinear → 𝓗'.IsLinear → 𝓗' ≤ 𝓗 →
    (∀ w : Fin n, |((𝓗'.deg w : ℝ)) - (D : ℝ)| ≤ β * (D : ℝ)) →
    (∀ e ∈ 𝓗'.edges, edgeSize e ≤ r) →
    (𝓕V.ncard : ℝ) ≤ (n : ℝ) ^ Real.log n →
    (𝓕E.ncard : ℝ) ≤ (n : ℝ) ^ Real.log n →
    (∀ i, MultiHypergraph.IsMatching 𝓗 (M i)) →
    (∀ i, ∀ e ∈ M i, e ∉ 𝓗'.edgeSet) →
    (∀ i j, i ≠ j → EdgeDisjointFam (M i) (M j)) →
    (∀ i, ((famVert (M i)).ncard : ℝ) ≤ β * (D : ℝ)) →
    (∀ e ∈ 𝓗'.edgeSet,
      (({i : Fin D | (e ∩ famVert (M i)).Nonempty}).ncard : ℝ) ≤ β * (D : ℝ)) →
    ∃ N : Fin D → Set (EdgeObj 𝓗'),
      (∀ i, IsObjMatching (N i)) ∧
      (∀ i j, i ≠ j → Disjoint (N i) (N j)) ∧
      (∀ i, Disjoint (objVert (N i)) (famVert (M i))) ∧
      (∀ i, PseudoRandomFam (objFam (N i)) 𝓕V γ κ) ∧
      LeftoverFamObj N 𝓕E γ κ

/-- `PseudorandomMatchingAtObj` for every vertex count above a threshold. -/
def PseudorandomMatchingAboveObj (N₀ : ℕ) (r : ℕ) (β κ γ : ℝ) : Prop :=
  ∀ n : ℕ, N₀ ≤ n → PseudorandomMatchingAtObj n r β κ γ

/-- The body of `cor:sparse_egj` at a fixed vertex count (the cone's
`SparseMatchingStatement` with the threshold `n₀` stripped off; see
`SparseMatchingAbove`). -/
def SparseMatchingBody (n : ℕ) (r : ℕ) (κ γ : ℝ) : Prop :=
  ∀ D : ℝ, (n : ℝ) ^ ((1 : ℝ) / 100) ≤ D →
  ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear → (∀ e ∈ 𝓗, edgeSize e = r) →
    (∀ v : Fin n, |((hypergraphDegree 𝓗 v : ℝ)) - D| ≤ κ * D) →
    ∀ 𝓕 : Set (Set (Fin n)), (𝓕.ncard : ℝ) ≤ (n : ℝ) ^ (2 * Real.log n) →
      ∃ M : Set 𝓗, IsMatching 𝓗 M ∧ ∀ S ∈ 𝓕, D ^ ((1 : ℝ) / 20) ≤ (S.ncard : ℝ) →
        |(((S \ matchVert M).ncard : ℝ) - γ * (S.ncard : ℝ))| ≤ 4 * κ * (S.ncard : ℝ)

/-- `cor:sparse_egj` for every vertex count above an explicit threshold. -/
def SparseMatchingAbove (N₀ : ℕ) (r : ℕ) (κ γ : ℝ) : Prop :=
  ∀ n : ℕ, N₀ ≤ n → SparseMatchingBody n r κ γ

/-- The cone's `SparseMatchingStatement` in terms of the fixed-`n` body: the
threshold `n₀` is existential there. -/
theorem sparseMatchingStatement_iff :
    SparseMatchingStatement ↔
      ∀ r : ℕ, 2 ≤ r → ∀ κ γ : ℝ, 0 < κ → κ ≤ 1 → 0 < γ → γ ≤ 1 →
        ∃ n₀ : ℝ, 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ (n : ℝ) → SparseMatchingBody n r κ γ := by
  constructor
  · intro h r hr κ γ hκ hκ1 hγ hγ1
    obtain ⟨n₀, hn₀, h⟩ := h r hr κ γ hκ hκ1 hγ hγ1
    exact ⟨n₀, hn₀, fun n hn => h n hn⟩
  · intro h r hr κ γ hκ hκ1 hγ hγ1
    obtain ⟨n₀, hn₀, h⟩ := h r hr κ γ hκ hκ1 hγ hγ1
    exact ⟨n₀, hn₀, fun n hn => h n hn⟩

/-- **`lem:embed` at the explicit constant `C₀ = r`**: the conclusion of the
cone's `EmbedStatement` with `C₀` replaced by `r` (the value produced by
`Work.Deep.Nibble.embedStatement`).  This is the form in which the §8 reduction
consumes the embedding lemma, because the threshold of the pseudorandom-matching
lemma involves `C₀`. -/
def EmbedAtR (r : ℕ) : Prop :=
  ∀ {N : ℕ} (D C : ℝ) (𝓗 : MultiHypergraph N), (r : ℝ) ≤ C → 0 < D → (1 : ℝ) ≤ D →
    𝓗.IsLinear →
    (∀ e ∈ 𝓗.edges, edgeSize e ≤ r) →
    (∀ v : Fin N, (𝓗.deg v : ℝ) ≤ D) →
    (∀ v : Fin N, 0 < 𝓗.deg v → D - C ≤ (𝓗.deg v : ℝ)) →
    ∃ (M : ℕ) (ι : Fin N ↪ Fin M) (𝓖 : Hypergraph (Fin M))
      (κ : ({e : Set (Fin N) // e ∈ 𝓗.edges} ⊕
            {p : Fin N × ℕ // p.2 < 𝓗.singles p.1}) ≃
            {e : Set (Fin M) //
              e ∈ 𝓖 ∧ (e ∩ ι '' {v : Fin N | 0 < 𝓗.deg v}).Nonempty}),
      (∀ e ∈ 𝓖, edgeSize e = r) ∧
      𝓖.IsLinear ∧
      (M : ℝ) ≤ (r : ℝ) * ((r : ℝ) - 1) ^ 2 * D ^ 3 * (N : ℝ) ∧
      (∀ (e : Set (Fin N)) (he : e ∈ 𝓗.edges),
          ((κ (Sum.inl ⟨e, he⟩) : Set (Fin M)) ∩ ι '' {v : Fin N | 0 < 𝓗.deg v})
            = ι '' e) ∧
      (∀ (v : Fin N) (k : ℕ) (hk : k < 𝓗.singles v),
          (κ (Sum.inr ⟨(v, k), hk⟩) : Set (Fin M)) ∩ ι '' {v : Fin N | 0 < 𝓗.deg v}
            = {ι v}) ∧
      (∀ w : Fin M, D - C ≤ (MultiHypergraph.hdeg 𝓖 w : ℝ) ∧
        (MultiHypergraph.hdeg 𝓖 w : ℝ) ≤ D) ∧
      (∀ v : Fin N, 0 < 𝓗.deg v → MultiHypergraph.hdeg 𝓖 (ι v) = 𝓗.deg v)

end

end ErdosFaberLovaszConjecture
