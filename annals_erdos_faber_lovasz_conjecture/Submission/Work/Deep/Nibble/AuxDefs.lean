import Submission.Work.Deep.Nibble.Defs

/-!
# Auxiliary vocabulary for the proof of `lem:pseudorandom_matching` (§8)

This module sets up the objects used in the proof of
`PseudorandomMatchingStatement` from `EmbedStatement` and
`SparseMatchingStatement` (the paper's Lemma `lem:pseudorandom_matching`):

* `psiSet` — the paper's map `ψ e* = e* ∩ V(𝓗')`, as a total function;
* `AuxVertex`, `auxEdge`, `auxHypergraph` — the `(r+1)`-uniform incidence
  hypergraph `𝓗_aux` of the paper (`efl.tex:1680`);
* `auxFam` — the family `𝓕^aux` of prescribed vertex sets to which
  `cor:sparse_egj` is applied.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

variable {n M D : ℕ}

/-- The paper's map `ψ`, made total: for an edge `f` of `𝓖`, `ψ f` is the set of
old vertices `v` with `ι v ∈ f`. -/
def psiSet (ι : Fin n ↪ Fin M) (f : Set (Fin M)) : Set (Fin n) := {v | ι v ∈ f}

@[simp]
theorem mem_psiSet {ι : Fin n ↪ Fin M} {f : Set (Fin M)} {v : Fin n} :
    v ∈ psiSet ι f ↔ ι v ∈ f := Iff.rfl

/-- The set of edges of `𝓖` meeting the image `ι '' V` of the old vertex set. -/
def Emeet (ι : Fin n ↪ Fin M) (𝓖 : Hypergraph (Fin M)) (V : Set (Fin n)) :
    Set (Set (Fin M)) :=
  {f ∈ 𝓖 | (f ∩ ι '' V).Nonempty}

theorem mem_Emeet {ι : Fin n ↪ Fin M} {𝓖 : Hypergraph (Fin M)} {V : Set (Fin n)}
    {f : Set (Fin M)} : f ∈ Emeet ι 𝓖 V ↔ f ∈ 𝓖 ∧ (f ∩ ι '' V).Nonempty := Iff.rfl

/-- The vertex type of the auxiliary hypergraph `𝓗_aux`: the edges of `𝓖`
(these are the "`e*`" vertices) together with the copies `w^i` of the vertices
`w ∈ V(𝓖)` that avoid `ι '' V(M i)`. -/
abbrev AuxVertex (n M D : ℕ) (𝓖 : Hypergraph (Fin M)) (ι : Fin n ↪ Fin M)
    (Mfam : Fin D → Set (Set (Fin n))) : Type :=
  {y : Set (Fin M) ⊕ (Fin D × Fin M) //
    y.elim (fun f => f ∈ 𝓖) (fun p => p.2 ∉ ι '' famVert (Mfam p.1))}

instance (n M D : ℕ) (𝓖 : Hypergraph (Fin M)) (ι : Fin n ↪ Fin M)
    (Mfam : Fin D → Set (Set (Fin n))) : Fintype (AuxVertex n M D 𝓖 ι Mfam) := by
  haveI : Finite (Set (Fin M) ⊕ (Fin D × Fin M)) := Finite.of_fintype _
  exact Fintype.ofFinite _

/-- The degree of a vertex of a hypergraph on an arbitrary type. -/
def degreeAt {α : Type*} (𝓗 : Hypergraph α) (y : α) : ℕ :=
  Nat.card {A : Set α // A ∈ 𝓗 ∧ y ∈ A}

theorem degreeAt_def {α : Type*} (𝓗 : Hypergraph α) (y : α) :
    degreeAt 𝓗 y = Nat.card {A : Set α // A ∈ 𝓗 ∧ y ∈ A} := rfl

theorem auxVertex_ext {n M D : ℕ} {𝓖 : Hypergraph (Fin M)} {ι : Fin n ↪ Fin M}
    {Mfam : Fin D → Set (Set (Fin n))} {y z : AuxVertex n M D 𝓖 ι Mfam}
    (h : y.val = z.val) : y = z := Subtype.ext h

/-- The `e*`-vertex of `𝓗_aux` attached to an edge `f ∈ 𝓖`. -/
def auxVInl (n M D : ℕ) (𝓖 : Hypergraph (Fin M)) (ι : Fin n ↪ Fin M)
    (Mfam : Fin D → Set (Set (Fin n))) (f : Set (Fin M)) (hf : f ∈ 𝓖) :
    AuxVertex n M D 𝓖 ι Mfam :=
  ⟨Sum.inl f, hf⟩

/-- The `w^i`-vertex of `𝓗_aux`. -/
def auxVInr (n M D : ℕ) (𝓖 : Hypergraph (Fin M)) (ι : Fin n ↪ Fin M)
    (Mfam : Fin D → Set (Set (Fin n))) (i : Fin D) (w : Fin M)
    (hw : w ∉ ι '' famVert (Mfam i)) : AuxVertex n M D 𝓖 ι Mfam :=
  ⟨Sum.inr (i, w), hw⟩

/-- The edge `{f} ∪ {v^i : v ∈ f}` of `𝓗_aux`. -/
def auxEdge (n M D : ℕ) (𝓖 : Hypergraph (Fin M)) (ι : Fin n ↪ Fin M)
    (Mfam : Fin D → Set (Set (Fin n))) (f : Set (Fin M)) (i : Fin D) :
    Set (AuxVertex n M D 𝓖 ι Mfam) :=
  {y | y.val = Sum.inl f ∨ ∃ v : Fin M, y.val = Sum.inr (i, v) ∧ v ∈ f}

/-- The auxiliary hypergraph `𝓗_aux`: the edges are `{f} ∪ {v^i : v ∈ f}` for
`f ∈ 𝓖` and `i ∈ Fin D` with `f ∩ ι '' V(M i) = ∅`. -/
def auxHypergraph (n M D : ℕ) (𝓖 : Hypergraph (Fin M)) (ι : Fin n ↪ Fin M)
    (Mfam : Fin D → Set (Set (Fin n))) : Hypergraph (AuxVertex n M D 𝓖 ι Mfam) :=
  {A | ∃ (f : Set (Fin M)) (_hf : f ∈ 𝓖) (i : Fin D),
    f ∩ ι '' famVert (Mfam i) = ∅ ∧ A = auxEdge n M D 𝓖 ι Mfam f i}

theorem mem_auxHypergraph {n M D : ℕ} {𝓖 : Hypergraph (Fin M)} {ι : Fin n ↪ Fin M}
    {Mfam : Fin D → Set (Set (Fin n))} {A : Set (AuxVertex n M D 𝓖 ι Mfam)} :
    A ∈ auxHypergraph n M D 𝓖 ι Mfam ↔
      ∃ (f : Set (Fin M)) (_hf : f ∈ 𝓖) (i : Fin D),
        f ∩ ι '' famVert (Mfam i) = ∅ ∧ A = auxEdge n M D 𝓖 ι Mfam f i := Iff.rfl

@[simp]
theorem auxVInl_val {n M D : ℕ} {𝓖 : Hypergraph (Fin M)} {ι : Fin n ↪ Fin M}
    {Mfam : Fin D → Set (Set (Fin n))} {f : Set (Fin M)} (hf : f ∈ 𝓖) :
    (auxVInl n M D 𝓖 ι Mfam f hf).val = Sum.inl f := rfl

@[simp]
theorem auxVInr_val {n M D : ℕ} {𝓖 : Hypergraph (Fin M)} {ι : Fin n ↪ Fin M}
    {Mfam : Fin D → Set (Set (Fin n))} {i : Fin D} {w : Fin M}
    (hw : w ∉ ι '' famVert (Mfam i)) :
    (auxVInr n M D 𝓖 ι Mfam i w hw).val = Sum.inr (i, w) := rfl

theorem val_mem_auxEdge {n M D : ℕ} {𝓖 : Hypergraph (Fin M)} {ι : Fin n ↪ Fin M}
    {Mfam : Fin D → Set (Set (Fin n))} (y : AuxVertex n M D 𝓖 ι Mfam)
    (f : Set (Fin M)) (i : Fin D) :
    y ∈ auxEdge n M D 𝓖 ι Mfam f i ↔
      y.val = Sum.inl f ∨ ∃ v : Fin M, y.val = Sum.inr (i, v) ∧ v ∈ f := Iff.rfl

@[simp]
theorem auxVInl_mem_auxEdge {n M D : ℕ} {𝓖 : Hypergraph (Fin M)} {ι : Fin n ↪ Fin M}
    {Mfam : Fin D → Set (Set (Fin n))} {f f' : Set (Fin M)} (hf' : f' ∈ 𝓖) (i : Fin D) :
    auxVInl n M D 𝓖 ι Mfam f' hf' ∈ auxEdge n M D 𝓖 ι Mfam f i ↔ f' = f := by
  rw [val_mem_auxEdge, auxVInl_val]
  constructor
  · rintro (h | ⟨v, h, -⟩)
    · exact Sum.inl.inj h
    · exact absurd h Sum.inl_ne_inr
  · intro h
    exact Or.inl (by rw [h])

@[simp]
theorem auxVInr_mem_auxEdge {n M D : ℕ} {𝓖 : Hypergraph (Fin M)} {ι : Fin n ↪ Fin M}
    {Mfam : Fin D → Set (Set (Fin n))} {f : Set (Fin M)} {i i' : Fin D} {w : Fin M}
    (hw : w ∉ ι '' famVert (Mfam i')) :
    auxVInr n M D 𝓖 ι Mfam i' w hw ∈ auxEdge n M D 𝓖 ι Mfam f i ↔ i' = i ∧ w ∈ f := by
  rw [val_mem_auxEdge, auxVInr_val]
  constructor
  · rintro (h | ⟨v, hv, hvf⟩)
    · exact absurd h Sum.inr_ne_inl
    · have h1 : (i', w) = (i, v) := Sum.inr.inj hv
      refine ⟨congrArg Prod.fst h1, ?_⟩
      have h2 : w = v := congrArg Prod.snd h1
      rw [h2]
      exact hvf
  · rintro ⟨rfl, hw'⟩
    exact Or.inr ⟨w, rfl, hw'⟩

/-- The witness produced by `lem:embed` (`EmbedStatement`) in the application of
`lem:pseudorandom_matching`: an `r`-uniform linear hypergraph `𝓖` on `Fin M`, an
embedding `ι` of the old vertices, the bijection `κ` identifying the edges of
`𝓖` meeting `ι '' V(𝓗')` with the edges of `𝓗'` counted with multiplicity, and
the degree estimates (E2). -/
structure EmbedWitness (n r : ℕ) (D' C : ℝ) (𝓗' : MultiHypergraph n) where
  /-- the number of vertices of `𝓖` -/
  M : ℕ
  /-- the embedding of the old vertices -/
  ι : Fin n ↪ Fin M
  /-- the `r`-uniform linear hypergraph `𝓖` -/
  𝓖 : Hypergraph (Fin M)
  /-- `ψ` of the paper, as the bijection `κ` -/
  κ : ({e : Set (Fin n) // e ∈ 𝓗'.edges} ⊕
        {p : Fin n × ℕ // p.2 < 𝓗'.singles p.1}) ≃
      {e : Set (Fin M) // e ∈ 𝓖 ∧ (e ∩ ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty}
  /-- `𝓖` is `r`-uniform -/
  uni : ∀ e ∈ 𝓖, edgeSize e = r
  /-- `𝓖` is linear -/
  lin : 𝓖.IsLinear
  /-- (E3): the number of vertices -/
  card : (M : ℝ) ≤ (r : ℝ) * ((r : ℝ) - 1) ^ 2 * D' ^ 3 * (n : ℝ)
  /-- (E1) for proper edges -/
  meet_inl : ∀ (e : Set (Fin n)) (he : e ∈ 𝓗'.edges),
      ((κ (Sum.inl ⟨e, he⟩) : Set (Fin M)) ∩ ι '' {v : Fin n | 0 < 𝓗'.deg v}) = ι '' e
  /-- (E1) for the singleton copies -/
  meet_inr : ∀ (v : Fin n) (k : ℕ) (hk : k < 𝓗'.singles v),
      (κ (Sum.inr ⟨(v, k), hk⟩) : Set (Fin M)) ∩ ι '' {v : Fin n | 0 < 𝓗'.deg v} = {ι v}
  /-- (E2): lower degree bound -/
  deg_lo : ∀ w : Fin M, D' - C ≤ (MultiHypergraph.hdeg 𝓖 w : ℝ)
  /-- (E2): upper degree bound -/
  deg_hi : ∀ w : Fin M, (MultiHypergraph.hdeg 𝓖 w : ℝ) ≤ D'
  /-- (E2): the degrees at non-isolated old vertices are those of `𝓗'` -/
  deg_old : ∀ v : Fin n, 0 < 𝓗'.deg v → MultiHypergraph.hdeg 𝓖 (ι v) = 𝓗'.deg v

/-- `EmbedStatement` produces an `EmbedWitness` whenever its hypotheses hold. -/
theorem embedWitness_of_embedStatement (hE : EmbedStatement) {r : ℕ} (hr : 3 ≤ r) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ (r : ℝ) ≤ C₀ ∧
      ∀ {n : ℕ} (D' C : ℝ) (𝓗' : MultiHypergraph n), C₀ ≤ C → 0 < D' → (1 : ℝ) ≤ D' →
        𝓗'.IsLinear → (∀ e ∈ 𝓗'.edges, edgeSize e ≤ r) →
        (∀ v : Fin n, (𝓗'.deg v : ℝ) ≤ D') →
        (∀ v : Fin n, 0 < 𝓗'.deg v → D' - C ≤ (𝓗'.deg v : ℝ)) →
        Nonempty (EmbedWitness n r D' C 𝓗') := by
  obtain ⟨C₀, hC₀, hrC₀, H⟩ := hE r hr
  refine ⟨C₀, hC₀, hrC₀, ?_⟩
  intro n D' C 𝓗' hC hD hD1 hlin hsize hle hlo
  obtain ⟨M, ι, 𝓖, κ, huni, hlin', hcard, hinl, hinr, hdeg, hdegold⟩ :=
    H n C D' hC hD hD1 𝓗' hlin hsize hle hlo
  exact ⟨⟨M, ι, 𝓖, κ, huni, hlin', hcard, hinl, hinr,
    (fun w => (hdeg w).1), (fun w => (hdeg w).2), hdegold⟩⟩

/-- The paper's `ψ` on `E_meet`, packaged: the edge of `𝓗'` (counted with
multiplicity) attached by `κ` to an edge of `𝓖` meeting `ι '' V(𝓗')`. -/
def psiOf {n : ℕ} {r : ℕ} {D' C : ℝ} {𝓗' : MultiHypergraph n}
    (W : EmbedWitness n r D' C 𝓗')
    (f : {e : Set (Fin W.M) // e ∈ W.𝓖 ∧ (e ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty}) :
    Set (Fin n) :=
  match W.κ.symm f with
  | Sum.inl q => q.1
  | Sum.inr q => {q.1.1}

/-- `degreeAt` agrees with the `Nat.card` of the edge subtype used by
`SparseMatchingStatement` and `hypergraphDegree`. -/
theorem degreeAt_eq {α : Type*} (𝓗 : Hypergraph α) (y : α) :
    degreeAt 𝓗 y = Nat.card {e : 𝓗 // y ∈ (e : Set α)} := by
  rw [degreeAt, Nat.card_congr]
  refine Equiv.ofBijective
    (fun x : {A : Set α // A ∈ 𝓗 ∧ y ∈ A} => (⟨⟨x.1, x.2.1⟩, x.2.2⟩ :
      {e : 𝓗 // y ∈ (e : Set α)})) ⟨?_, ?_⟩
  · intro a b h
    exact Subtype.ext (congrArg (fun z => (z.1.1 : Set α)) h)
  · rintro ⟨⟨e, he⟩, hy⟩
    exact ⟨⟨e, he, hy⟩, rfl⟩

/-- `φ(i,S)`: the `i`-th clone set of a family `S` of old vertices, as a subset
of the vertex type of `𝓗_aux`.  Because the vertex type already excludes the
clones of `ι '' V(M i)`, this is `φ(i,S) ∖ φ(i, V(M i))` of the paper. -/
def phiSet (n M D : ℕ) (𝓖 : Hypergraph (Fin M)) (ι : Fin n ↪ Fin M)
    (Mfam : Fin D → Set (Set (Fin n))) (i : Fin D) (S : Set (Fin n)) :
    Set (AuxVertex n M D 𝓖 ι Mfam) :=
  {y | ∃ v : Fin M, v ∈ ι '' S ∧ y.val = Sum.inr (i, v)}

theorem mem_phiSet {n M D : ℕ} {𝓖 : Hypergraph (Fin M)} {ι : Fin n ↪ Fin M}
    {Mfam : Fin D → Set (Set (Fin n))} {i : Fin D} {S : Set (Fin n)}
    {y : AuxVertex n M D 𝓖 ι Mfam} :
    y ∈ phiSet n M D 𝓖 ι Mfam i S ↔ ∃ w ∈ S, y.val = Sum.inr (i, ι w) := by
  constructor
  · rintro ⟨v, ⟨w, hwS, rfl⟩, hv⟩
    exact ⟨w, hwS, hv⟩
  · rintro ⟨w, hwS, hv⟩
    exact ⟨ι w, ⟨w, hwS, rfl⟩, hv⟩

/-- The pruned preimage `ψ^{-1}(F)`, as a set of edges of `𝓖`. -/
def psiInvSet {n r : ℕ} {D' C : ℝ} {𝓗' : MultiHypergraph n} (W : EmbedWitness n r D' C 𝓗')
    (F : Set (Set (Fin n))) : Set (Set (Fin W.M)) :=
  {f | ∃ (hf : f ∈ W.𝓖) (hmeet : (f ∩ W.ι '' {v : Fin n | 0 < 𝓗'.deg v}).Nonempty),
        psiOf W ⟨f, hf, hmeet⟩ ∈ F}

/-- The `Sum.inl`-part of `𝓕^aux`: the set of `e*`-vertices attached to the
edges of `𝓖` whose `ψ`-image lies in `F`. -/
def inlSet (n M D : ℕ) (𝓖 : Hypergraph (Fin M)) (ι : Fin n ↪ Fin M)
    (Mfam : Fin D → Set (Set (Fin n))) (S : Set (Set (Fin M))) :
    Set (AuxVertex n M D 𝓖 ι Mfam) :=
  {y | ∃ f ∈ S, y.val = Sum.inl f}

/-- The family `𝓕^aux` of the paper (`efl.tex:1697`). -/
def auxFam {n r : ℕ} {D' C : ℝ} {𝓗' : MultiHypergraph n} (W : EmbedWitness n r D' C 𝓗')
    (D : ℕ) (𝓖 : Hypergraph (Fin W.M)) (ι : Fin n ↪ Fin W.M)
    (Mfam : Fin D → Set (Set (Fin n))) (𝓕V : Set (Set (Fin n)))
    (𝓕E : Set (Set (Set (Fin n)))) :
    Set (Set (AuxVertex n W.M D 𝓖 ι Mfam)) :=
  (⋃ i : Fin D, phiSet n W.M D 𝓖 ι Mfam i '' 𝓕V) ∪
    (fun F : Set (Set (Fin n)) => inlSet n W.M D 𝓖 ι Mfam (psiInvSet W F)) '' 𝓕E

end

end Work.Deep.Nibble
