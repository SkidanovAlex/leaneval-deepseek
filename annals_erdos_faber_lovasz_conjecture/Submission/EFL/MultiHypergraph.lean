import Submission.EFL.Reservoir

/-!
# Linear multi-hypergraphs (paper §8–§12)

Several constructions of the paper produce a *linear multi-hypergraph*: a
hypergraph whose edges of size at least two are pairwise intersecting in at
most one vertex, but in which *singleton* edges may occur with multiplicity.
The canonical example is `𝓗_reg` of Definition 11.4 (`def:hreg`), obtained
from `𝓗` by adding `max 0 (n - 3 - d_𝓗(w))` singleton edges at every vertex
`w`, and the multi-hypergraph `𝓗'` of the Regularising Lemma 11.3, obtained
from `𝓗_small ∖ R_res` by adding `k - d(w)` singleton edges at each vertex `w`
with `d(w) < k`.

We model this as a pair: the family `edges` of edges of size at least two,
and a function `singles : Fin n → ℕ` giving the multiplicity of the singleton
edge `{w}`.  The degree of a vertex is the number of edges containing it
(counted with multiplicity).  Order is componentwise.

The main declarations are

* `MultiHypergraph.deg` — the degree `d_𝓜(w)`;
* `MultiHypergraph.IsLinear` — linearity of the proper edges;
* `MultiHypergraph.ofHypergraph` — a hypergraph as a multi-hypergraph with no
  singletons;
* `MultiHypergraph.regHypergraph` — `𝓗_reg` of Definition 11.4;
* `MultiHypergraph.addSingletons` — `𝓕` with `k - d_𝓕(w)` singleton edges
  added at each vertex `w`, the object produced by the Regularising Lemma.
-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- A *multi-hypergraph* on `Fin n`: the family of its edges of size at least
two, together with the multiplicity of the singleton edge at each vertex. -/
structure MultiHypergraph (n : ℕ) where
  /-- The edges of size at least two. -/
  edges : Set (Set (Fin n))
  /-- The number of singleton edges `{v}`. -/
  singles : Fin n → ℕ

namespace MultiHypergraph

variable {n : ℕ}

/-- The degree of `v` in a family of edges, as a natural number. -/
def hdeg (𝓗 : Hypergraph (Fin n)) (v : Fin n) : ℕ := {e ∈ 𝓗 | v ∈ e}.ncard

/-- The degree `d_𝓜(v)`: the number of edges containing `v`, counted with
multiplicity (the singleton edges `{v}` contribute `singles v`). -/
def deg (𝓜 : MultiHypergraph n) (v : Fin n) : ℕ :=
  hdeg 𝓜.edges v + 𝓜.singles v

@[simp]
theorem deg_def (𝓜 : MultiHypergraph n) (v : Fin n) :
    𝓜.deg v = hdeg 𝓜.edges v + 𝓜.singles v := rfl

/-- Extensionality. -/
@[ext]
theorem ext {𝓜 𝓝 : MultiHypergraph n} (hedges : 𝓜.edges = 𝓝.edges)
    (hsingles : 𝓜.singles = 𝓝.singles) : 𝓜 = 𝓝 := by
  obtain ⟨e₁, s₁⟩ := 𝓜
  obtain ⟨e₂, s₂⟩ := 𝓝
  simp only [MultiHypergraph.mk.injEq] at hedges hsingles ⊢
  exact ⟨hedges, hsingles⟩

/-- **Linearity of a multi-hypergraph**: the edges of size at least two are
pairwise intersecting in at most one vertex (the proper edge family consists
of edges of size at least two). -/
def IsLinear (𝓜 : MultiHypergraph n) : Prop :=
  (∀ e ∈ 𝓜.edges, 2 ≤ edgeSize e) ∧
    𝓜.edges.Pairwise fun e₁ e₂ => (e₁ ∩ e₂).Subsingleton

instance instLE : LE (MultiHypergraph n) :=
  ⟨fun 𝓜 𝓝 => 𝓜.edges ⊆ 𝓝.edges ∧ ∀ v, 𝓜.singles v ≤ 𝓝.singles v⟩

@[simp]
theorem le_def {𝓜 𝓝 : MultiHypergraph n} :
    𝓜 ≤ 𝓝 ↔ 𝓜.edges ⊆ 𝓝.edges ∧ ∀ v, 𝓜.singles v ≤ 𝓝.singles v := Iff.rfl

theorem le_self (𝓜 : MultiHypergraph n) : 𝓜 ≤ 𝓜 := ⟨subset_rfl, fun _ => Nat.le_refl _⟩

theorem le_trans {𝓜 𝓝 𝓟 : MultiHypergraph n} (h₁ : 𝓜 ≤ 𝓝) (h₂ : 𝓝 ≤ 𝓟) : 𝓜 ≤ 𝓟 :=
  ⟨h₁.1.trans h₂.1, fun v => (h₁.2 v).trans (h₂.2 v)⟩

theorem edges_mono {𝓜 𝓝 : MultiHypergraph n} (h : 𝓜 ≤ 𝓝) : 𝓜.edges ⊆ 𝓝.edges := h.1

theorem singles_mono {𝓜 𝓝 : MultiHypergraph n} (h : 𝓜 ≤ 𝓝) (v : Fin n) :
    𝓜.singles v ≤ 𝓝.singles v := h.2 v

/-- Degree is monotone for the componentwise order. -/
theorem deg_le_deg {𝓜 𝓝 : MultiHypergraph n} (h : 𝓜 ≤ 𝓝) (v : Fin n) :
    𝓜.deg v ≤ 𝓝.deg v := by
  have hset : {e ∈ 𝓜.edges | v ∈ e} ⊆ {e ∈ 𝓝.edges | v ∈ e} := by
    intro e he
    exact ⟨h.1 he.1, he.2⟩
  have := Set.ncard_le_ncard hset
  exact Nat.add_le_add this (h.2 v)

/-- The multi-hypergraph underlying a hypergraph (no singleton edges). -/
def ofHypergraph (𝓗 : Hypergraph (Fin n)) : MultiHypergraph n := ⟨𝓗, fun _ => 0⟩

@[simp]
theorem edges_ofHypergraph (𝓗 : Hypergraph (Fin n)) : (ofHypergraph 𝓗).edges = 𝓗 := rfl

@[simp]
theorem singles_ofHypergraph (𝓗 : Hypergraph (Fin n)) (v : Fin n) :
    (ofHypergraph 𝓗).singles v = 0 := rfl

@[simp]
theorem deg_ofHypergraph (𝓗 : Hypergraph (Fin n)) (v : Fin n) :
    (ofHypergraph 𝓗).deg v = hdeg 𝓗 v := by
  simp [deg, hdeg]

theorem ofHypergraph_le_iff {𝓗 : Hypergraph (Fin n)} {𝓜 : MultiHypergraph n} :
    ofHypergraph 𝓗 ≤ 𝓜 ↔ 𝓗 ⊆ 𝓜.edges := by
  constructor
  · intro h
    simpa using h.1
  · intro h
    exact ⟨by simpa using h, fun v => by simp⟩

theorem isLinear_ofHypergraph {𝓗 : Hypergraph (Fin n)} (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e)
    (hlin : 𝓗.IsLinear) : (ofHypergraph 𝓗).IsLinear :=
  ⟨by simpa using hbig, hlin⟩

theorem isLinear_mono {𝓜 𝓝 : MultiHypergraph n} (h : 𝓜 ≤ 𝓝) (hlin : 𝓝.IsLinear) :
    𝓜.IsLinear :=
  ⟨fun e he => hlin.1 e (h.1 he), hlin.2.mono h.1⟩

/-- `𝓗_reg` of Definition 11.4: `𝓗` with `max 0 (n - 3 - d_𝓗(w))` singleton
edges added at every vertex `w`. -/
def regHypergraph (𝓗 : Hypergraph (Fin n)) : MultiHypergraph n :=
  ⟨𝓗, fun w => n - 3 - hdeg 𝓗 w⟩

@[simp]
theorem edges_regHypergraph (𝓗 : Hypergraph (Fin n)) : (regHypergraph 𝓗).edges = 𝓗 := rfl

@[simp]
theorem singles_regHypergraph (𝓗 : Hypergraph (Fin n)) (w : Fin n) :
    (regHypergraph 𝓗).singles w = n - 3 - hdeg 𝓗 w := rfl

/-- The multi-hypergraph obtained from the edge family `𝓕` by adding
`k - d_𝓕(w)` singleton edges at every vertex `w` with `d_𝓕(w) < k`
(so that the resulting degree at `w` is `max k (d_𝓕 w)`). -/
def addSingletons (𝓕 : Hypergraph (Fin n)) (k : ℕ) : MultiHypergraph n :=
  ⟨𝓕, fun w => k - hdeg 𝓕 w⟩

@[simp]
theorem edges_addSingletons (𝓕 : Hypergraph (Fin n)) (k : ℕ) :
    (addSingletons 𝓕 k).edges = 𝓕 := rfl

@[simp]
theorem singles_addSingletons (𝓕 : Hypergraph (Fin n)) (k : ℕ) (w : Fin n) :
    (addSingletons 𝓕 k).singles w = k - hdeg 𝓕 w := rfl

/-- The degree in `addSingletons 𝓕 k` is `max k (d_𝓕 w)`. -/
theorem deg_addSingletons (𝓕 : Hypergraph (Fin n)) (k : ℕ) (w : Fin n) :
    (addSingletons 𝓕 k).deg w = max (hdeg 𝓕 w) k := by
  rw [deg_def, edges_addSingletons, singles_addSingletons, hdeg]
  omega

/-- A multi-hypergraph is obtained from an edge family by adding singletons
iff its degrees are `max k (d_𝓕 w)`. -/
theorem eq_addSingletons_of_deg {𝓜 : MultiHypergraph n} {𝓕 : Hypergraph (Fin n)}
    (h : 𝓜.edges = 𝓕) (k : ℕ) (hdeg' : ∀ w, 𝓜.deg w = max (hdeg 𝓕 w) k) :
    𝓜 = addSingletons 𝓕 k := by
  obtain ⟨edges, singles⟩ := 𝓜
  have h' : edges = 𝓕 := by simpa using h
  have hsing : singles = fun w => k - hdeg 𝓕 w := by
    funext w
    have hw := hdeg' w
    simp only [deg_def, hdeg] at hw
    rw [h'] at hw
    show singles w = k - {e ∈ 𝓕 | w ∈ e}.ncard
    omega
  subst h'
  subst hsing
  rfl

/-- Deleting a family of proper edges (singleton multiplicities are
unaffected). -/
def sdiff (𝓜 : MultiHypergraph n) (𝓕 : Hypergraph (Fin n)) : MultiHypergraph n :=
  ⟨𝓜.edges \ 𝓕, 𝓜.singles⟩

@[simp]
theorem edges_sdiff (𝓜 : MultiHypergraph n) (𝓕 : Hypergraph (Fin n)) :
    (𝓜.sdiff 𝓕).edges = 𝓜.edges \ 𝓕 := rfl

@[simp]
theorem singles_sdiff (𝓜 : MultiHypergraph n) (𝓕 : Hypergraph (Fin n)) :
    (𝓜.sdiff 𝓕).singles = 𝓜.singles := rfl

theorem sdiff_le (𝓜 : MultiHypergraph n) (𝓕 : Hypergraph (Fin n)) : 𝓜.sdiff 𝓕 ≤ 𝓜 :=
  ⟨Set.sdiff_subset, fun _ => Nat.le_refl _⟩

/-- The *vertex support* of the proper edges of a multi-hypergraph. -/
def supp (𝓜 : MultiHypergraph n) : Set (Fin n) :=
  ⋃₀ 𝓜.edges

theorem mem_supp {𝓜 : MultiHypergraph n} {v : Fin n} : v ∈ 𝓜.supp ↔ ∃ e ∈ 𝓜.edges, v ∈ e := by
  simp [supp]

end MultiHypergraph

end

end ErdosFaberLovaszConjecture
