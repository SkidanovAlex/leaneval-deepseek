import Submission.EFL.AlphaBoundedColouring
import Submission.EFL.ColourClassCounting

/-!
# Greedy list-colouring (Prop 6.9 of the paper)

Proposition 6.9 is the greedy engine that turns a *list assignment* on the
edges of a linear hypergraph into an `α₂`-bounded proper edge-colouring,
provided every list is long enough compared with the number of neighbours
of the edge that precede it in a fixed linear ordering of the edges.

> **Proposition 6.9.**  Let `0 < 1/n₀ ≪ 1/r ≪ α₁, α₂ < 1` and `n ≥ n₀`.  Let
> `⪯` be a linear ordering of the edges of an `n`-vertex linear hypergraph
> `H` where every `e ∈ H` satisfies `|e| ≥ r`.  If `C` is a list-assignment
> for the line graph of `H` such that every `e ∈ H` satisfies
> `|C(e)| ≥ d⪯(e) + α₁n`, then there is an `α₂`-bounded proper
> edge-colouring `φ` of `H` such that `φ(e) ∈ C(e)` for every `e ∈ H`.

Here (paper §6.1), for an edge `e`, `N⪯(e) = {f ∈ N(e) : f ⪯ e}` and
`d⪯(e) = |N⪯(e)|`: the neighbours of `e` (distinct edges intersecting `e`)
that precede-or-equal `e` in the ordering; `H⪯e = {f ∈ H : f ⪯ e}` is the
initial segment.

## Formalisation conventions

* **Ordering.**  The edges of `𝓗` form a finite type (they are the members
  of the set `𝓗 ⊆ Set (Fin n)`, which is finite because `Fin n` is).  A
  *linear ordering* of the edges is represented by its rank function
  `ord : 𝓗 ≃ Fin (Fintype.card 𝓗)`: `e ⪯ f` is `ord e ≤ ord f`.  Every
  linear order on a finite type arises this way (the rank map), and the
  equivalence keeps all arithmetic on the standard order of `Fin`.
* **Lists.**  Colours are the elements of `Fin n` (the colour host used
  throughout this project).  A *list assignment* is a map
  `C : 𝓗 → Finset (Fin n)`; a colouring `φ` *respects* `C` when
  `φ.labels e ∈ C e` for every edge `e`.
* **Boundedness** is the host-independent `Coloring.AlphaBounded` of
  `AlphaBoundedColouring.lean`; the honest per-instance statement
  `Prop69Instance` records the hypotheses the proof needs (linearity, all
  edges of size `≥ r`, lists long against `d⪯`, and the concrete margins
  `2n/(α₂(r−1)) < α₁n/4` (heavy colours — Prop 6.8(i)) and
  `#big < α₁n/2` (big edges), the paper's hierarchy
  `0 < 1/n₀ ≪ 1/r ≪ α₁, α₂` supplying them for `n ≥ n₀`).

**Prop 6.9 is fully proved below.**  The greedy engine
(`greedy_colouring_hugeFirst`) processes the edges in order and extends a
maximal colourable prefix; the complete proof needs and has: the
`SegmentColourable` machinery, the huge-edge step (a fresh colour — its
class is a singleton) and the small-edge step (a colour outside `C₁ ∪ C₂`
— proper and light), the bounds `|C₁| ≤ d⪯(f)` and
`|C₂| ≤ 2n/(α₂(r−1))`, the transport of the colouring of the whole edge
set back to `𝓗`, and — to remove the huge-first restriction on the
ordering — the huge-first reordering of an arbitrary ordering with the
forward-degree comparison `fwddeg' ≤ fwddeg + #big`
(`exists_hugeFirst_reorder`, `fwddeg_le_of_reorder`), which halves `α₁`
and gives `prop69_colouring`, recorded as `Prop69Instance`/`prop69Instance`
at the bottom of this file.

The proof (paper §6.3) processes the edges in the order `⪯`: starting from
the empty prefix (colourable), take a colouring of an initial segment
`H⪯e*` of maximum size (the set of such `e*` is finite and nonempty); if
`e*` is not the last edge, let `f` be its successor.  If `f` is huge
(`|f| ≥ α₂n/2`) a fresh colour (outside all colours used on the prefix)
works, since then the colour is used once.  Otherwise `f` is small, and any
colour of `C(f)` that is neither used on a preceding neighbour of `f`
(properness) nor a colour whose current class already covers `≥ α₂n/2`
vertices (boundedness) extends the colouring; the classes with
`≥ α₂n/2` vertices are bounded by Prop 6.8(i) — `|C₂| ≤ 2n/(α₂(r−1))` —
contradicting `|C(f)| ≥ d⪯(f) + α₁n`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The neighbours of `e` in the line graph of `𝓗` (distinct edges
intersecting `e`) that precede-or-equal `e` in the ordering `ord`
(`N⪯(e)` of the paper).  The ordering is given by an equivalence
`ord : 𝓗 ≃ Fin k` (the rank of each edge); the choice of `k` is
irrelevant (an equivalence forces `k = |𝓗|`).  The type `𝓗` is finite
because the vertex type `Fin n` is, so the Finset is taken over all edges;
`classical` provides the required decidability. -/
noncomputable def precedingNeighbours {k : ℕ} (𝓗 : Hypergraph (Fin n)) (ord : 𝓗 ≃ Fin k)
    (e : 𝓗) : Finset 𝓗 := by
  classical
  exact (Finset.univ : Finset 𝓗).filter (fun f : 𝓗 =>
    f ≠ e ∧ ord f ≤ ord e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)

/-- The *preceding degree* `d⪯(e) = |N⪯(e)|` of the paper §6.1: the number
of neighbours of `e` that precede-or-equal `e` in the ordering. -/
noncomputable def precedingDegree {k : ℕ} (𝓗 : Hypergraph (Fin n)) (ord : 𝓗 ≃ Fin k)
    (e : 𝓗) : ℕ :=
  (precedingNeighbours 𝓗 ord e).card

/-- Membership in `precedingNeighbours`. -/
lemma mem_precedingNeighbours {k : ℕ} (𝓗 : Hypergraph (Fin n)) (ord : 𝓗 ≃ Fin k)
    (e f : 𝓗) :
    f ∈ precedingNeighbours 𝓗 ord e ↔
      f ≠ e ∧ ord f ≤ ord e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty := by
  classical
  simp [precedingNeighbours]

/-- An edge is not its own preceding neighbour. -/
lemma precedingNeighbours_not_self {k : ℕ} (𝓗 : Hypergraph (Fin n)) (ord : 𝓗 ≃ Fin k)
    (e : 𝓗) : e ∉ precedingNeighbours 𝓗 ord e := by
  rw [mem_precedingNeighbours]
  exact fun h => h.1 rfl

/-- Two edges cannot strictly precede each other. -/
lemma order_le_antisymm {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    {e f : 𝓗} (h₁ : ord e ≤ ord f) (h₂ : ord f ≤ ord e) : e = f := by
  exact ord.injective (le_antisymm h₁ h₂)

/-- The ordering ranks of two edges compare. -/
lemma order_le_total {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (e f : 𝓗) : ord e ≤ ord f ∨ ord f ≤ ord e :=
  le_total (ord e) (ord f)

/-- Preceding neighbours of `e` are distinct from `e` and precede-or-equal it
(restated as a derived membership rule). -/
lemma mem_precedingNeighbours_of_le {k : ℕ} (𝓗 : Hypergraph (Fin n)) (ord : 𝓗 ≃ Fin k)
    {e f : 𝓗} (hne : f ≠ e) (hle : ord f ≤ ord e)
    (hint : ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty) :
    f ∈ precedingNeighbours 𝓗 ord e := by
  rw [mem_precedingNeighbours]
  exact ⟨hne, hle, hint⟩

/-! **Prop 6.9 (paper §6.3) is proved below** as `prop69_colouring` (the
greedy engine `greedy_colouring_hugeFirst` for huge-first orderings, the
huge-first reordering of an arbitrary ordering with its forward-degree
comparison, and the halving of `α₁` that absorbs the reordering slack).
The per-instance statement `Prop69Instance` (now defined at the bottom of
this file, after `bigFinset`) records the theorem with the concrete margins
the proof needs: `2n/(α₂(r−1)) < α₁n/4` (heavy colours, Prop 6.8(i)) and
`#big < α₁n/2` (fresh colours for big edges and reordering slack); both are
discharged at the level of the `≪`-hierarchy `0 < 1/n₀ ≪ 1/r ≪ α₁, α₂`. -/

/-! ## Colouring edge subsets (subhypergraph API)

The greedy proof of Prop 6.9 colours the edges of an *initial segment*
(prefix) of the ordering and extends the colouring one edge at a time.  A
colourings lives on a hypergraph whose edges are vertex sets; an *edge
subset* `M : Set 𝓗` becomes the hypergraph `edgeSubgraph M` of the vertex
sets of the edges in `M` (a subhypergraph of `𝓗` on the same vertices).
Because `𝓗` is a set of vertex sets, different edges of `𝓗` have different
vertex sets (`edgeSet_injective`), so `edgeSubgraph M` is in natural
bijection with `M` — membership in `edgeSubgraph M` of a vertex set
determines the edge it came from (`edgeOfSubgraph`).

* restriction: a colouring `φ` of `𝓗` restricts to a colouring of
  `edgeSubgraph M` (`restrictTo`), which is proper (by construction) and,
  if `φ` respects a list assignment `C`, the restriction respects `C` on
  the edges of `M` (`restrictTo_respects`).
* single-edge extension: a colouring of `edgeSubgraph M` extends to a
  colouring of `edgeSubgraph (insert f M)` by giving the new edge `f` a
  colour `c` distinct from the colours of the `M`-edges intersecting `f`
  (`extendColouring`), agreeing with the old colouring on `M`
  (`extendColouring_old`, `extendColouring_new`).
-/

/-- The subhypergraph on the edges of an edge subset `M : Set 𝓗`: the vertex
sets of the edges in `M`, viewed as a hypergraph on the same vertices. -/
def edgeSubgraph (𝓗 : Hypergraph (Fin n)) (M : Set 𝓗) : Hypergraph (Fin n) :=
  (fun x : 𝓗 => (x : Set (Fin n))) '' M

/-- Membership in `edgeSubgraph M`. -/
lemma mem_edgeSubgraph (𝓗 : Hypergraph (Fin n)) (M : Set 𝓗) (s : Set (Fin n)) :
    s ∈ edgeSubgraph 𝓗 M ↔ ∃ x : 𝓗, x ∈ M ∧ (x : Set (Fin n)) = s := by
  simp [edgeSubgraph]

/-- The subhypergraph of an edge subset is a subhypergraph of `𝓗`. -/
lemma edgeSubgraph_subset (𝓗 : Hypergraph (Fin n)) (M : Set 𝓗) : edgeSubgraph 𝓗 M ⊆ 𝓗 := by
  intro s hs
  rcases (mem_edgeSubgraph 𝓗 M s).1 hs with ⟨x, _hx, hEq⟩
  rw [← hEq]
  exact x.2

/-- An edge of `𝓗` whose vertex set lies in the subgraph of `M` is a member
of `M` (vertex sets determine edges, as `𝓗` is a set of vertex sets). -/
lemma edgeOfSubgraph_mem {𝓗 : Hypergraph (Fin n)} (M : Set 𝓗) {x : 𝓗}
    (hx : (x : Set (Fin n)) ∈ edgeSubgraph 𝓗 M) : x ∈ M := by
  rcases (mem_edgeSubgraph 𝓗 M (x : Set (Fin n))).1 hx with ⟨y, hy, hEq⟩
  have hxy : x = y := by
    apply Subtype.ext
    exact hEq.symm
  simpa [hxy] using hy

/-- Restricting a colouring of `𝓗` to the edges of `M` gives a colouring of
the subhypergraph `edgeSubgraph M`. -/
def restrictTo {𝓗 : Hypergraph (Fin n)} {α : Type*} (φ : 𝓗.Coloring α)
    (M : Set 𝓗) : (edgeSubgraph 𝓗 M).Coloring α :=
  Hypergraph.Coloring.restrict (edgeSubgraph_subset 𝓗 M) φ

/-- The vertex set of an edge of `M` is an element of `edgeSubgraph M`. -/
lemma edge_mem_edgeSubgraph {𝓗 : Hypergraph (Fin n)} (M : Set 𝓗) {x : 𝓗} (hx : x ∈ M) :
    (x : Set (Fin n)) ∈ edgeSubgraph 𝓗 M :=
  (mem_edgeSubgraph 𝓗 M (x : Set (Fin n))).2 ⟨x, hx, rfl⟩

/-- The restricted colouring gives an edge of `M` the colour `φ` gives it. -/
lemma restrictTo_labels {𝓗 : Hypergraph (Fin n)} {α : Type*} (φ : 𝓗.Coloring α)
    (M : Set 𝓗) {x : 𝓗} (hx : x ∈ M) :
    (restrictTo φ M).labels ⟨(x : Set (Fin n)), edge_mem_edgeSubgraph M hx⟩ = φ.labels x := by
  unfold restrictTo
  change φ.labels (⟨(x : Set (Fin n)), edgeSubgraph_subset 𝓗 M (edge_mem_edgeSubgraph M hx)⟩ : 𝓗) = φ.labels x
  have heq : (⟨(x : Set (Fin n)), edgeSubgraph_subset 𝓗 M (edge_mem_edgeSubgraph M hx)⟩ : 𝓗) = x := by
    apply Subtype.ext
    rfl
  rw [heq]

/-- If `φ` respects the list assignment `C` on every edge, so does its
restriction to any edge subset (for the same lists, evaluated on the edges
of `M`). -/
lemma restrictTo_respects {𝓗 : Hypergraph (Fin n)} (φ : 𝓗.Coloring (Fin n))
    (M : Set 𝓗) (C : 𝓗 → Finset (Fin n))
    (hφC : ∀ e : 𝓗, φ.labels e ∈ C e) :
    ∀ x : 𝓗, ∀ hx : x ∈ M,
      (restrictTo φ M).labels ⟨(x : Set (Fin n)), edge_mem_edgeSubgraph M hx⟩ ∈ C x := by
  intro x hx
  rw [restrictTo_labels φ M hx]
  exact hφC x

/-- An element of `edgeSubgraph (insert f M)` whose vertex set is not
`f`'s lies in `edgeSubgraph M` (vertex sets determine edges). -/
lemma mem_edgeSubgraph_insert_left {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {f : 𝓗}
    {s : Set (Fin n)} (hs : s ∈ edgeSubgraph 𝓗 (insert f M))
    (hsne : s ≠ (f : Set (Fin n))) : s ∈ edgeSubgraph 𝓗 M := by
  classical
  rcases (mem_edgeSubgraph 𝓗 (insert f M) s).1 hs with ⟨y, hy, hEq⟩
  have hyM : y ∈ M := by
    rcases (Set.mem_insert_iff.mp hy) with hyf | hyM
    · exfalso
      apply hsne
      rw [← hEq, hyf]
    · exact hyM
  exact (mem_edgeSubgraph 𝓗 M s).2 ⟨y, hyM, hEq⟩

/-- The vertex set of an edge of `M` lies in the subgraph of `insert f M`. -/
lemma edge_mem_edgeSubgraph_insert {𝓗 : Hypergraph (Fin n)} (M : Set 𝓗) {f x : 𝓗}
    (hx : x ∈ M) : (x : Set (Fin n)) ∈ edgeSubgraph 𝓗 (insert f M) := by
  exact edge_mem_edgeSubgraph (insert f M) (by exact Or.inr hx)

/-- **Single-edge extension.**  A colouring of the edges of `M` extends to a
colouring of the edges of `insert f M` by giving the new edge `f` the colour
`c`, provided `c` is not used by any `M`-edge intersecting `f`. -/
noncomputable def extendColouring {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} (f : 𝓗)
    (_hfM : f ∉ M) (φM : (edgeSubgraph 𝓗 M).Coloring (Fin n)) (c : Fin n)
    (hc : ∀ e : 𝓗, (heM : e ∈ M) →
      ((e : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty →
        φM.labels ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph M heM⟩ ≠ c) :
    (edgeSubgraph 𝓗 (insert f M)).Coloring (Fin n) := by
  classical
  let lab : (edgeSubgraph 𝓗 (insert f M)) → Fin n := fun s =>
    if hsne : s.1 ≠ (f : Set (Fin n)) then
      φM.labels ⟨s.1, mem_edgeSubgraph_insert_left s.2 hsne⟩
    else c
  refine ⟨lab, ?_⟩
  intro s₁ s₂ hsd hnon
  dsimp [lab]
  by_cases h₁ : s₁.1 ≠ (f : Set (Fin n))
  · by_cases h₂ : s₂.1 ≠ (f : Set (Fin n))
    · -- both s₁ and s₂ are old edges of M: properness comes from φM
      rw [dif_pos h₁, dif_pos h₂]
      have h₂' : (⟨s₁.1, mem_edgeSubgraph_insert_left s₁.2 h₁⟩ : edgeSubgraph 𝓗 M) ≠
          ⟨s₂.1, mem_edgeSubgraph_insert_left s₂.2 h₂⟩ := by
        intro heq
        apply hsd
        apply Subtype.ext
        exact congrArg (fun t : edgeSubgraph 𝓗 M => (t : Set (Fin n))) heq
      have hint : (((⟨s₁.1, mem_edgeSubgraph_insert_left s₁.2 h₁⟩ : edgeSubgraph 𝓗 M) : Set (Fin n)) ∩
          ((⟨s₂.1, mem_edgeSubgraph_insert_left s₂.2 h₂⟩ : edgeSubgraph 𝓗 M) : Set (Fin n))).Nonempty := by
        simpa using hnon
      exact φM.isColoring (⟨s₁.1, mem_edgeSubgraph_insert_left s₁.2 h₁⟩) (⟨s₂.1, mem_edgeSubgraph_insert_left s₂.2 h₂⟩) h₂' hint
    · -- s₂ is the new edge f, s₁ an old edge intersecting it
      rw [dif_pos h₁, dif_neg h₂]
      have hs₂f : s₂.1 = (f : Set (Fin n)) := of_not_not h₂
      rcases (mem_edgeSubgraph 𝓗 M s₁.1).1 (mem_edgeSubgraph_insert_left s₁.2 h₁) with ⟨y, hyM, hEq⟩
      have hneq : φM.labels ⟨s₁.1, mem_edgeSubgraph_insert_left s₁.2 h₁⟩ ≠ c := by
        have hint : ((y : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty := by
          have h1 : (⟨s₁.1, mem_edgeSubgraph_insert_left s₁.2 h₁⟩ : edgeSubgraph 𝓗 M) =
              ⟨(y : Set (Fin n)), edge_mem_edgeSubgraph M hyM⟩ := by
            apply Subtype.ext
            exact hEq.symm
          have h1' : s₁.1 = (y : Set (Fin n)) :=
            congrArg (fun t : edgeSubgraph 𝓗 M => (t : Set (Fin n))) h1
          simpa [h1', hs₂f] using hnon
        have hc' := hc y hyM hint
        have hlab : φM.labels ⟨s₁.1, mem_edgeSubgraph_insert_left s₁.2 h₁⟩ =
            φM.labels ⟨(y : Set (Fin n)), edge_mem_edgeSubgraph M hyM⟩ := by
          apply congrArg φM.labels
          apply Subtype.ext
          exact hEq.symm
        rwa [← hlab] at hc'
      exact hneq
  · -- s₁ is the new edge f
    have hs₁f : s₁.1 = (f : Set (Fin n)) := of_not_not h₁
    by_cases h₂ : s₂.1 ≠ (f : Set (Fin n))
    · -- s₂ an old edge intersecting f
      rw [dif_neg h₁, dif_pos h₂]
      rcases (mem_edgeSubgraph 𝓗 M s₂.1).1 (mem_edgeSubgraph_insert_left s₂.2 h₂) with ⟨y, hyM, hEq⟩
      have hneq : φM.labels ⟨s₂.1, mem_edgeSubgraph_insert_left s₂.2 h₂⟩ ≠ c := by
        have hint : ((y : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty := by
          have h2 : (⟨s₂.1, mem_edgeSubgraph_insert_left s₂.2 h₂⟩ : edgeSubgraph 𝓗 M) =
              ⟨(y : Set (Fin n)), edge_mem_edgeSubgraph M hyM⟩ := by
            apply Subtype.ext
            exact hEq.symm
          have h2' : s₂.1 = (y : Set (Fin n)) :=
            congrArg (fun t : edgeSubgraph 𝓗 M => (t : Set (Fin n))) h2
          simpa [h2', hs₁f, Set.inter_comm] using hnon
        have hc' := hc y hyM hint
        have hlab : φM.labels ⟨s₂.1, mem_edgeSubgraph_insert_left s₂.2 h₂⟩ =
            φM.labels ⟨(y : Set (Fin n)), edge_mem_edgeSubgraph M hyM⟩ := by
          apply congrArg φM.labels
          apply Subtype.ext
          exact hEq.symm
        rwa [← hlab] at hc'
      exact hneq.symm
    · -- both s₁ and s₂ are f: s₁ = s₂, contradicting hsd
      exfalso
      apply hsd
      apply Subtype.ext
      exact hs₁f.trans (of_not_not h₂).symm


/-- `edgeSubgraph` is monotone in the edge subset. -/
lemma edgeSubgraph_mono {𝓗 : Hypergraph (Fin n)} {M₁ M₂ : Set 𝓗} (h : M₁ ⊆ M₂) :
    edgeSubgraph 𝓗 M₁ ⊆ edgeSubgraph 𝓗 M₂ := by
  intro s hs
  rcases (mem_edgeSubgraph 𝓗 M₁ s).1 hs with ⟨x, hx, hEq⟩
  exact (mem_edgeSubgraph 𝓗 M₂ s).2 ⟨x, h hx, hEq⟩

/-- **The extension agrees with the old colouring on the edges of `M`.**  The
colour that `extendColouring` gives to an element of `edgeSubgraph M` (viewed
inside `edgeSubgraph (insert f M)`) is the colour `φM` gives it. -/
lemma extendColouring_agrees {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {f : 𝓗}
    (hfM : f ∉ M) (φM : (edgeSubgraph 𝓗 M).Coloring (Fin n)) (c : Fin n)
    (hc : ∀ e : 𝓗, (heM : e ∈ M) →
      ((e : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty →
        φM.labels ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph M heM⟩ ≠ c)
    {u : edgeSubgraph 𝓗 M} :
    (extendColouring f hfM φM c hc).labels
      ⟨u.1, edgeSubgraph_mono (Set.subset_insert f M) u.2⟩ = φM.labels u := by
  classical
  have hne : u.1 ≠ (f : Set (Fin n)) := by
    intro hEq
    apply hfM
    have hfM' : (f : Set (Fin n)) ∈ edgeSubgraph 𝓗 M := by
      rw [← hEq]
      exact u.2
    exact edgeOfSubgraph_mem M hfM'
  unfold extendColouring
  simp only [dif_pos hne]

/-- **The extension colours the new edge `f` with `c`.**  The colour that
`extendColouring` gives to the element of `edgeSubgraph (insert f M)` whose
vertex set is `f`'s is `c`. -/
lemma extendColouring_self {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {f : 𝓗}
    (hfM : f ∉ M) (φM : (edgeSubgraph 𝓗 M).Coloring (Fin n)) (c : Fin n)
    (hc : ∀ e : 𝓗, (heM : e ∈ M) →
      ((e : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty →
        φM.labels ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph M heM⟩ ≠ c)
    {u : edgeSubgraph 𝓗 (insert f M)} (hu : u.1 = (f : Set (Fin n))) :
    (extendColouring f hfM φM c hc).labels u = c := by
  classical
  have hnot : ¬ u.1 ≠ (f : Set (Fin n)) := by
    intro h
    exact h hu
  unfold extendColouring
  simp only [dif_neg hnot]


/-! ## Initial segments of an edge ordering

For an ordering `ord : 𝓗 ≃ Fin k` (rank function) the *initial segment of
length `m`* is the set of the first `m` edges:
`EdgeOrderSegment ord m = {f | (ord f : ℕ) < m}`.  The paper's initial
segment `H⪯e = {f : H | f ⪯ e}` (edges up to and including `e`) is
`EdgeOrderSegment ord ((ord e : ℕ) + 1)`.  The lemmas below are the
segment plumbing used by the greedy extension argument: the membership
criterion, monotonicity of segments, and the *successor step* — colouring
the next edge `f` adds it to the segment, i.e.
`insert f (segment (ord f)) = segment (ord f + 1)` (equivalently
`H⪯f = H⪯e ∪ {f}` when `f` is the successor of `e`). -/

/-- The initial segment of length `m` of the ordering `ord`: the edges of
rank `< m` (the first `m` edges in the order). -/
def EdgeOrderSegment {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (m : ℕ) : Set 𝓗 :=
  {f : 𝓗 | (ord f : ℕ) < m}

/-- Membership in an initial segment: the edge's rank is below the bound. -/
@[simp]
lemma mem_EdgeOrderSegment {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    {m : ℕ} {f : 𝓗} : f ∈ EdgeOrderSegment ord m ↔ (ord f : ℕ) < m := by
  rfl

/-- The initial segment of length `0` is empty. -/
@[simp]
lemma EdgeOrderSegment_zero {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k) :
    EdgeOrderSegment ord 0 = ∅ := by
  ext f
  simp

/-- If every edge lies below the bound, the segment is the whole edge set. -/
lemma EdgeOrderSegment_univ_of_all {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    {m : ℕ} (h : ∀ f : 𝓗, (ord f : ℕ) < m) : EdgeOrderSegment ord m = Set.univ := by
  ext f
  simp [h f]

/-- Initial segments are monotone in the bound: more edges are included. -/
lemma EdgeOrderSegment_mono {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) : EdgeOrderSegment ord m₁ ⊆ EdgeOrderSegment ord m₂ := by
  intro f hf
  rw [mem_EdgeOrderSegment] at hf ⊢
  exact lt_of_lt_of_le hf h

/-- **Successor step.**  Adding the edge `f` to the segment of its own rank
gives the segment one longer: `insert f (segment (ord f)) =
segment (ord f + 1)` (in paper terms `H⪯f = H⪯e ∪ {f}` for `e` the
predecessor of `f`). -/
lemma insert_succ {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k) (f : 𝓗) :
    insert f (EdgeOrderSegment ord ((ord f : ℕ))) = EdgeOrderSegment ord ((ord f : ℕ) + 1) := by
  classical
  ext g
  constructor
  · intro hg
    rcases (Set.mem_insert_iff.mp hg) with hgf | hseg
    · -- g = f: rank of f is below rank f + 1
      subst g
      rw [mem_EdgeOrderSegment]
      exact Nat.lt_succ_self (ord f : ℕ)
    · -- g in the segment: rank g < rank f, hence < rank f + 1
      rw [mem_EdgeOrderSegment] at hseg ⊢
      exact Nat.lt_succ_of_lt hseg
  · intro hg
    rw [mem_EdgeOrderSegment] at hg
    -- rank g < rank f + 1: g = f or rank g < rank f
    by_cases hgf : g = f
    · rw [hgf]
      simp
    · right
      rw [mem_EdgeOrderSegment]
      have hle : (ord g : ℕ) ≤ (ord f : ℕ) := Nat.le_of_lt_succ hg
      have hlt : (ord g : ℕ) < (ord f : ℕ) ∨ (ord g : ℕ) = (ord f : ℕ) := lt_or_eq_of_le hle
      rcases hlt with hlt | heq
      · exact hlt
      · exfalso
        apply hgf
        apply ord.injective
        apply Fin.ext
        exact heq

/-! ## The heavy colours `C₂` of the greedy argument

In the proof of Prop 6.9 the colour set `C₂` consists of the colours whose
colour class already covers at least `α₂n/2` vertices.  `HeavyColours` is
that set (for a colouring of any hypergraph on `Fin n`); its size is
bounded by Prop 6.8(i) (`card_bigColourClasses_le`), giving the paper's
`|C₂| ≤ 2n/(α₂(r−1))` when every edge has size `≥ r`.  This is the bound
that contradicts `|C₂| ≥ α₁n/2` at the end of the Prop 6.9 proof. -/

/-- The colours whose class covers at least `α₂n/2` vertices — the set the
paper calls `C₂`. -/
def HeavyColours {𝓗 : Hypergraph (Fin n)} (α₂ : ℝ) (φ : 𝓗.Coloring (Fin n)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun c : Fin n => (α₂ / 2 : ℝ) * (n : ℝ) ≤ (φ.classVertexCount c : ℝ))

/-- Membership in `HeavyColours`. -/
lemma mem_HeavyColours {𝓗 : Hypergraph (Fin n)} (α₂ : ℝ) (φ : 𝓗.Coloring (Fin n))
    (c : Fin n) : c ∈ HeavyColours α₂ φ ↔
      (α₂ / 2 : ℝ) * (n : ℝ) ≤ (φ.classVertexCount c : ℝ) := by
  classical
  simp [HeavyColours]

/-- **`|C₂| ≤ 2n/(α₂(r−1))`** (paper, Prop 6.9 proof): for a proper
edge-colouring of a linear hypergraph whose edges all have size at least
`r`, at most `2n/(α₂(r−1))` colours can have a class covering at least
`α₂n/2` vertices.  (Follows from Prop 6.8(i) with the halved threshold
`α₂/2` and edge size `r − 1`.) -/
theorem heavyColours_card_le {n r : ℕ} {α₂ : ℝ} (h2n : 2 ≤ n) (h2r : 2 ≤ r)
    (hα₂ : 0 < α₂) {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, (r : ℕ) ≤ edgeSize (e : Set (Fin n)))
    (φ : 𝓗.Coloring (Fin n)) :
    ((HeavyColours α₂ φ).card : ℝ) ≤ (2 : ℝ) * (n : ℝ) / (α₂ * ((r : ℝ) - 1)) := by
  classical
  have hr' : 1 ≤ r - 1 := by omega
  have hbig' : ∀ e : 𝓗, ((r - 1 : ℕ) + 1) ≤ edgeSize (e : Set (Fin n)) := by
    intro e
    have := hsize e
    omega
  have hle := card_bigColourClasses_le (h2n := h2n) (hα := half_pos hα₂) (hr := hr')
    (𝓗 := 𝓗) (hlin := hlin) (hbig := hbig') (φ := φ)
  -- hle : ((univ.filter (fun c => (α₂/2)*n ≤ classVertexCount)).card : ℝ) ≤ n / ((α₂/2) * ((r-1 : ℕ) : ℝ))
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    norm_num
  have hRHS : (n : ℝ) / ((α₂ / 2) * ((r - 1 : ℕ) : ℝ)) = (2 : ℝ) * (n : ℝ) / (α₂ * ((r : ℝ) - 1)) := by
    rw [hcast]
    field_simp [hα₂.ne']
  have hmem : ((Finset.univ : Finset (Fin n)).filter
      (fun c : Fin n => (α₂ / 2 : ℝ) * (n : ℝ) ≤ (φ.classVertexCount c : ℝ))).card =
      (HeavyColours α₂ φ).card := by
    rfl
  rwa [hmem, hRHS] at hle
/-- The embedding of `M`-elements inside `edgeSubgraph (insert f M)`. -/
def segmentEmbed {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {f : 𝓗}
    (u : edgeSubgraph 𝓗 M) : edgeSubgraph 𝓗 (insert f M) :=
  ⟨u.1, edgeSubgraph_mono (Set.subset_insert f M) u.2⟩

/-- `segmentEmbed` is injective (it only adds a membership proof). -/
lemma segmentEmbed_injective {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {f : 𝓗} :
    Function.Injective (segmentEmbed (𝓗 := 𝓗) (M := M) (f := f)) := by
  intro u v h
  apply Subtype.ext
  exact congrArg (fun t : edgeSubgraph 𝓗 (insert f M) => (t : Set (Fin n))) h

/-- For every colour `d ≠ c`, the colour class of `d` in the extension is the
image under `segmentEmbed` of the colour class of `d` in `φM` (the new edge
`f` has colour `c`, so only the class of `c` changes). -/
lemma colorClass_extend_ne {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {f : 𝓗}
    (hfM : f ∉ M) (φM : (edgeSubgraph 𝓗 M).Coloring (Fin n)) (c d : Fin n) (hdc : d ≠ c)
    (hc : ∀ e : 𝓗, (heM : e ∈ M) →
      ((e : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty →
        φM.labels ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph M heM⟩ ≠ c) :
    (extendColouring f hfM φM c hc).colorClass d =
      segmentEmbed '' (φM.colorClass d) := by
  classical
  ext u
  constructor
  · intro hu
    rw [mem_colorClass] at hu
    have huM : u.1 ≠ (f : Set (Fin n)) := by
      intro hEq
      apply hdc
      have hc' : (extendColouring f hfM φM c hc).labels u = c := by
        rw [extendColouring_self (f := f) hfM φM c hc (u := u) hEq]
      rw [hu.symm]
      exact hc'
    have hM : u.1 ∈ edgeSubgraph 𝓗 M := mem_edgeSubgraph_insert_left u.2 huM
    let v : edgeSubgraph 𝓗 M := ⟨u.1, hM⟩
    refine (Set.mem_image segmentEmbed (φM.colorClass d) u).mpr ⟨v, ?_, ?_⟩
    · rw [mem_colorClass]
      have hag := extendColouring_agrees hfM φM c hc (u := v)
      have heq : segmentEmbed v = u := by
        apply Subtype.ext
        rfl
      rw [← hu, ← heq]
      exact hag.symm
    · rfl
  · intro hu
    rcases (Set.mem_image segmentEmbed (φM.colorClass d) u).mp hu with ⟨v, hv, rfl⟩
    rw [mem_colorClass]
    rw [mem_colorClass] at hv
    have hag := extendColouring_agrees hfM φM c hc (u := v)
    rw [← hv]
    exact hag



/-! ### Boundedness of the extension (complete)

The lemmas below prove the boundedness half of the greedy extension step of
Prop 6.9: extending an `α₂`-bounded colouring of a prefix by a *small* new
edge `f` (`|f| < α₂n/2`, i.e. `f ∉ Hbig`) with a *light* colour `c`
(`c ∉ C₂`: the old class covers `< α₂n/2` vertices) keeps the colouring
`α₂`-bounded.  The colour class of `c` in the extension is the old class
plus the new edge (`edgeSetFamily_extend_c`); covered-vertex counts are
subadditive (`FVC_insert_le`); the other classes and their covered families
are unchanged (`colorClass_extend_ne`, `edgeSetFamily_extend_ne`). -/

/-- **The colour-class family of `c` in the extension is the old class
family plus the vertex set of the new edge `f`.** -/
lemma edgeSetFamily_extend_c {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {f : 𝓗}
    (hfM : f ∉ M) (φM : (edgeSubgraph 𝓗 M).Coloring (Fin n)) (c : Fin n)
    (hc : ∀ e : 𝓗, (heM : e ∈ M) →
      ((e : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty →
        φM.labels ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph M heM⟩ ≠ c) :
    EdgeSetFamily ((extendColouring f hfM φM c hc).colorClass c) =
      insert (f : Set (Fin n)) (EdgeSetFamily (φM.colorClass c)) := by
  classical
  ext e
  rw [Finset.mem_insert]
  constructor
  · intro he
    rcases (mem_EdgeSetFamily ((extendColouring f hfM φM c hc).colorClass c) e).1 he with ⟨x, hx, hEq⟩
    rw [mem_colorClass] at hx
    by_cases hEqf : x.1 = (f : Set (Fin n))
    · exact Or.inl (by rw [← hEq]; exact hEqf)
    · right
      have hM : x.1 ∈ edgeSubgraph 𝓗 M := mem_edgeSubgraph_insert_left x.2 hEqf
      let v : edgeSubgraph 𝓗 M := ⟨x.1, hM⟩
      have hvc : v ∈ φM.colorClass c := by
        rw [mem_colorClass]
        have hag := extendColouring_agrees hfM φM c hc (u := v)
        have heq : segmentEmbed v = x := by
          apply Subtype.ext
          rfl
        have hx' : (extendColouring f hfM φM c hc).labels (segmentEmbed v) = c := by
          simpa [heq] using hx
        exact hag.symm.trans hx'
      have hvEq : (v : Set (Fin n)) = e := by
        simpa [v] using hEq
      exact (mem_EdgeSetFamily (φM.colorClass c) e).2 ⟨v, hvc, hvEq⟩
  · intro he
    rcases he with hEqf | hefam
    · -- e = f.val: witness the new edge itself (it has colour c)
      have hef : e = (f : Set (Fin n)) := hEqf
      let x : edgeSubgraph 𝓗 (insert f M) := ⟨e, by
        rw [hef]
        exact edge_mem_edgeSubgraph (insert f M) (by exact Or.inl rfl)⟩
      have hxc : x ∈ (extendColouring f hfM φM c hc).colorClass c := by
        rw [mem_colorClass]
        rw [extendColouring_self (f := f) hfM φM c hc (u := x) (by simpa [x] using hef)]
      exact (mem_EdgeSetFamily ((extendColouring f hfM φM c hc).colorClass c) e).2 ⟨x, hxc, by rfl⟩
    · -- e is a colour-c edge of M: its embedding keeps colour c
      rcases (mem_EdgeSetFamily (φM.colorClass c) e).1 hefam with ⟨v, hv, hEq⟩
      let x : edgeSubgraph 𝓗 (insert f M) := segmentEmbed v
      have hxc : x ∈ (extendColouring f hfM φM c hc).colorClass c := by
        rw [mem_colorClass]
        rw [mem_colorClass] at hv
        have hag := extendColouring_agrees hfM φM c hc (u := v)
        dsimp [x]
        exact hag.trans hv
      have hxEq : (x : Set (Fin n)) = e := by
        dsimp [x]
        exact hEq
      exact (mem_EdgeSetFamily ((extendColouring f hfM φM c hc).colorClass c) e).2 ⟨x, hxc, hxEq⟩

/-- Covered-vertex count of a family plus a single set is subadditive. -/
lemma FVC_insert_le {s : Set (Fin n)} (t : Finset (Set (Fin n))) :
    FamilyVertexCount (insert s t) ≤ FamilyVertexCount t + s.ncard := by
  classical
  have hsets : FamilyVertices (insert s t) = FamilyVertices t ∪ s := by
    ext v
    constructor
    · intro hv
      rcases hv with ⟨e, he, hv⟩
      rcases (Finset.mem_insert.mp he) with rfl | he
      · exact Or.inr hv
      · exact Or.inl ⟨e, he, hv⟩
    · intro hv
      rcases hv with hv | hv
      · rcases hv with ⟨e, he, hv⟩
        exact ⟨e, (Finset.mem_insert.mpr (Or.inr he)), hv⟩
      · exact ⟨s, (Finset.mem_insert.mpr (Or.inl rfl)), hv⟩
  have hle : (FamilyVertices t ∪ s).ncard ≤ (FamilyVertices t).ncard + s.ncard := by
    exact Set.ncard_union_le (FamilyVertices t) s
  simpa [FamilyVertexCount, hsets] using hle

/-- The colour-class family of a colour `d ≠ c` is unchanged by the
extension (the new edge has colour `c`). -/
lemma edgeSetFamily_extend_ne {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {f : 𝓗}
    (hfM : f ∉ M) (φM : (edgeSubgraph 𝓗 M).Coloring (Fin n)) (c d : Fin n) (hdc : d ≠ c)
    (hc : ∀ e : 𝓗, (heM : e ∈ M) →
      ((e : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty →
        φM.labels ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph M heM⟩ ≠ c) :
    EdgeSetFamily ((extendColouring f hfM φM c hc).colorClass d) = EdgeSetFamily (φM.colorClass d) := by
  classical
  rw [colorClass_extend_ne hfM φM c d hdc hc]
  ext e
  constructor
  · intro he
    rcases (mem_EdgeSetFamily (segmentEmbed '' (φM.colorClass d)) e).1 he with ⟨x, hx, hEq⟩
    rcases (Set.mem_image segmentEmbed (φM.colorClass d) x).mp hx with ⟨v, hv, rfl⟩
    exact (mem_EdgeSetFamily (φM.colorClass d) e).2 ⟨v, hv, hEq⟩
  · intro he
    rcases (mem_EdgeSetFamily (φM.colorClass d) e).1 he with ⟨v, hv, hEq⟩
    exact (mem_EdgeSetFamily (segmentEmbed '' (φM.colorClass d)) e).2
      ⟨segmentEmbed v, (Set.mem_image segmentEmbed (φM.colorClass d) (segmentEmbed v)).mpr ⟨v, hv, rfl⟩, hEq⟩

/-- The class of `c` in the extension covers at most the old class plus the
new edge (real subadditivity). -/
lemma FVC_colorClass_extend_c_le {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {f : 𝓗}
    (hfM : f ∉ M) (φM : (edgeSubgraph 𝓗 M).Coloring (Fin n)) (c : Fin n)
    (hc : ∀ e : 𝓗, (heM : e ∈ M) →
      ((e : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty →
        φM.labels ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph M heM⟩ ≠ c) :
    (FamilyVertexCount (EdgeSetFamily ((extendColouring f hfM φM c hc).colorClass c)) : ℝ) ≤
      (FamilyVertexCount (EdgeSetFamily (φM.colorClass c)) : ℝ) +
        (edgeSize (f : Set (Fin n)) : ℝ) := by
  classical
  have hfam := edgeSetFamily_extend_c hfM φM c hc
  have hle := FVC_insert_le (s := (f : Set (Fin n))) (t := EdgeSetFamily (φM.colorClass c))
  have hsz : ((f : Set (Fin n)).ncard) = edgeSize (f : Set (Fin n)) := by
    exact (edgeSize_eq_ncard (f : Set (Fin n))).symm
  have hle' : FamilyVertexCount (EdgeSetFamily ((extendColouring f hfM φM c hc).colorClass c)) ≤
      FamilyVertexCount (EdgeSetFamily (φM.colorClass c)) + edgeSize (f : Set (Fin n)) := by
    simpa [hfam, hsz] using hle
  exact_mod_cast hle'

/-- **Extending keeps `α₂`-boundedness** (paper Prop 6.9 proof, small-edge
case): if `φM` is `α₂`-bounded, the new edge `f` is small
(`|f| < α₂n/2`, i.e. `f ∉ Hbig`) and the colour `c` is light
(`c ∉ C₂`: its old class covers `< α₂n/2` vertices), then the extension is
`α₂`-bounded.  (The classes different from `c` are unchanged; the class of
`c` covers at most `FVC(old class c) + |f| < α₂n/2 + α₂n/2 ≤ α₂n`.) -/
theorem extendColouring_bounded {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {f : 𝓗}
    (hfM : f ∉ M) (φM : (edgeSubgraph 𝓗 M).Coloring (Fin n)) (c : Fin n) (α₂ : ℝ)
    (hc : ∀ e : 𝓗, (heM : e ∈ M) →
      ((e : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty →
        φM.labels ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph M heM⟩ ≠ c)
    (hbdd : φM.AlphaBounded α₂)
    (hlight : (FamilyVertexCount (EdgeSetFamily (φM.colorClass c)) : ℝ) < (α₂ / 2 : ℝ) * (n : ℝ))
    (hsmall : (edgeSize (f : Set (Fin n)) : ℝ) < (α₂ / 2 : ℝ) * (n : ℝ)) :
    (extendColouring f hfM φM c hc).AlphaBounded α₂ := by
  classical
  intro d
  by_cases hdc : d = c
  · subst d
    right
    have hFVC := FVC_colorClass_extend_c_le hfM φM c hc
    have hlt : (FamilyVertexCount
        (EdgeSetFamily ((extendColouring f hfM φM c hc).colorClass c)) : ℝ) < α₂ * (n : ℝ) := by
      nlinarith
    exact le_of_lt hlt
  · rcases hbdd d with hOne | hBdd
    · left
      have hcl := colorClass_extend_ne hfM φM c d hdc hc
      rw [hcl]
      have hcard : ((segmentEmbed (𝓗 := 𝓗) (M := M) (f := f)) '' (φM.colorClass d)).ncard =
          (φM.colorClass d).ncard := by
        exact Set.ncard_image_of_injective (φM.colorClass d) (segmentEmbed_injective (𝓗 := 𝓗) (M := M) (f := f))
      rwa [hcard]
    · right
      have hfam := edgeSetFamily_extend_ne hfM φM c d hdc hc
      rwa [hfam]

/-- **Fresh colour** (pigeonhole): if a list `C` is larger than a set `S` of
forbidden colours, some colour of `C` is not in `S`. -/
lemma exists_color_unused {C S : Finset (Fin n)} (h : S.card < C.card) :
    ∃ c : Fin n, c ∈ C ∧ c ∉ S := by
  classical
  by_contra hc
  have hsub : C ⊆ S := by
    intro c hcC
    by_contra hcs
    exact hc ⟨c, hcC, hcs⟩
  exact (not_lt_of_ge (Finset.card_le_card hsub)) h

/-- The union of two colour sets is no larger than the sum of their sizes
(reals; used to bound `|C(f)| ≤ |C₁| + |C₂|`). -/
lemma card_union_le_add {A B : Finset (Fin n)} :
    ((A ∪ B).card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) := by
  exact_mod_cast (Finset.card_union_le A B)

/-!
## Prop 6.9: the maximality-over-prefixes blueprint

The greedy proof of `Prop69Instance` runs on the *natural-index* segments
`S_m := EdgeOrderSegment ord m` (`S_0 = ∅`, `S_k = all edges`), colouring
the first `m` edges.  For `m ≤ k` write `Colourable m` for: there is an
`α₂`-bounded proper colouring of `edgeSubgraph 𝓗 S_m` respecting the lists
`C`.  `Colourable 0` holds (empty colouring); choose the largest
`m* ≤ k` with `Colourable m*` (the set of such `m` is nonempty and bounded
by `k`, hence has a maximum).

**Claim: `m* = k`.**  Suppose `m* < k` and let `f` be the next edge, the
unique edge with `(ord f : ℕ) = m*` (exists since `m* < k`).  If some
colour `c ∈ C(f)` can be assigned to `f` — proper (c avoids the colours of
the coloured edges intersecting `f`, the `C₁` condition) and bounded
(c is *light*: `c ∉ C₂`, i.e. its old class covers `< α₂n/2` vertices, or
the new edge is small enough) — then `extendColouring_bounded` gives
`Colourable (m* + 1)`, contradicting the maximality of `m*`.

Two cases for why such a colour always exists (the honest corrections to
the paper's sketch, which uses the false bound `e(Hbig) ≤ 4/α₂`):

1. **`f` is huge** (`|f| ≥ α₂n/2`, i.e. `f ∈ Hbig`).  Give `f` a *fresh*
   colour not used anywhere in the prefix: its class is then `{f}` (bounded
   via the "single edge" disjunct).  A fresh colour exists by
   `exists_color_unused` because the number of colours used in the prefix is
   at most `m* = #{edges before f}`, all of which are huge when `f` is
   (huge edges form an initial segment of the order, by the Hbig-first
   reordering), and
   `m* ≤ #{huge edges} ≤ n(n−1)/(⌈α₂n/2⌉(⌈α₂n/2⌉−1)) ≤ 2·(4/α₂²)`
   (`card_edges_size_ge_le`), which is `< α₁n/2` for `n ≥ n₀` by the
   hierarchy `1/n₀ ≪ 1/r ≪ α₁, α₂`; since `|C(f)| ≥ d⪯(f) + α₁n` and
   `d⪯(f) ≥ 0`, the prefix uses fewer than `|C(f)|` colours.
   (This is where the paper's `(2.2)`-based count must be replaced by the
   honest pair count `card_edges_size_ge_le`.)
2. **`f` is small** (`|f| < α₂n/2`).  If every colour of `C(f)` were
   forbidden (`C(f) ⊆ C₁ ∪ C₂`, where `C₁` are the colours of the coloured
   edges intersecting `f` and `C₂` the heavy colours of the prefix), then
   `|C(f)| ≤ |C₁| + |C₂|` (`card_union_le_add`), with `|C₁| ≤ d⪯(f)`
   (colours used on a set of at most `d⪯(f)` edges — a subset of
   `precedingNeighbours ord f`) and `|C₂| ≤ 2n/(α₂(r−1))`
   (`heavyColours_card_le`, since all edges have size `≥ r`), so
   `d⪯(f) + α₁n ≤ |C(f)| ≤ d⪯(f) + |C₂| ≤ d⪯(f) + 2n/(α₂(r−1))`,
   contradicting the margin `2n/(α₂(r−1)) < α₁n/2` recorded in
   `Prop69Instance`.  Hence some `c ∈ C(f) ∖ (C₁ ∪ C₂)` exists, and
   `extendColouring_bounded` (with `|f| < α₂n/2`) gives
   `Colourable (m* + 1)`, contradiction.

So `m* = k`: the whole edge set is colourable.  The colouring of
`edgeSubgraph 𝓗 S_k = edgeSubgraph 𝓗 (all of 𝓗)` transports to a colouring
of `𝓗` (the two hypergraphs are equal: `val '' (all of 𝓗) = 𝓗`), yielding
the conclusion of `Prop69Instance`.

All of these steps are now formalised below: the `SegmentColourable`
predicate and the maximal prefix `m*` (`exists_maxSegmentColourable`), the
successor edge, the fresh-colour (huge) and `C₁ ∪ C₂` (small) counting
arguments, and the transport from `edgeSubgraph 𝓗 (all of 𝓗)` to `𝓗`.
They assemble into the theorem `greedy_colouring_hugeFirst`: Prop 6.9 for
orderings that put all big edges (those of size ≥ α₂n/2) first, under the
two margins `2n/(α₂(r−1)) < α₁n/2` and `#big < α₁n`.  The honest count of
big edges (`card_edges_size_ge_le` from the pair bound) supplies `#big` at
the level of the `≪`-hierarchy; lifting the huge-first restriction to an
arbitrary ordering by reordering (at the cost of halving `α₁`) is the
remaining reordering step recorded in `Prop69Instance`.
-/

/-! ## The `SegmentColourable` predicate and maximal prefixes

Prop 6.9's greedy proof processes the edges in the order `ord`, colouring
the first `m` edges (the segment `EdgeOrderSegment ord m`) and maintaining
`α₂`-boundedness and list-respect.  `SegmentColourable ord α₂ C m` says
that such a colouring of the first `m` edges exists.  The empty segment is
always colourable (`segmentColourable_zero`), and since `m` is bounded by
`k` (the number of edges), the colourable segments have a maximal length
(`exists_maxSegmentColourable`).  The greedy argument shows the maximum is
`k`, i.e. the whole edge set is colourable. -/

/-- Transporting a colouring along an equality of hypergraphs. -/
def Coloring.cast {𝓖₁ 𝓖₂ : Hypergraph (Fin n)} {α : Type*} (h : 𝓖₁ = 𝓖₂)
    (φ : 𝓖₁.Coloring α) : 𝓖₂.Coloring α := by
  subst h
  exact φ

/-- The empty hypergraph is colourable into any colour type. -/
def colouringEmpty {α : Type*} : (∅ : Hypergraph (Fin n)).Coloring α where
  labels x := False.elim x.2
  isColoring := by
    intro x
    exact False.elim x.2

/-- The colouring of the empty hypergraph is α-bounded (all classes are
empty, hence have at most one edge). -/
lemma colouringEmpty_AlphaBounded {α₂ : ℝ} :
    (colouringEmpty (n := n) (α := Fin n)).AlphaBounded α₂ := by
  intro c
  left
  have hcl : (colouringEmpty (n := n) (α := Fin n)).colorClass c = ∅ := by
    ext x
    constructor
    · intro hx
      exact False.elim x.2
    · intro hx
      exact False.elim x.2
  rw [hcl]
  simp

/-- The subgraph of the empty edge subset is the empty hypergraph. -/
lemma edgeSubgraph_empty (𝓗 : Hypergraph (Fin n)) :
    edgeSubgraph 𝓗 ∅ = (∅ : Hypergraph (Fin n)) := by
  ext s
  simp [edgeSubgraph]


/-- **`SegmentColourable`**: the first `m` edges of the ordering (the
initial segment `EdgeOrderSegment ord m`) admit an `α₂`-bounded proper
edge-colouring respecting the list assignment `C`. -/
def SegmentColourable {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (α₂ : ℝ) (C : 𝓗 → Finset (Fin n)) (m : ℕ) : Prop :=
  ∃ φ : (edgeSubgraph 𝓗 (EdgeOrderSegment ord m)).Coloring (Fin n),
    φ.AlphaBounded α₂ ∧
    ∀ x : 𝓗, ∀ hx : x ∈ EdgeOrderSegment ord m,
      φ.labels ⟨(x : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord m) hx⟩ ∈ C x

/-- The subgraph of the empty segment has no elements (there are no edges of
rank `< 0`). -/
lemma edgeSubgraph_segment_zero_empty {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (x : edgeSubgraph 𝓗 (EdgeOrderSegment ord 0)) : False := by
  rcases (mem_edgeSubgraph 𝓗 (EdgeOrderSegment ord 0) x.1).1 x.2 with ⟨y, hy, hEq⟩
  rw [EdgeOrderSegment_zero] at hy
  exact hy

/-- Any hypergraph with no edges is colourable (into any colour type). -/
def colouringOfEmptyType {𝓖 : Hypergraph (Fin n)} {α : Type*}
    (hempty : ∀ _x : 𝓖, False) : 𝓖.Coloring α where
  labels x := False.elim (hempty x)
  isColoring := by
    intro x
    exact False.elim (hempty x)

/-- The colouring of an edgeless hypergraph is α-bounded (every colour
class is empty). -/
lemma colouringOfEmptyType_AlphaBounded {𝓖 : Hypergraph (Fin n)} {α₂ : ℝ}
    (hempty : ∀ _x : 𝓖, False) :
    (colouringOfEmptyType (α := Fin n) hempty).AlphaBounded α₂ := by
  intro c
  left
  have hcl : (colouringOfEmptyType (α := Fin n) hempty).colorClass c = ∅ := by
    ext x
    constructor
    · intro _hx
      exact False.elim (hempty x)
    · intro _hx
      exact False.elim (hempty x)
  rw [hcl]
  simp

/-- The empty segment is colourable (vacuously): its subgraph has no edges,
so the edgeless colouring is `α₂`-bounded and trivially respects `C`. -/
lemma segmentColourable_zero {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (α₂ : ℝ) (C : 𝓗 → Finset (Fin n)) : SegmentColourable ord α₂ C 0 := by
  classical
  let hempty : ∀ x : edgeSubgraph 𝓗 (EdgeOrderSegment ord 0), False :=
    edgeSubgraph_segment_zero_empty ord
  refine ⟨colouringOfEmptyType hempty, ?_, ?_⟩
  · exact colouringOfEmptyType_AlphaBounded hempty
  · intro x hx
    exfalso
    rw [EdgeOrderSegment_zero] at hx
    exact hx

/-- **Maximal colourable prefix.**  The colourable segments among
`0,…,k` are nonempty (the empty segment is colourable) and bounded by `k`,
so they have a maximal length `m*`: `m* ≤ k`, `SegmentColourable m*`, and
any colourable `m ≤ k` satisfies `m ≤ m*`. -/
theorem exists_maxSegmentColourable {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (α₂ : ℝ) (C : 𝓗 → Finset (Fin n)) :
    ∃ mstar : ℕ, mstar ≤ k ∧ SegmentColourable ord α₂ C mstar ∧
      ∀ m : ℕ, m ≤ k → SegmentColourable ord α₂ C m → m ≤ mstar := by
  classical
  let A : Finset ℕ := (Finset.range (k + 1)).filter (SegmentColourable ord α₂ C)
  have h0 : 0 ∈ A := by
    simp [A, segmentColourable_zero ord α₂ C]
  have hne : A.Nonempty := ⟨0, h0⟩
  let mstar : ℕ := A.max' hne
  refine ⟨mstar, ?_, ?_, ?_⟩
  · -- mstar ≤ k: mstar ∈ A ⊆ range (k+1)
    have hm : mstar ∈ A := Finset.max'_mem A hne
    have hlt : mstar < k + 1 := by
      have hrange : mstar ∈ Finset.range (k + 1) := (Finset.mem_filter.mp hm).1
      exact Finset.mem_range.mp hrange
    omega
  · -- SegmentColourable mstar
    have hm : mstar ∈ A := Finset.max'_mem A hne
    exact (Finset.mem_filter.mp hm).2
  · intro m hmk hcol
    have hmA : m ∈ A := by
      simp [A, hmk, hcol]
    have hle : m ≤ A.max' hne := by
      exact Finset.le_max' A m hmA
    simpa [mstar] using hle
/-- The *successor edge* of the segment of length `m` (for `m < k`): the
unique edge of rank `m`, i.e. the next edge after the first `m`. -/
def successorEdge {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k) (m : ℕ)
    (hm : m < k) : 𝓗 :=
  ord.symm ⟨m, hm⟩

/-- The successor edge of the segment of length `m` has rank `m`. -/
lemma rank_successorEdge {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    {m : ℕ} (hm : m < k) : (ord (successorEdge ord m hm) : ℕ) = m := by
  simp [successorEdge]

/-- The successor edge is not yet in the segment. -/
lemma successorEdge_not_in_segment {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    {m : ℕ} (hm : m < k) : successorEdge ord m hm ∉ EdgeOrderSegment ord m := by
  rw [mem_EdgeOrderSegment]
  intro h
  have hrank := rank_successorEdge ord hm
  omega

/-- α-boundedness is preserved when colourings are transported along an
equality of hypergraphs (the label functions agree up to the type
identification). -/
lemma AlphaBounded_cast {𝓖₁ 𝓖₂ : Hypergraph (Fin n)} {β : ℝ} (h : 𝓖₁ = 𝓖₂)
    (φ : 𝓖₁.Coloring (Fin n)) :
    (Coloring.cast h φ).AlphaBounded β ↔ φ.AlphaBounded β := by
  subst h
  rfl

/-- `edgeSubgraph` is congruent in the edge subset. -/
lemma edgeSubgraph_congr {𝓗 : Hypergraph (Fin n)} {M₁ M₂ : Set 𝓗} (h : M₁ = M₂) :
    edgeSubgraph 𝓗 M₁ = edgeSubgraph 𝓗 M₂ := by
  rw [h]
/-- label comparison under `Coloring.cast`: the transported colouring gives
`u` the label that `φ` gives to the same vertex set (with a given
membership proof in the source hypergraph) -/
lemma cast_labels {𝓖₁ 𝓖₂ : Hypergraph (Fin n)} {α : Type*} (h : 𝓖₁ = 𝓖₂)
    (φ : 𝓖₁.Coloring α) (u : 𝓖₂) (hu : u.1 ∈ 𝓖₁) :
    (Coloring.cast h φ).labels u = φ.labels ⟨u.1, hu⟩ := by
  subst h
  exact congrArg φ.labels (Subtype.ext (rfl : (u : Set (Fin n)) = (u : Set (Fin n))))

/-- gluing: from a colouring of segment m and a suitable colour c for the
successor f, a colouring of segment (m+1) -/
theorem segmentColourable_succ {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (α₂ : ℝ) (C : 𝓗 → Finset (Fin n)) {m : ℕ} (hmk : m < k)
    (φ : (edgeSubgraph 𝓗 (EdgeOrderSegment ord m)).Coloring (Fin n))
    (hC : ∀ x : 𝓗, ∀ hx : x ∈ EdgeOrderSegment ord m,
      φ.labels ⟨(x : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord m) hx⟩ ∈ C x)
    (c : Fin n)
    (hcC : c ∈ C (successorEdge ord m hmk))
    (hcproper : ∀ e : 𝓗, (he : e ∈ EdgeOrderSegment ord m) →
      (((e : Set (Fin n)) ∩ ((successorEdge ord m hmk : 𝓗) : Set (Fin n))).Nonempty) →
        φ.labels ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord m) he⟩ ≠ c)
    (hbddψ : (extendColouring (successorEdge ord m hmk)
        (successorEdge_not_in_segment ord hmk) φ c hcproper).AlphaBounded α₂) :
    SegmentColourable ord α₂ C (m + 1) := by
  classical
  let f : 𝓗 := successorEdge ord m hmk
  have hfM : f ∉ EdgeOrderSegment ord m := successorEdge_not_in_segment ord hmk
  have hseg : insert f (EdgeOrderSegment ord m) = EdgeOrderSegment ord (m + 1) := by
    have h1 := insert_succ ord f
    simpa [f, rank_successorEdge ord hmk] using h1
  let ψ := extendColouring f hfM φ c hcproper
  have hEq : edgeSubgraph 𝓗 (insert f (EdgeOrderSegment ord m)) =
      edgeSubgraph 𝓗 (EdgeOrderSegment ord (m + 1)) := edgeSubgraph_congr hseg
  let χ := Coloring.cast hEq ψ
  refine ⟨χ, ?_, ?_⟩
  · -- boundedness
    exact (AlphaBounded_cast hEq ψ).mpr (by simpa [ψ] using hbddψ)
  · -- list-respect on segment (m+1)
    intro x hx
    have hxins : x ∈ insert f (EdgeOrderSegment ord m) := by
      rwa [← hseg] at hx
    rcases (Set.mem_insert_iff.mp hxins) with hxf | hxseg
    · -- x = f: colour c ∈ C(f)
      subst x
      -- label of χ at the element of segment(m+1) whose vertex set is f.val = c
      have hself : χ.labels ⟨(f : Set (Fin n)),
          edge_mem_edgeSubgraph (EdgeOrderSegment ord (m + 1)) hx⟩ = c := by
        have hcl := cast_labels (𝓖₁ := edgeSubgraph 𝓗 (insert f (EdgeOrderSegment ord m)))
          (𝓖₂ := edgeSubgraph 𝓗 (EdgeOrderSegment ord (m + 1))) hEq ψ
          ⟨(f : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord (m + 1)) hx⟩
          (edge_mem_edgeSubgraph (insert f (EdgeOrderSegment ord m)) (by exact Or.inl rfl))
        dsimp [χ]
        rw [hcl]
        -- ψ.labels at ⟨f.val, mem-insert⟩ = c via extendColouring_self
        apply extendColouring_self (f := f) hfM φ c hcproper
        rfl
      rw [hself]
      simpa [f] using hcC
    · -- x ∈ segment m: colour = φ's colour (agrees), which lies in C x
      have hcl := cast_labels (𝓖₁ := edgeSubgraph 𝓗 (insert f (EdgeOrderSegment ord m)))
        (𝓖₂ := edgeSubgraph 𝓗 (EdgeOrderSegment ord (m + 1))) hEq ψ
        ⟨(x : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord (m + 1)) hx⟩
        (edgeSubgraph_mono (Set.subset_insert f (EdgeOrderSegment ord m))
          (edge_mem_edgeSubgraph (EdgeOrderSegment ord m) hxseg))
      dsimp [χ]
      rw [hcl]
      -- ψ.labels at the embedded old edge = φ.labels at it (agrees), then hC
      have hag := extendColouring_agrees hfM φ c hcproper
        (u := ⟨(x : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord m) hxseg⟩)
      -- target: ψ.labels ⟨x.val, mono-proof⟩ = φ.labels ⟨x.val, mem⟩ ; hag gives exactly this
      rw [hag]
      exact hC x hxseg

/-! ## The colours `C₁` used by the prefix on neighbours of the successor

In the proof of Prop 6.9 (small-edge case), `C₁` is the set of colours
assigned by the prefix colouring `φ` to the coloured edges that intersect
the successor edge `f` (`C₁ := ⋃_{e ∈ fwdnbr(f)} φ(e)` in the paper's
notation).  A colour outside `C₁` is *proper* for `f`: no coloured edge
intersecting `f` has that colour, so `f` can be given it without conflict
(`segmentC1_proper`).  The size of `C₁` is bounded by the number of
coloured edges intersecting `f`, which is `d⪯(f)` — the number of
preceding neighbours of `f` (`segmentC1_card_le`); the preceding
neighbours of the successor lie in the current segment
(`preceding_mem_segment_succ`). -/

/-- predecessors of the successor edge lie in the segment -/
lemma preceding_mem_segment_succ {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    {m : ℕ} (hmk : m < k) {g : 𝓗}
    (hg : g ∈ precedingNeighbours 𝓗 ord (successorEdge ord m hmk)) :
    g ∈ EdgeOrderSegment ord m := by
  classical
  rw [mem_precedingNeighbours] at hg
  rw [mem_EdgeOrderSegment]
  have hrank : (ord (successorEdge ord m hmk) : ℕ) = m := rank_successorEdge ord hmk
  have hle : (ord g : ℕ) ≤ m := by
    have hf : ord g ≤ ord (successorEdge ord m hmk) := hg.2.1
    have hfnat : (ord g : ℕ) ≤ (ord (successorEdge ord m hmk) : ℕ) := by
      simpa using hf
    exact hfnat.trans (le_of_eq hrank)
  have hne : (ord g : ℕ) ≠ m := by
    intro heq
    apply hg.1
    apply ord.injective
    apply Fin.ext
    exact heq.trans hrank.symm
  omega

/-- the colours used by the colouring φ of segment m on its edges that
intersect the successor edge f (the paper's C₁) -/
def segmentC1 {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k) {m : ℕ}
    (hmk : m < k) (φ : (edgeSubgraph 𝓗 (EdgeOrderSegment ord m)).Coloring (Fin n)) : Finset (Fin n) := by
  classical
  let f : 𝓗 := successorEdge ord m hmk
  let S : Finset 𝓗 := (Finset.univ : Finset 𝓗).filter (fun g : 𝓗 =>
    g ∈ EdgeOrderSegment ord m ∧ (((g : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty))
  exact S.attach.image (fun g : {x : 𝓗 // x ∈ S} =>
    φ.labels ⟨(g.1 : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord m)
      ((Finset.mem_filter.mp g.2).2.1)⟩)

/-- colours on the segment-neighbours of the successor: bound by d⪯(f) -/
lemma segmentC1_card_le {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    {m : ℕ} (hmk : m < k) (φ : (edgeSubgraph 𝓗 (EdgeOrderSegment ord m)).Coloring (Fin n)) :
    (segmentC1 ord hmk φ).card ≤ precedingDegree 𝓗 ord (successorEdge ord m hmk) := by
  classical
  let f : 𝓗 := successorEdge ord m hmk
  have hfrank : (ord f : ℕ) = m := by simpa [f] using (rank_successorEdge ord hmk)
  have h1 : (segmentC1 ord hmk φ).card ≤
      ((Finset.univ : Finset 𝓗).filter (fun x : 𝓗 =>
        (ord x : ℕ) < m ∧ (((x : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty))).card := by
    unfold segmentC1
    dsimp [f]
    exact (Finset.card_image_le.trans (by simp [Finset.card_attach]))
  have hsub : ((Finset.univ : Finset 𝓗).filter (fun x : 𝓗 =>
        (ord x : ℕ) < m ∧ (((x : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty)))
      ⊆ precedingNeighbours 𝓗 ord f := by
    intro x hx
    have hseg : (ord x : ℕ) < m := (Finset.mem_filter.mp hx).2.1
    have hint : ((x : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty := (Finset.mem_filter.mp hx).2.2
    rw [mem_precedingNeighbours]
    have hne : x ≠ f := by
      intro hxf
      subst x
      omega
    have hlt : (ord x : ℕ) < (ord f : ℕ) := by omega
    exact ⟨hne, (by simpa using (le_of_lt hlt) : ord x ≤ ord f), hint⟩
  have h2 : ((Finset.univ : Finset 𝓗).filter (fun x : 𝓗 =>
      (ord x : ℕ) < m ∧ (((x : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty))).card ≤
      (precedingNeighbours 𝓗 ord f).card := Finset.card_le_card hsub
  exact h1.trans (by simpa [precedingDegree] using h2)

/-- a colour outside C₁ is proper for the new edge: no segment edge
intersecting the successor has that colour -/
lemma segmentC1_proper {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    {m : ℕ} (hmk : m < k) (φ : (edgeSubgraph 𝓗 (EdgeOrderSegment ord m)).Coloring (Fin n))
    (c : Fin n) (hc1 : c ∉ segmentC1 ord hmk φ) :
    ∀ e : 𝓗, (he : e ∈ EdgeOrderSegment ord m) →
      (((e : Set (Fin n)) ∩ ((successorEdge ord m hmk : 𝓗) : Set (Fin n))).Nonempty) →
        φ.labels ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord m) he⟩ ≠ c := by
  classical
  intro e he hint hlab
  apply hc1
  unfold segmentC1
  dsimp
  rw [Finset.mem_image]
  refine ⟨⟨e, ?_⟩, ?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ e, ⟨he, by simpa using hint⟩⟩
  · simp
  · simpa using hlab

/-! ## The greedy steps of Prop 6.9 (complete)

The following complete the greedy engine of Prop 6.9.  For a colouring
`φ` of the segment of length `m` and the successor edge
`f := successorEdge ord m hmk` of rank `m`, a colour `c` extends the
colouring to the segment of length `m+1` (and keeps `α₂`-boundedness and
list-respect) in three situations:

* **small `f` + light `c`** (`segmentColourable_succ_small`): `|f| < α₂n/2`
  and `c ∉ C₂` (its old class covers `< α₂n/2` vertices) — boundedness via
  `extendColouring_bounded`; `c ∉ C₁` (`segmentC1`) gives properness.
* **fresh `c`** (`extendColouring_fresh_bounded`,
  `segmentColourable_succ_huge`): `c` is unused anywhere on the segment,
  so its class in the extension is the singleton `{f}` — bounded regardless
  of `|f|`.  `segmentColourable_succ_huge_exists` supplies the colour from
  `C(f)` by pigeonhole when `C(f)` has more colours than the segment uses.
* **small `f` + colour outside `C₁ ∪ C₂`** (`segmentColourable_succ_small_exists`):
  pigeonhole version of the small case.

The counting lemmas then bound the number of colours the segment uses
(`segmentUsedColours`, `segmentFinset`) and the sizes of `C₁`
(`segmentC1_card_le`) and `C₂` (`heavyColours_card_le`); the huge-first
assumption (`bigFinset`, an ordering putting all big edges first) bounds
the size of a segment ending before a big successor by the total number of
big edges minus one (`segmentFinset_subset_bigFinset_erase`).  These are
assembled in **`greedy_colouring_hugeFirst`**: under the huge-first
ordering and the two margins `2n/(α₂(r−1)) < α₁n/2` and `#big < α₁n`,
Prop 6.9 holds.  (Removing the huge-first assumption by reordering the
given ordering, at the cost of halving `α₁`, is the remaining reordering
step; see `Prop69Instance`.) -/

/-- small-f extension: colour c ∈ C(f) proper (∉ C₁) and light (∉ C₂),
with |f| < α₂n/2 ⇒ segment (m+1) colourable -/
theorem segmentColourable_succ_small {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (α₂ : ℝ) (C : 𝓗 → Finset (Fin n)) {m : ℕ} (hmk : m < k)
    (φ : (edgeSubgraph 𝓗 (EdgeOrderSegment ord m)).Coloring (Fin n))
    (hbdd : φ.AlphaBounded α₂)
    (hC : ∀ x : 𝓗, ∀ hx : x ∈ EdgeOrderSegment ord m,
      φ.labels ⟨(x : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord m) hx⟩ ∈ C x)
    (c : Fin n)
    (hcC : c ∈ C (successorEdge ord m hmk))
    (hc1 : c ∉ segmentC1 ord hmk φ)
    (hc2 : c ∉ HeavyColours α₂ φ)
    (hsmall : (edgeSize ((successorEdge ord m hmk : 𝓗) : Set (Fin n)) : ℝ) < (α₂ / 2 : ℝ) * (n : ℝ)) :
    SegmentColourable ord α₂ C (m + 1) := by
  classical
  have hcproper : ∀ e : 𝓗, (he : e ∈ EdgeOrderSegment ord m) →
      (((e : Set (Fin n)) ∩ ((successorEdge ord m hmk : 𝓗) : Set (Fin n))).Nonempty) →
        φ.labels ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord m) he⟩ ≠ c :=
    segmentC1_proper ord hmk φ c hc1
  have hlight : (FamilyVertexCount (EdgeSetFamily (φ.colorClass c)) : ℝ) < (α₂ / 2 : ℝ) * (n : ℝ) := by
    have hnot : ¬ (α₂ / 2 : ℝ) * (n : ℝ) ≤ (φ.classVertexCount c : ℝ) := by
      simpa [mem_HeavyColours] using hc2
    have hlt : (φ.classVertexCount c : ℝ) < (α₂ / 2 : ℝ) * (n : ℝ) := lt_of_not_ge hnot
    have hEq : FamilyVertexCount (EdgeSetFamily (φ.colorClass c)) = φ.classVertexCount c :=
      (classVertexCount_eq_FamilyVertexCount φ c).symm
    rwa [hEq]
  refine segmentColourable_succ ord α₂ C hmk φ hC c hcC hcproper ?hbddψ
  exact extendColouring_bounded (successorEdge_not_in_segment ord hmk) φ c α₂ hcproper hbdd hlight hsmall

/-- fresh colour c: colour class of c in the extension is contained in {f} -/
lemma colorClass_extend_fresh {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {f : 𝓗}
    (hfM : f ∉ M) (φM : (edgeSubgraph 𝓗 M).Coloring (Fin n)) (c : Fin n)
    (hfresh : ∀ u : edgeSubgraph 𝓗 M, φM.labels u ≠ c) :
    (extendColouring f hfM φM c (fun e _heM _hint =>
        hfresh ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph M _heM⟩)).colorClass c ⊆
      {⟨(f : Set (Fin n)), edge_mem_edgeSubgraph (insert f M) (by exact Or.inl rfl)⟩} := by
  classical
  intro u hu
  rw [mem_colorClass] at hu
  have huEq : u.1 = (f : Set (Fin n)) := by
    by_contra hne
    have hM : u.1 ∈ edgeSubgraph 𝓗 M := mem_edgeSubgraph_insert_left u.2 hne
    have hlab : (extendColouring f hfM φM c (fun e _heM _hint =>
        hfresh ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph M _heM⟩)).labels u =
        φM.labels ⟨u.1, hM⟩ := by
      unfold extendColouring
      simp only [dif_pos hne]
    have hfr := hfresh ⟨u.1, hM⟩
    apply hfr
    rw [← hu, hlab]
  rw [Set.mem_singleton_iff]
  apply Subtype.ext
  exact huEq

/-- fresh colour c: the class of c in the extension is exactly {f} -/
lemma colorClass_extend_fresh_eq {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {f : 𝓗}
    (hfM : f ∉ M) (φM : (edgeSubgraph 𝓗 M).Coloring (Fin n)) (c : Fin n)
    (hfresh : ∀ u : edgeSubgraph 𝓗 M, φM.labels u ≠ c) :
    (extendColouring f hfM φM c (fun e _heM _hint =>
        hfresh ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph M _heM⟩)).colorClass c =
      {⟨(f : Set (Fin n)), edge_mem_edgeSubgraph (insert f M) (by exact Or.inl rfl)⟩} := by
  classical
  ext u
  constructor
  · intro hu
    exact colorClass_extend_fresh (f := f) hfM φM c hfresh hu
  · intro hu
    rw [mem_colorClass]
    have huEq : u = ⟨(f : Set (Fin n)), edge_mem_edgeSubgraph (insert f M) (by exact Or.inl rfl)⟩ :=
      (Set.mem_singleton_iff.mp hu)
    subst u
    apply extendColouring_self (f := f) hfM φM c (fun e _heM _hint =>
        hfresh ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph M _heM⟩) (u := ⟨(f : Set (Fin n)),
          edge_mem_edgeSubgraph (insert f M) (by exact Or.inl rfl)⟩)
    rfl

/-- fresh colour case: giving f a colour unused in the prefix keeps
α₂-boundedness (the class of c is the singleton {f}) -/
theorem extendColouring_fresh_bounded {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {f : 𝓗}
    (hfM : f ∉ M) (φM : (edgeSubgraph 𝓗 M).Coloring (Fin n)) (c : Fin n) (α₂ : ℝ)
    (hfresh : ∀ u : edgeSubgraph 𝓗 M, φM.labels u ≠ c)
    (hbdd : φM.AlphaBounded α₂) :
    (extendColouring f hfM φM c (fun e _heM _hint =>
        hfresh ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph M _heM⟩)).AlphaBounded α₂ := by
  classical
  intro d
  by_cases hdc : d = c
  · subst d
    left
    have hEq := colorClass_extend_fresh_eq (f := f) hfM φM c hfresh
    rw [hEq]
    simp
  · rcases hbdd d with hOne | hBdd
    · left
      have hcl := colorClass_extend_ne (f := f) hfM φM c d hdc
        (fun e _heM _hint => hfresh ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph M _heM⟩)
      rw [hcl]
      have hcard : ((segmentEmbed (𝓗 := 𝓗) (M := M) (f := f)) '' (φM.colorClass d)).ncard =
          (φM.colorClass d).ncard := by
        exact Set.ncard_image_of_injective (φM.colorClass d) (segmentEmbed_injective (𝓗 := 𝓗) (M := M) (f := f))
      rwa [hcard]
    · right
      have hfam := edgeSetFamily_extend_ne (f := f) hfM φM c d hdc
        (fun e _heM _hint => hfresh ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph M _heM⟩)
      rwa [hfam]

/-- huge-f step: if f is given a fresh colour (not used anywhere in the
segment), the segment (m+1) is colourable (no size condition on f needed) -/
theorem segmentColourable_succ_huge {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (α₂ : ℝ) (C : 𝓗 → Finset (Fin n)) {m : ℕ} (hmk : m < k)
    (φ : (edgeSubgraph 𝓗 (EdgeOrderSegment ord m)).Coloring (Fin n))
    (hbdd : φ.AlphaBounded α₂)
    (hC : ∀ x : 𝓗, ∀ hx : x ∈ EdgeOrderSegment ord m,
      φ.labels ⟨(x : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord m) hx⟩ ∈ C x)
    (c : Fin n)
    (hcC : c ∈ C (successorEdge ord m hmk))
    (hfresh : ∀ u : edgeSubgraph 𝓗 (EdgeOrderSegment ord m), φ.labels u ≠ c) :
    SegmentColourable ord α₂ C (m + 1) := by
  classical
  refine segmentColourable_succ ord α₂ C hmk φ hC c hcC ?hcproper ?hbddψ
  · intro e he _hint
    exact hfresh ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord m) he⟩
  · exact extendColouring_fresh_bounded (successorEdge_not_in_segment ord hmk) φ c α₂ hfresh hbdd


/-- linearity is inherited by subhypergraphs -/
lemma isLinear_of_subset {𝓖 𝓗 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗)
    (hlin : 𝓗.IsLinear) : 𝓖.IsLinear := by
  intro e₁ he₁ e₂ he₂ hne
  exact hlin (hsub he₁) (hsub he₂) hne

/-- the edge-subgraph of an edge subset of a linear hypergraph is linear -/
lemma edgeSubgraph_isLinear {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) (M : Set 𝓗) :
    (edgeSubgraph 𝓗 M).IsLinear :=
  isLinear_of_subset (edgeSubgraph_subset 𝓗 M) hlin

/-- edge-size lower bounds pass to edge subgraphs -/
lemma edgeSubgraph_size_ge {𝓗 : Hypergraph (Fin n)} (M : Set 𝓗) (r : ℕ)
    (hsize : ∀ e : 𝓗, r ≤ edgeSize (e : Set (Fin n))) :
    ∀ u : edgeSubgraph 𝓗 M, r ≤ edgeSize (u : Set (Fin n)) := by
  intro u
  have hu𝓗 : u.1 ∈ 𝓗 := edgeSubgraph_subset 𝓗 M u.2
  have h := hsize ⟨u.1, hu𝓗⟩
  simpa using h

/-- the initial segment as a finset -/
def segmentFinset {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k) (m : ℕ) : Finset 𝓗 := by
  classical
  exact (Finset.univ : Finset 𝓗).filter (fun f : 𝓗 => (ord f : ℕ) < m)

/-- membership in the segment finset -/
lemma mem_segmentFinset {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k) {m : ℕ} {f : 𝓗} :
    f ∈ segmentFinset ord m ↔ (ord f : ℕ) < m := by
  classical
  simp [segmentFinset]

/-- the successor is not in the segment finset -/
lemma successorEdge_not_in_segmentFinset {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    {m : ℕ} (hmk : m < k) : successorEdge ord m hmk ∉ segmentFinset ord m := by
  rw [mem_segmentFinset]
  have hrank := rank_successorEdge ord hmk
  omega

/-- the colours used by a colouring φ of the segment -/
def segmentUsedColours {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k) {m : ℕ}
    (φ : (edgeSubgraph 𝓗 (EdgeOrderSegment ord m)).Coloring (Fin n)) : Finset (Fin n) := by
  classical
  exact (segmentFinset ord m).attach.image (fun e : {x : 𝓗 // x ∈ segmentFinset ord m} =>
    φ.labels ⟨(e.1 : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord m)
      ((mem_segmentFinset ord).mp e.2)⟩)

/-- size of the used-colour set is at most the size of the segment -/
lemma segmentUsedColours_card_le {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k) {m : ℕ}
    (φ : (edgeSubgraph 𝓗 (EdgeOrderSegment ord m)).Coloring (Fin n)) :
    (segmentUsedColours ord φ).card ≤ (segmentFinset ord m).card := by
  classical
  unfold segmentUsedColours
  exact (Finset.card_image_le.trans (by simp [Finset.card_attach]))

/-- membership in the used-colour set -/
lemma mem_segmentUsedColours {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k) {m : ℕ}
    (φ : (edgeSubgraph 𝓗 (EdgeOrderSegment ord m)).Coloring (Fin n)) (c : Fin n) :
    c ∈ segmentUsedColours ord φ ↔
      ∃ e : 𝓗, ∃ he : e ∈ segmentFinset ord m,
        φ.labels ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord m)
          ((mem_segmentFinset ord).mp he)⟩ = c := by
  classical
  unfold segmentUsedColours
  rw [Finset.mem_image]
  constructor
  · intro h
    rcases h with ⟨x, hx, hEq⟩
    refine ⟨x.1, x.2, ?_⟩
    simpa using hEq
  · intro h
    rcases h with ⟨e, he, hEq⟩
    refine ⟨⟨e, he⟩, ?_, ?_⟩
    · exact Finset.mem_attach _ ⟨e, he⟩
    · simpa using hEq

/-- a colour absent from the used set is fresh on every segment edge -/
lemma usedColours_fresh {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k) {m : ℕ}
    (φ : (edgeSubgraph 𝓗 (EdgeOrderSegment ord m)).Coloring (Fin n)) (c : Fin n)
    (hc : c ∉ segmentUsedColours ord φ) :
    ∀ u : edgeSubgraph 𝓗 (EdgeOrderSegment ord m), φ.labels u ≠ c := by
  classical
  intro u hlab
  apply hc
  rw [mem_segmentUsedColours]
  rcases (mem_edgeSubgraph 𝓗 (EdgeOrderSegment ord m) u.1).1 u.2 with ⟨e, heM, hEq⟩
  let heF : e ∈ segmentFinset ord m := (mem_segmentFinset ord).mpr ((mem_EdgeOrderSegment ord).mp heM)
  refine ⟨e, heF, ?_⟩
  have hsubeq : (⟨(e : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord m)
        ((mem_segmentFinset ord).mp heF)⟩ : edgeSubgraph 𝓗 (EdgeOrderSegment ord m)) = u := by
    apply Subtype.ext
    exact hEq
  rw [hsubeq]
  exact hlab

/-- the big edges (|e| ≥ α₂n/2), as a finset -/
def bigFinset (α₂ : ℝ) (𝓗 : Hypergraph (Fin n)) : Finset 𝓗 := by
  classical
  exact (Finset.univ : Finset 𝓗).filter (fun e : 𝓗 =>
    (α₂ / 2 : ℝ) * (n : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ))

/-- membership in bigFinset -/
lemma mem_bigFinset (α₂ : ℝ) (𝓗 : Hypergraph (Fin n)) (e : 𝓗) :
    e ∈ bigFinset α₂ 𝓗 ↔ (α₂ / 2 : ℝ) * (n : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) := by
  classical
  simp [bigFinset]

/-- huge-f extension step: some colour of C(f) is unused on the prefix -/
theorem segmentColourable_succ_huge_exists {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (α₂ : ℝ) (C : 𝓗 → Finset (Fin n)) {m : ℕ} (hmk : m < k)
    (φ : (edgeSubgraph 𝓗 (EdgeOrderSegment ord m)).Coloring (Fin n))
    (hbdd : φ.AlphaBounded α₂)
    (hC : ∀ x : 𝓗, ∀ hx : x ∈ EdgeOrderSegment ord m,
      φ.labels ⟨(x : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord m) hx⟩ ∈ C x)
    (hsmallC : (segmentUsedColours ord φ).card < (C (successorEdge ord m hmk)).card) :
    SegmentColourable ord α₂ C (m + 1) := by
  classical
  rcases exists_color_unused (C := C (successorEdge ord m hmk)) (S := segmentUsedColours ord φ) hsmallC
    with ⟨c, hcC, hcused⟩
  refine segmentColourable_succ_huge ord α₂ C hmk φ hbdd hC c hcC ?_
  exact usedColours_fresh ord φ c hcused

/-- small-f extension step: some colour of C(f) is outside C₁ ∪ C₂ -/
theorem segmentColourable_succ_small_exists {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (α₂ : ℝ) (C : 𝓗 → Finset (Fin n)) {m : ℕ} (hmk : m < k)
    (φ : (edgeSubgraph 𝓗 (EdgeOrderSegment ord m)).Coloring (Fin n))
    (hbdd : φ.AlphaBounded α₂)
    (hC : ∀ x : 𝓗, ∀ hx : x ∈ EdgeOrderSegment ord m,
      φ.labels ⟨(x : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord m) hx⟩ ∈ C x)
    (hsmallC : (segmentC1 ord hmk φ ∪ HeavyColours α₂ φ).card < (C (successorEdge ord m hmk)).card)
    (hsmall : (edgeSize ((successorEdge ord m hmk : 𝓗) : Set (Fin n)) : ℝ) < (α₂ / 2 : ℝ) * (n : ℝ)) :
    SegmentColourable ord α₂ C (m + 1) := by
  classical
  rcases exists_color_unused (C := C (successorEdge ord m hmk))
    (S := segmentC1 ord hmk φ ∪ HeavyColours α₂ φ) hsmallC with ⟨c, hcC, hc12⟩
  have hc1 : c ∉ segmentC1 ord hmk φ := by
    intro h
    exact hc12 (Finset.mem_union.mpr (Or.inl h))
  have hc2 : c ∉ HeavyColours α₂ φ := by
    intro h
    exact hc12 (Finset.mem_union.mpr (Or.inr h))
  exact segmentColourable_succ_small ord α₂ C hmk φ hbdd hC c hcC hc1 hc2 hsmall

/-- the edge-subgraph on all of 𝓗 is 𝓗 itself -/
lemma edgeSubgraph_univ (𝓗 : Hypergraph (Fin n)) : edgeSubgraph 𝓗 Set.univ = 𝓗 := by
  ext s
  constructor
  · intro hs
    rcases (mem_edgeSubgraph 𝓗 Set.univ s).1 hs with ⟨x, _hx, hEq⟩
    rw [← hEq]
    exact x.2
  · intro hs
    exact (mem_edgeSubgraph 𝓗 Set.univ s).2 ⟨⟨s, hs⟩, by simp, rfl⟩

/-- segment is contained in the erased big finset when the successor is big
(huge-first ordering) -/
lemma segmentFinset_subset_bigFinset_erase {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (α₂ : ℝ) {m : ℕ} {f : 𝓗}
    (hbigfirst : ∀ e : 𝓗, e ∈ bigFinset α₂ 𝓗 →
      ∀ g : 𝓗, (ord g : ℕ) < (ord e : ℕ) → g ∈ bigFinset α₂ 𝓗)
    (hfrank : (ord f : ℕ) = m) (hfbig : f ∈ bigFinset α₂ 𝓗) (hfnseg : f ∉ segmentFinset ord m) :
    segmentFinset ord m ⊆ (bigFinset α₂ 𝓗).erase f := by
  classical
  intro e he
  rw [Finset.mem_erase]
  constructor
  · intro hEqf
    subst e
    exact hfnseg he
  · have hlt : (ord e : ℕ) < (ord f : ℕ) := by
      rw [mem_segmentFinset] at he
      omega
    exact hbigfirst f hfbig e hlt

/-! ## Prop 6.9 engine: greedy colouring under a huge-first ordering -/

/-- **Prop 6.9 (huge-first engine).**  Let `𝓗` be a linear hypergraph on `n`
vertices whose edges all have size at least `r`, with a linear ordering
`ord` in which every *big* edge (`|e| ≥ α₂n/2`) precedes every edge that is
not big.  If `C` is a list assignment with `|C(e)| ≥ d⪯(e) + α₁n` for every
edge `e`, then there is an `α₂`-bounded proper edge-colouring `φ` of `𝓗`
with `φ(e) ∈ C(e)` for every `e`, provided the two margins
`2n/(α₂(r−1)) < α₁n/2` (bounding the heavy colours by Prop 6.8(i)) and
`#big < α₁n` (bounding the number of big edges, so a fresh colour exists
when the successor is big) hold.  (The `#big` bound is derived from the
pair count `card_edges_size_ge_le` at the level of the `≪`-hierarchy.) -/
theorem greedy_colouring_hugeFirst {n r k : ℕ} {α₁ α₂ : ℝ} {𝓗 : Hypergraph (Fin n)}
    (h2n : 2 ≤ n) (h2r : 2 ≤ r) (hα₂ : 0 < α₂)
    (hmargin : (2 : ℝ) * (n : ℝ) / (α₂ * ((r : ℝ) - 1)) < (α₁ * (n : ℝ)) / 2)
    (hbigmargin : ((bigFinset α₂ 𝓗).card : ℝ) < α₁ * (n : ℝ))
    (hlin : 𝓗.IsLinear) (hsize : ∀ e : 𝓗, (r : ℕ) ≤ edgeSize (e : Set (Fin n)))
    (ord : 𝓗 ≃ Fin k)
    (hbigfirst : ∀ e : 𝓗, e ∈ bigFinset α₂ 𝓗 →
      ∀ g : 𝓗, (ord g : ℕ) < (ord e : ℕ) → g ∈ bigFinset α₂ 𝓗)
    (C : 𝓗 → Finset (Fin n))
    (hC : ∀ e : 𝓗, ((precedingDegree 𝓗 ord e : ℝ) + α₁ * (n : ℝ)) ≤ ((C e).card : ℝ)) :
    ∃ φ : 𝓗.Coloring (Fin n), φ.AlphaBounded α₂ ∧ ∀ e : 𝓗, φ.labels e ∈ C e := by
  classical
  rcases exists_maxSegmentColourable ord α₂ C with ⟨mstar, hmstarK, hcol, hmax⟩
  have hmstarEq : mstar = k := by
    by_contra hne
    have hmk : mstar < k := by
      omega
    exfalso
    -- show SegmentColourable (mstar + 1), contradicting maximality
    rcases hcol with ⟨φ, hbdd, hCseg⟩
    let f : 𝓗 := successorEdge ord mstar hmk
    have hC1 : SegmentColourable ord α₂ C (mstar + 1) := by
      by_cases hfbig : f ∈ bigFinset α₂ 𝓗
      · -- f is big: a fresh colour works
        have hcard₂ : (segmentFinset ord mstar).card ≤ (bigFinset α₂ 𝓗).card - 1 := by
          have hsub : segmentFinset ord mstar ⊆ (bigFinset α₂ 𝓗).erase f := by
            exact segmentFinset_subset_bigFinset_erase ord α₂ hbigfirst (rank_successorEdge ord hmk)
              hfbig (successorEdge_not_in_segmentFinset ord hmk)
          have hle : (segmentFinset ord mstar).card ≤ ((bigFinset α₂ 𝓗).erase f).card :=
            Finset.card_le_card hsub
          have herase : ((bigFinset α₂ 𝓗).erase f).card = (bigFinset α₂ 𝓗).card - 1 :=
            Finset.card_erase_of_mem hfbig
          rwa [herase] at hle
        have husedle : (segmentUsedColours ord φ).card ≤ (bigFinset α₂ 𝓗).card - 1 :=
          (segmentUsedColours_card_le ord φ).trans hcard₂
        have hCf : (α₁ * (n : ℝ)) ≤ ((C f).card : ℝ) := by
          have h := hC f
          have hd : (0 : ℝ) ≤ (precedingDegree 𝓗 ord f : ℝ) := by positivity
          nlinarith
        have hreal : ((segmentUsedColours ord φ).card : ℝ) < ((C f).card : ℝ) := by
          have h₁ : ((segmentUsedColours ord φ).card : ℝ) ≤ (((bigFinset α₂ 𝓗).card - 1 : ℕ) : ℝ) := by
            exact_mod_cast husedle
          have h₂ : (((bigFinset α₂ 𝓗).card - 1 : ℕ) : ℝ) < ((bigFinset α₂ 𝓗).card : ℝ) := by
            have hpos : 0 < (bigFinset α₂ 𝓗).card := Finset.card_pos.mpr ⟨f, hfbig⟩
            have hsub : (bigFinset α₂ 𝓗).card - 1 < (bigFinset α₂ 𝓗).card :=
              Nat.sub_lt hpos (by norm_num)
            exact_mod_cast hsub
          nlinarith
        have husedlt : (segmentUsedColours ord φ).card < (C f).card := by
          exact_mod_cast hreal
        exact segmentColourable_succ_huge_exists ord α₂ C hmk φ hbdd hCseg husedlt
      · -- f is small: a colour outside C₁ ∪ C₂ works
        have hlinSeg : (edgeSubgraph 𝓗 (EdgeOrderSegment ord mstar)).IsLinear :=
          edgeSubgraph_isLinear hlin (EdgeOrderSegment ord mstar)
        have hsizeSeg : ∀ u : edgeSubgraph 𝓗 (EdgeOrderSegment ord mstar),
            (r : ℕ) ≤ edgeSize (u : Set (Fin n)) :=
          edgeSubgraph_size_ge (EdgeOrderSegment ord mstar) r hsize
        have hC₂le : (((HeavyColours α₂ φ).card : ℝ) ≤
            (2 : ℝ) * (n : ℝ) / (α₂ * ((r : ℝ) - 1))) := by
          exact heavyColours_card_le (h2n := h2n) (h2r := h2r) (hα₂ := hα₂)
            (𝓗 := edgeSubgraph 𝓗 (EdgeOrderSegment ord mstar)) (hlin := hlinSeg)
            (hsize := hsizeSeg) (φ := φ)
        have hC₁₂le : (((segmentC1 ord hmk φ ∪ HeavyColours α₂ φ).card : ℝ) ≤
            (precedingDegree 𝓗 ord f : ℝ) + ((HeavyColours α₂ φ).card : ℝ)) := by
          have hu := card_union_le_add (A := segmentC1 ord hmk φ) (B := HeavyColours α₂ φ)
          have hc1r : ((segmentC1 ord hmk φ).card : ℝ) ≤ (precedingDegree 𝓗 ord f : ℝ) := by
            exact_mod_cast (segmentC1_card_le ord hmk φ)
          nlinarith
        have hCf : ((precedingDegree 𝓗 ord f : ℝ) + α₁ * (n : ℝ)) ≤ ((C f).card : ℝ) := hC f
        have hreal : (((segmentC1 ord hmk φ ∪ HeavyColours α₂ φ).card : ℝ) < ((C f).card : ℝ)) := by
          have h₁ : ((segmentC1 ord hmk φ ∪ HeavyColours α₂ φ).card : ℝ) <
              (precedingDegree 𝓗 ord f : ℝ) + α₁ * (n : ℝ) := by
            nlinarith [hmargin, hC₂le, hC₁₂le]
          exact lt_of_lt_of_le h₁ hCf
        have hsmallC : (segmentC1 ord hmk φ ∪ HeavyColours α₂ φ).card < (C f).card := by
          exact_mod_cast hreal
        have hsmallf : (edgeSize ((f : 𝓗) : Set (Fin n)) : ℝ) < (α₂ / 2 : ℝ) * (n : ℝ) := by
          have hnot : ¬ (α₂ / 2 : ℝ) * (n : ℝ) ≤ (edgeSize ((f : 𝓗) : Set (Fin n)) : ℝ) := by
            intro hb
            exact hfbig ((mem_bigFinset α₂ 𝓗 f).mpr hb)
          exact lt_of_not_ge hnot
        exact segmentColourable_succ_small_exists ord α₂ C hmk φ hbdd hCseg hsmallC hsmallf
    have hle1 : mstar + 1 ≤ k := by omega
    have hmle : mstar + 1 ≤ mstar := hmax (mstar + 1) hle1 hC1
    omega
  -- mstar = k: transport the colouring of the whole segment to 𝓗
  rcases hcol with ⟨φ, hbdd, hCseg⟩
  have hsegk : EdgeOrderSegment ord k = Set.univ :=
    EdgeOrderSegment_univ_of_all ord (by intro f; exact (ord f).isLt)
  have hEq : edgeSubgraph 𝓗 (EdgeOrderSegment ord mstar) = 𝓗 := by
    rw [hmstarEq, hsegk]
    exact edgeSubgraph_univ 𝓗
  let χ : 𝓗.Coloring (Fin n) := Coloring.cast hEq φ
  refine ⟨χ, ?_, ?_⟩
  · have hb := (AlphaBounded_cast hEq φ).mpr hbdd
    simpa [χ] using hb
  · intro e
    have hx : e ∈ EdgeOrderSegment ord mstar := by
      rw [mem_EdgeOrderSegment]
      have hlt : (ord e : ℕ) < k := (ord e).isLt
      omega
    have hu : (e : Set (Fin n)) ∈ edgeSubgraph 𝓗 (EdgeOrderSegment ord mstar) :=
      edge_mem_edgeSubgraph (EdgeOrderSegment ord mstar) hx
    have hcl := cast_labels (𝓖₁ := edgeSubgraph 𝓗 (EdgeOrderSegment ord mstar))
      (𝓖₂ := 𝓗) hEq φ (u := e) hu
    dsimp [χ]
    rw [hcl]
    have hsame : (⟨(e : Set (Fin n)), hu⟩ : edgeSubgraph 𝓗 (EdgeOrderSegment ord mstar)) =
        ⟨(e : Set (Fin n)), edge_mem_edgeSubgraph (EdgeOrderSegment ord mstar) hx⟩ := by
      apply Subtype.ext
      rfl
    rw [← hsame]
    exact hCseg e hx
/-! ## Lifting Prop 6.9 to arbitrary orderings: the huge-first reordering

The engine `greedy_colouring_hugeFirst` proves Prop 6.9 for orderings in
which every big edge precedes every edge that is not big.  Any ordering can
be *reordered* to such an ordering while barely changing the forward
degrees: the new order puts all big edges first (in the original relative
order) followed by all other edges (again in the original relative order).
This is built on `Fin k` by the rank map `newRank` (big indices get ranks
`0..cardBig−1`, small ones `cardBig..k−1`); `exists_hugeFirst_reorder`
gives the reordered ordering together with (a) the huge-first property and
(b) the inclusion `fwdnbr'(e) ⊆ fwdnbr(e) ∪ big`, so the forward degree
increases by at most `#big` (`fwddeg_le_of_reorder`).  Halving `α₁` absorbs
the slack, giving **`prop69_colouring`** — Prop 6.9 for an *arbitrary*
ordering under the margins `2n/(α₂(r−1)) < α₁n/4` and `#big < α₁n/2`. -/
/-- count of big indices ≤ i -/
def bigCount {k : ℕ} (bigK : Fin k → Prop) [DecidablePred bigK] (i : Fin k) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter (fun j : Fin k => bigK j ∧ j ≤ i)).card

/-- count of small indices ≤ i -/
def smallCount {k : ℕ} (bigK : Fin k → Prop) [DecidablePred bigK] (i : Fin k) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter (fun j : Fin k => ¬ bigK j ∧ j ≤ i)).card

/-- number of big indices -/
def cardBig {k : ℕ} (bigK : Fin k → Prop) [DecidablePred bigK] : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter (fun j : Fin k => bigK j)).card

/-- big indices are counted once each: i big ⇒ bigCount i ≥ 1 -/
lemma one_le_bigCount {k : ℕ} {bigK : Fin k → Prop} [DecidablePred bigK] {i : Fin k}
    (hi : bigK i) : 1 ≤ bigCount bigK i := by
  classical
  have hmem : i ∈ (Finset.univ : Finset (Fin k)).filter (fun j : Fin k => bigK j ∧ j ≤ i) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ i, ⟨hi, le_rfl⟩⟩
  exact Finset.card_pos.mpr ⟨i, hmem⟩

/-- small indices are counted once each: i small ⇒ smallCount i ≥ 1 -/
lemma one_le_smallCount {k : ℕ} {bigK : Fin k → Prop} [DecidablePred bigK] {i : Fin k}
    (hi : ¬ bigK i) : 1 ≤ smallCount bigK i := by
  classical
  have hmem : i ∈ (Finset.univ : Finset (Fin k)).filter (fun j : Fin k => ¬ bigK j ∧ j ≤ i) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ i, ⟨hi, le_rfl⟩⟩
  exact Finset.card_pos.mpr ⟨i, hmem⟩

/-- bigCount is monotone in i -/
lemma bigCount_mono {k : ℕ} {bigK : Fin k → Prop} [DecidablePred bigK] {i j : Fin k}
    (hij : i ≤ j) : bigCount bigK i ≤ bigCount bigK j := by
  classical
  have hsub : ((Finset.univ : Finset (Fin k)).filter (fun a : Fin k => bigK a ∧ a ≤ i)) ⊆
      ((Finset.univ : Finset (Fin k)).filter (fun a : Fin k => bigK a ∧ a ≤ j)) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ a, ⟨ha.2.1, le_trans ha.2.2 hij⟩⟩
  exact Finset.card_le_card hsub

/-- smallCount is monotone in i -/
lemma smallCount_mono {k : ℕ} {bigK : Fin k → Prop} [DecidablePred bigK] {i j : Fin k}
    (hij : i ≤ j) : smallCount bigK i ≤ smallCount bigK j := by
  classical
  have hsub : ((Finset.univ : Finset (Fin k)).filter (fun a : Fin k => ¬ bigK a ∧ a ≤ i)) ⊆
      ((Finset.univ : Finset (Fin k)).filter (fun a : Fin k => ¬ bigK a ∧ a ≤ j)) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ a, ⟨ha.2.1, le_trans ha.2.2 hij⟩⟩
  exact Finset.card_le_card hsub

/-- bigCount i ≤ cardBig -/
lemma bigCount_le_cardBig {k : ℕ} {bigK : Fin k → Prop} [DecidablePred bigK] (i : Fin k) :
    bigCount bigK i ≤ cardBig bigK := by
  classical
  have hsub : ((Finset.univ : Finset (Fin k)).filter (fun a : Fin k => bigK a ∧ a ≤ i)) ⊆
      ((Finset.univ : Finset (Fin k)).filter (fun a : Fin k => bigK a)) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ a, ha.2.1⟩
  exact Finset.card_le_card hsub

/-- bigCount is order-reflecting on bigs: count i ≤ count j and both big ⇒ i ≤ j -/
lemma bigCount_le_of_big {k : ℕ} {bigK : Fin k → Prop} [DecidablePred bigK]
    {i j : Fin k} (hi : bigK i)
    (h : bigCount bigK i ≤ bigCount bigK j) : i ≤ j := by
  classical
  by_contra hnot
  have hgt : j < i := lt_of_not_ge hnot
  have hstrict : bigCount bigK j < bigCount bigK i := by
    have hsub : ((Finset.univ : Finset (Fin k)).filter (fun a : Fin k => bigK a ∧ a ≤ j)) ⊆
        ((Finset.univ : Finset (Fin k)).filter (fun a : Fin k => bigK a ∧ a ≤ i)) := by
      intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_univ a, ⟨ha.2.1, le_trans ha.2.2 (le_of_lt hgt)⟩⟩
    have hmem : i ∈ (Finset.univ : Finset (Fin k)).filter (fun a : Fin k => bigK a ∧ a ≤ i) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, ⟨hi, le_rfl⟩⟩
    have hni : i ∉ (Finset.univ : Finset (Fin k)).filter (fun a : Fin k => bigK a ∧ a ≤ j) := by
      rw [Finset.mem_filter]
      exact fun h => (not_le_of_gt hgt) h.2.2
    exact Finset.card_lt_card (by
      constructor
      · exact hsub
      · intro hEq
        exact hni (hEq hmem))
  omega


/-- smallCount is order-reflecting on smalls: count i ≤ count j and both small ⇒ i ≤ j -/
lemma smallCount_le_of_small {k : ℕ} {bigK : Fin k → Prop} [DecidablePred bigK]
    {i j : Fin k} (hi : ¬ bigK i)
    (h : smallCount bigK i ≤ smallCount bigK j) : i ≤ j := by
  classical
  by_contra hnot
  have hgt : j < i := lt_of_not_ge hnot
  have hstrict : smallCount bigK j < smallCount bigK i := by
    have hsub : ((Finset.univ : Finset (Fin k)).filter (fun a : Fin k => ¬ bigK a ∧ a ≤ j)) ⊆
        ((Finset.univ : Finset (Fin k)).filter (fun a : Fin k => ¬ bigK a ∧ a ≤ i)) := by
      intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_univ a, ⟨ha.2.1, le_trans ha.2.2 (le_of_lt hgt)⟩⟩
    have hmem : i ∈ (Finset.univ : Finset (Fin k)).filter (fun a : Fin k => ¬ bigK a ∧ a ≤ i) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, ⟨hi, le_rfl⟩⟩
    have hni : i ∉ (Finset.univ : Finset (Fin k)).filter (fun a : Fin k => ¬ bigK a ∧ a ≤ j) := by
      rw [Finset.mem_filter]
      exact fun h => (not_le_of_gt hgt) h.2.2
    exact Finset.card_lt_card (by
      constructor
      · exact hsub
      · intro hEq
        exact hni (hEq hmem))
  omega

/-- total number of small indices: cardBig + cardSmall = k -/
lemma cardBig_add_cardSmall {k : ℕ} {bigK : Fin k → Prop} [DecidablePred bigK] :
    cardBig bigK + ((Finset.univ : Finset (Fin k)).filter (fun j : Fin k => ¬ bigK j)).card = k := by
  classical
  have hdisj : Disjoint ((Finset.univ : Finset (Fin k)).filter (fun j : Fin k => bigK j))
      ((Finset.univ : Finset (Fin k)).filter (fun j : Fin k => ¬ bigK j)) := by
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    exact (Finset.mem_filter.mp hj₂).2 (Finset.mem_filter.mp hj₁).2
  have hunion : ((Finset.univ : Finset (Fin k)).filter (fun j : Fin k => bigK j)) ∪
      ((Finset.univ : Finset (Fin k)).filter (fun j : Fin k => ¬ bigK j)) = Finset.univ := by
    ext j
    constructor
    · intro hj
      simp
    · intro hj
      by_cases hb : bigK j
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hj, hb⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hj, hb⟩))
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_univ] at hcard
  simpa [cardBig] using hcard.symm

/-- smallCount i ≤ number of small indices -/
lemma smallCount_le_cardSmall {k : ℕ} {bigK : Fin k → Prop} [DecidablePred bigK] (i : Fin k) :
    smallCount bigK i ≤ ((Finset.univ : Finset (Fin k)).filter (fun j : Fin k => ¬ bigK j)).card := by
  classical
  have hsub : ((Finset.univ : Finset (Fin k)).filter (fun a : Fin k => ¬ bigK a ∧ a ≤ i)) ⊆
      ((Finset.univ : Finset (Fin k)).filter (fun a : Fin k => ¬ bigK a)) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ a, ha.2.1⟩
  exact Finset.card_le_card hsub

/-- new rank: big indices first (in original order), then small ones -/
def newRank {k : ℕ} (bigK : Fin k → Prop) [DecidablePred bigK] (i : Fin k) : Fin k :=
  if h : bigK i then
    ⟨bigCount bigK i - 1, by
      have h1 : 1 ≤ bigCount bigK i := one_le_bigCount h
      have hle : bigCount bigK i ≤ cardBig bigK := bigCount_le_cardBig (bigK := bigK) i
      have hk : cardBig bigK ≤ k := by
        have hsub : ((Finset.univ : Finset (Fin k)).filter (fun j : Fin k => bigK j)) ⊆
            (Finset.univ : Finset (Fin k)) := by
          intro a _ha
          simp
        simpa [cardBig] using Finset.card_le_card hsub
      omega⟩
  else
    ⟨cardBig bigK + smallCount bigK i - 1, by
      have h1 : 1 ≤ smallCount bigK i := one_le_smallCount h
      have hs : smallCount bigK i ≤
          ((Finset.univ : Finset (Fin k)).filter (fun j : Fin k => ¬ bigK j)).card :=
        smallCount_le_cardSmall (bigK := bigK) i
      have hsum : cardBig bigK +
          ((Finset.univ : Finset (Fin k)).filter (fun j : Fin k => ¬ bigK j)).card = k :=
        cardBig_add_cardSmall (bigK := bigK)
      omega⟩

/-- value of the new rank at a big index -/
lemma newRank_val_of_big {k : ℕ} {bigK : Fin k → Prop} [DecidablePred bigK] {i : Fin k}
    (hi : bigK i) : (newRank (bigK := bigK) i : ℕ) = bigCount bigK i - 1 := by
  classical
  simp [newRank, hi]

/-- value of the new rank at a small index -/
lemma newRank_val_of_small {k : ℕ} {bigK : Fin k → Prop} [DecidablePred bigK] {i : Fin k}
    (hi : ¬ bigK i) : (newRank (bigK := bigK) i : ℕ) = cardBig bigK + smallCount bigK i - 1 := by
  classical
  simp [newRank, hi]

/-- big indices have new rank < #big -/
lemma newRank_lt_cardBig_of_big {k : ℕ} {bigK : Fin k → Prop} [DecidablePred bigK] {i : Fin k}
    (hi : bigK i) : (newRank (bigK := bigK) i : ℕ) < cardBig bigK := by
  classical
  rw [newRank_val_of_big hi]
  have h1 : 1 ≤ bigCount bigK i := one_le_bigCount hi
  have hle : bigCount bigK i ≤ cardBig bigK := bigCount_le_cardBig (bigK := bigK) i
  have hpos : 1 ≤ cardBig bigK := by
    have hmem : i ∈ (Finset.univ : Finset (Fin k)).filter (fun j : Fin k => bigK j) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, hi⟩
    exact Finset.card_pos.mpr ⟨i, hmem⟩
  omega

/-- small indices have new rank ≥ #big -/
lemma cardBig_le_newRank_of_small {k : ℕ} {bigK : Fin k → Prop} [DecidablePred bigK] {i : Fin k}
    (hi : ¬ bigK i) : cardBig bigK ≤ (newRank (bigK := bigK) i : ℕ) := by
  classical
  rw [newRank_val_of_small hi]
  have h1 : 1 ≤ smallCount bigK i := one_le_smallCount hi
  omega

/-- new rank preserves the original order on big indices -/
lemma newRank_le_of_big {k : ℕ} {bigK : Fin k → Prop} [DecidablePred bigK]
    {i j : Fin k} (hi : bigK i) (hj : bigK j)
    (h : (newRank (bigK := bigK) i : ℕ) ≤ (newRank (bigK := bigK) j : ℕ)) : i ≤ j := by
  classical
  have h₁ : bigCount bigK i ≤ bigCount bigK j := by
    rw [newRank_val_of_big hi, newRank_val_of_big hj] at h
    have h2 : 1 ≤ bigCount bigK i := one_le_bigCount hi
    have h3 : 1 ≤ bigCount bigK j := one_le_bigCount hj
    omega
  exact bigCount_le_of_big (bigK := bigK) hi h₁

/-- new rank preserves the original order on small indices -/
lemma newRank_le_of_small {k : ℕ} {bigK : Fin k → Prop} [DecidablePred bigK]
    {i j : Fin k} (hi : ¬ bigK i) (hj : ¬ bigK j)
    (h : (newRank (bigK := bigK) i : ℕ) ≤ (newRank (bigK := bigK) j : ℕ)) : i ≤ j := by
  classical
  have h₁ : smallCount bigK i ≤ smallCount bigK j := by
    rw [newRank_val_of_small hi, newRank_val_of_small hj] at h
    have h2 : 1 ≤ smallCount bigK i := one_le_smallCount hi
    have h3 : 1 ≤ smallCount bigK j := one_le_smallCount hj
    omega
  exact smallCount_le_of_small (bigK := bigK) hi h₁

/-- a small index cannot precede a big one under the new rank -/
lemma not_small_le_big {k : ℕ} {bigK : Fin k → Prop} [DecidablePred bigK]
    {i j : Fin k} (hi : ¬ bigK i) (hj : bigK j) :
    ¬ (newRank (bigK := bigK) i : ℕ) ≤ (newRank (bigK := bigK) j : ℕ) := by
  classical
  intro h
  have hlt : (newRank (bigK := bigK) j : ℕ) < (newRank (bigK := bigK) i : ℕ) :=
    lt_of_lt_of_le (newRank_lt_cardBig_of_big hj) (cardBig_le_newRank_of_small hi)
  omega

/-- the new rank map is injective -/
lemma newRank_injective {k : ℕ} {bigK : Fin k → Prop} [DecidablePred bigK] :
    Function.Injective (newRank (bigK := bigK)) := by
  classical
  intro i j h
  by_cases hbi : bigK i
  · by_cases hbj : bigK j
    · have h1 : i ≤ j := newRank_le_of_big (bigK := bigK) hbi hbj (le_of_eq (congrArg Fin.val h))
      have h2 : j ≤ i := newRank_le_of_big (bigK := bigK) hbj hbi (le_of_eq (congrArg Fin.val h).symm)
      exact le_antisymm h1 h2
    · exfalso
      have hlt : (newRank (bigK := bigK) i : ℕ) < (newRank (bigK := bigK) j : ℕ) :=
        lt_of_lt_of_le (newRank_lt_cardBig_of_big hbi) (cardBig_le_newRank_of_small hbj)
      have hEq : (newRank (bigK := bigK) i : ℕ) = (newRank (bigK := bigK) j : ℕ) := congrArg Fin.val h
      omega
  · by_cases hbj : bigK j
    · exfalso
      have hlt : (newRank (bigK := bigK) j : ℕ) < (newRank (bigK := bigK) i : ℕ) :=
        lt_of_lt_of_le (newRank_lt_cardBig_of_big hbj) (cardBig_le_newRank_of_small hbi)
      have hEq : (newRank (bigK := bigK) j : ℕ) = (newRank (bigK := bigK) i : ℕ) := congrArg Fin.val h.symm
      omega
    · have h1 : i ≤ j := newRank_le_of_small (bigK := bigK) hbi hbj (le_of_eq (congrArg Fin.val h))
      have h2 : j ≤ i := newRank_le_of_small (bigK := bigK) hbj hbi (le_of_eq (congrArg Fin.val h).symm)
      exact le_antisymm h1 h2


/-- **huge-first reordering.**  Any ordering `ord` of the edges of `𝓗` can
be reordered to an ordering `ord'` that puts every big edge
(`|e| ≥ α₂n/2`) before every edge that is not big, in such a way that (a)
big edges precede all others under `ord'`, and (b) every preceding-neighbour
of `e` under `ord'` is either a preceding-neighbour of `e` under `ord` or a
big edge — hence `fwddeg_{ord'}(e) ≤ fwddeg_ord(e) + #big`. -/
theorem exists_hugeFirst_reorder {n k : ℕ} {α₂ : ℝ} {𝓗 : Hypergraph (Fin n)}
    (ord : 𝓗 ≃ Fin k) :
    ∃ ord' : 𝓗 ≃ Fin k,
      (∀ e : 𝓗, e ∈ bigFinset α₂ 𝓗 →
        ∀ g : 𝓗, (ord' g : ℕ) < (ord' e : ℕ) → g ∈ bigFinset α₂ 𝓗) ∧
      (∀ e : 𝓗, ∀ g : 𝓗, g ∈ precedingNeighbours 𝓗 ord' e →
        g ∈ precedingNeighbours 𝓗 ord e ∨ g ∈ bigFinset α₂ 𝓗) := by
  classical
  let bigK : Fin k → Prop := fun i => ord.symm i ∈ bigFinset α₂ 𝓗
  have hinj : Function.Injective (newRank (bigK := bigK)) := newRank_injective (bigK := bigK)
  have hsurj : Function.Surjective (newRank (bigK := bigK)) :=
    (Finite.injective_iff_surjective (f := newRank (bigK := bigK))).mp hinj
  let σ : Fin k ≃ Fin k := Equiv.ofBijective (newRank (bigK := bigK)) ⟨hinj, hsurj⟩
  let ord' : 𝓗 ≃ Fin k := ord.trans σ
  have hσ_apply : ∀ x : Fin k, σ x = newRank (bigK := bigK) x := by
    intro x
    dsimp [σ]
    exact congrFun (Equiv.coe_ofBijective (newRank (bigK := bigK))
      (⟨hinj, hsurj⟩ : Function.Bijective (newRank (bigK := bigK)))) x
  have hord'_apply : ∀ x : 𝓗, ord' x = newRank (bigK := bigK) (ord x) := by
    intro x
    calc
      ord' x = (ord.trans σ) x := rfl
      _ = σ (ord x) := by simp [Equiv.trans_apply]
      _ = newRank (bigK := bigK) (ord x) := hσ_apply (ord x)
  refine ⟨ord', ?_, ?_⟩
  · -- huge-first: every edge before a big edge is big
    intro e hebig g hlt
    have h1 : (newRank (bigK := bigK) (ord g) : ℕ) <
        (newRank (bigK := bigK) (ord e) : ℕ) := by
      change newRank (bigK := bigK) (ord g) < newRank (bigK := bigK) (ord e)
      rw [← hord'_apply g, ← hord'_apply e]
      exact hlt
    have h2 : (newRank (bigK := bigK) (ord e) : ℕ) < cardBig bigK := by
      have hbe : bigK (ord e) := by
        simpa [bigK] using hebig
      exact newRank_lt_cardBig_of_big (bigK := bigK) hbe
    have h3 : (newRank (bigK := bigK) (ord g) : ℕ) < cardBig bigK := lt_trans h1 h2
    have hbg : bigK (ord g) := by
      by_contra hng
      have hle : cardBig bigK ≤ (newRank (bigK := bigK) (ord g) : ℕ) :=
        cardBig_le_newRank_of_small (bigK := bigK) hng
      omega
    simpa [bigK] using hbg
  · -- fwdnbr(ord') ⊆ fwdnbr(ord) ∪ big
    intro e g hg
    have hg' := (mem_precedingNeighbours 𝓗 ord' e g).1 hg
    rcases hg' with ⟨hne, hle, hint⟩
    by_cases hgb : g ∈ bigFinset α₂ 𝓗
    · exact Or.inr hgb
    · left
      rw [mem_precedingNeighbours]
      refine ⟨hne, ?_, hint⟩
      have hgS : ¬ bigK (ord g) := by
        intro h
        exact hgb (by simpa [bigK] using h)
      have hle' : (newRank (bigK := bigK) (ord g) : ℕ) ≤
          (newRank (bigK := bigK) (ord e) : ℕ) := by
        change newRank (bigK := bigK) (ord g) ≤ newRank (bigK := bigK) (ord e)
        rw [← hord'_apply g, ← hord'_apply e]
        exact hle
      by_cases heB : e ∈ bigFinset α₂ 𝓗
      · exfalso
        have hbe : bigK (ord e) := by simpa [bigK] using heB
        exact not_small_le_big (bigK := bigK) hgS hbe hle'
      · have heS : ¬ bigK (ord e) := by
          intro h
          exact heB (by simpa [bigK] using h)
        exact newRank_le_of_small (bigK := bigK) hgS heS hle'


/-- **fwddeg degradation under reordering**: the preceding degree in the
huge-first ordering is at most the original one plus the number of big
edges. -/
lemma fwddeg_le_of_reorder {n k : ℕ} {α₂ : ℝ} {𝓗 : Hypergraph (Fin n)}
    (ord : 𝓗 ≃ Fin k) (ord' : 𝓗 ≃ Fin k)
    (hprec : ∀ e : 𝓗, ∀ g : 𝓗, g ∈ precedingNeighbours 𝓗 ord' e →
        g ∈ precedingNeighbours 𝓗 ord e ∨ g ∈ bigFinset α₂ 𝓗) :
    ∀ e : 𝓗, precedingDegree 𝓗 ord' e ≤ precedingDegree 𝓗 ord e + (bigFinset α₂ 𝓗).card := by
  classical
  intro e
  have hsub : ((precedingNeighbours 𝓗 ord' e : Finset 𝓗) : Set 𝓗) ⊆
      (((precedingNeighbours 𝓗 ord e : Finset 𝓗) : Set 𝓗) ∪ ((bigFinset α₂ 𝓗 : Finset 𝓗) : Set 𝓗)) := by
    intro g hg
    have hg' : g ∈ precedingNeighbours 𝓗 ord' e := by simpa using hg
    rcases hprec e g hg' with hl | hr
    · exact Or.inl (by simpa using hl)
    · exact Or.inr (by simpa using hr)
  have hcard : (precedingNeighbours 𝓗 ord' e).card ≤
      (((precedingNeighbours 𝓗 ord e : Finset 𝓗) : Set 𝓗) ∪ ((bigFinset α₂ 𝓗 : Finset 𝓗) : Set 𝓗)).ncard := by
    rw [← Set.ncard_coe_finset (precedingNeighbours 𝓗 ord' e)]
    exact Set.ncard_le_ncard hsub
  have hcard' : (((precedingNeighbours 𝓗 ord e : Finset 𝓗) : Set 𝓗) ∪
      ((bigFinset α₂ 𝓗 : Finset 𝓗) : Set 𝓗)).ncard ≤
      (precedingNeighbours 𝓗 ord e).card + (bigFinset α₂ 𝓗).card := by
    calc
      (((precedingNeighbours 𝓗 ord e : Finset 𝓗) : Set 𝓗) ∪
          ((bigFinset α₂ 𝓗 : Finset 𝓗) : Set 𝓗)).ncard
          ≤ ((precedingNeighbours 𝓗 ord e : Finset 𝓗) : Set 𝓗).ncard +
            ((bigFinset α₂ 𝓗 : Finset 𝓗) : Set 𝓗).ncard := Set.ncard_union_le _ _
      _ = (precedingNeighbours 𝓗 ord e).card + (bigFinset α₂ 𝓗).card := by simp
  exact hcard.trans hcard'

/-- **Prop 6.9 (greedy-colouring), arbitrary ordering.**  For a linear
`n`-vertex hypergraph whose edges all have size at least `r`, with any
linear ordering `ord` and a list assignment `C` with
`|C(e)| ≥ d⪯(e) + α₁n` for every edge, there is an `α₂`-bounded proper
edge-colouring `φ` with `φ(e) ∈ C(e)` for every `e`, provided the margins
`2n/(α₂(r−1)) < α₁n/4` (heavy colours, via Prop 6.8(i)) and
`#big < α₁n/2` (big edges; fresh colours; ordering slack) hold.  The proof
reorders `ord` to a huge-first ordering (halving `α₁` for the slack) and
applies `greedy_colouring_hugeFirst`. -/
theorem prop69_colouring {n r k : ℕ} {α₁ α₂ : ℝ} {𝓗 : Hypergraph (Fin n)}
    (h2n : 2 ≤ n) (h2r : 2 ≤ r) (hα₂ : 0 < α₂)
    (hmargin : (2 : ℝ) * (n : ℝ) / (α₂ * ((r : ℝ) - 1)) < (α₁ * (n : ℝ)) / 4)
    (hbigmargin : ((bigFinset α₂ 𝓗).card : ℝ) < (α₁ * (n : ℝ)) / 2)
    (hlin : 𝓗.IsLinear) (hsize : ∀ e : 𝓗, (r : ℕ) ≤ edgeSize (e : Set (Fin n)))
    (ord : 𝓗 ≃ Fin k) (C : 𝓗 → Finset (Fin n))
    (hC : ∀ e : 𝓗, ((precedingDegree 𝓗 ord e : ℝ) + α₁ * (n : ℝ)) ≤ ((C e).card : ℝ)) :
    ∃ φ : 𝓗.Coloring (Fin n), φ.AlphaBounded α₂ ∧ ∀ e : 𝓗, φ.labels e ∈ C e := by
  classical
  rcases exists_hugeFirst_reorder (α₂ := α₂) ord with ⟨ord', hbigfirst, hprec⟩
  have hdeg := fwddeg_le_of_reorder (α₂ := α₂) ord ord' hprec
  -- lists satisfy the halved margin w.r.t. ord'
  have hC' : ∀ e : 𝓗,
      ((precedingDegree 𝓗 ord' e : ℝ) + (α₁ / 2) * (n : ℝ)) ≤ ((C e).card : ℝ) := by
    intro e
    have h₁ : (precedingDegree 𝓗 ord' e : ℝ) ≤
        (precedingDegree 𝓗 ord e : ℝ) + ((bigFinset α₂ 𝓗).card : ℝ) := by
      exact_mod_cast hdeg e
    have hb : ((bigFinset α₂ 𝓗).card : ℝ) ≤ (α₁ / 2) * (n : ℝ) := by
      have hEq : (α₁ * (n : ℝ)) / 2 = (α₁ / 2) * (n : ℝ) := by ring
      rw [← hEq]
      exact le_of_lt hbigmargin  -- hmm order of rwa/le
    have hCbig := hC e
    nlinarith
  -- margins for the engine with α₁/2
  have hm1 : (2 : ℝ) * (n : ℝ) / (α₂ * ((r : ℝ) - 1)) < ((α₁ / 2) * (n : ℝ)) / 2 := by
    have hEq : ((α₁ / 2) * (n : ℝ)) / 2 = (α₁ * (n : ℝ)) / 4 := by ring
    rwa [hEq]
  have hm2 : ((bigFinset α₂ 𝓗).card : ℝ) < (α₁ / 2) * (n : ℝ) := by
    have hEq : (α₁ / 2) * (n : ℝ) = (α₁ * (n : ℝ)) / 2 := by ring
    rwa [hEq]
  exact greedy_colouring_hugeFirst (n := n) (r := r) (k := k) (α₁ := α₁ / 2) (α₂ := α₂)
    (𝓗 := 𝓗) h2n h2r hα₂ hm1 hm2 hlin hsize ord' hbigfirst C hC'

/-! ## Prop 6.9: final per-instance statement (proved)

`Prop69Instance` records Prop 6.9 of the paper in the per-instance shape
used by the rest of the project: the margin bundle
`2 ≤ n`, `2 ≤ r`, `0 < α₁`, `0 < α₂`,
`2n/(α₂(r−1)) < α₁n/4` (heavy colours) and `#big < α₁n/2` (big edges)
implies, for every ordering and every list assignment whose lists are long
against the forward degrees, the existence of an `α₂`-bounded proper
edge-colouring respecting the lists.  It is proved from
`prop69_colouring` (`prop69Instance`). -/

/-- **Prop 6.9 (paper §6.3), per-instance statement.**  For a linear
`n`-vertex hypergraph whose edges all have size `≥ r`, with any ordering
`ord` of the edges and a list assignment `C` (every `C(e)` a set of colours
of size at least `d⪯(e) + α₁n`), an `α₂`-bounded proper edge-colouring
exists with `φ(e) ∈ C(e)` for every edge — provided the hierarchy margins
`2n/(α₂(r−1)) < α₁n/4` and `#big < α₁n/2` hold. -/
def Prop69Instance (n r : ℕ) (α₁ α₂ : ℝ) (𝓗 : Hypergraph (Fin n)) : Prop :=
  ((2 ≤ n) ∧ (2 ≤ r) ∧ (0 < α₁) ∧ (0 < α₂) ∧
    ((2 : ℝ) * (n : ℝ) / (α₂ * ((r : ℝ) - 1)) < (α₁ * (n : ℝ)) / 4) ∧
    (((bigFinset α₂ 𝓗).card : ℝ) < (α₁ * (n : ℝ)) / 2)) →
    ∀ {k : ℕ} (ord : 𝓗 ≃ Fin k),
      𝓗.IsLinear →
      (∀ e : 𝓗, (r : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ)) →
      ∀ C : 𝓗 → Finset (Fin n),
        (∀ e : 𝓗, ((precedingDegree 𝓗 ord e : ℝ) + α₁ * (n : ℝ)) ≤ ((C e).card : ℝ)) →
          ∃ φ : 𝓗.Coloring (Fin n), φ.AlphaBounded α₂ ∧ ∀ e : 𝓗, φ.labels e ∈ C e

/-- **Prop 6.9 holds** (proof: reorder to huge-first, halve `α₁`, run the
greedy engine `greedy_colouring_hugeFirst`). -/
theorem prop69Instance {n r : ℕ} {α₁ α₂ : ℝ} {𝓗 : Hypergraph (Fin n)} :
    Prop69Instance n r α₁ α₂ 𝓗 := by
  classical
  intro hbundle
  rcases hbundle with ⟨h2n, h2r, hα₁, hα₂, hmargin, hbigm⟩
  intro k ord hlin hsize C hC
  have hsizeN : ∀ e : 𝓗, (r : ℕ) ≤ edgeSize (e : Set (Fin n)) := by
    intro e
    exact_mod_cast hsize e
  exact prop69_colouring (n := n) (r := r) (k := k) (α₁ := α₁) (α₂ := α₂) (𝓗 := 𝓗)
    h2n h2r hα₂ hmargin hbigm hlin hsizeN ord C hC
