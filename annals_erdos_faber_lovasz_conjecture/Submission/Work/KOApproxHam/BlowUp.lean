import Submission.Work.KOApproxHam.Assembly

/-!
# The blow-up vocabulary of the approximate Hamilton decomposition

This module provides the *concrete* structures that the two named steps of `Defs.lean` are proved
against, and the finer decomposition of the blow-up packing step into

* the **slicing step** `SliceStatement` — the reduced graph is regularised (max-flow/min-cut),
  decomposed into `1`-factors and lifted to edge-disjoint *regular* spanning subgraphs of `G`, each
  a blow-up of a cycle cover of the reduced graph whose pairs are dense-uniform;
* the **merging step** `SlicePackingStatement` — a blow-up slice of `G` contains edge-disjoint
  Hamilton cycles covering all but an `η`-fraction of its degree (Osthus–Staden §7).

## Contents

* `cycleBlowUpProd`, `cycleBlowUp` — the blow-up `C_k[m]` of a cycle, the model slice
  (`Work.KOApproxHam.hasHamiltonDecomposition_cycleBlowUp`, delegated);
* `mergeEdges` — the elementary merge of two cycles of a `1`-factor
  (`Work.KOApproxHam.merge_two_cycles`, delegated);
* `HamPackingI` — packings indexed by an arbitrary finite type, with the cardinality transport
  `HamPackingI.toPacking`;
* `IsBlowUpSlice`, `SliceFamily`, `SliceStatement`, `SlicePackingStatement`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.KOApproxHam

open Work.Deep.GKO

noncomputable section

variable {n k : ℕ}

/-! ## The blow-up of a cycle -/

/-- The **blow-up of the cycle `C_k` by `m`**, as a graph on the product `Fin k × Fin m`: two
vertices are adjacent when their first coordinates are consecutive on the cycle.  (The
conjunct `x ≠ y` is what makes the definition loopless for `k ≤ 1`; for `3 ≤ k` it is
redundant.  Note that the graph has no edges inside a part, and that the two parts
`Fin k × {j}` corresponding to non-consecutive indices are non-adjacent.) -/
def cycleBlowUpProd (k m : ℕ) [NeZero k] : SimpleGraph (Fin k × Fin m) where
  Adj x y := ((x.1 + 1 = y.1) ∨ (y.1 + 1 = x.1)) ∧ x ≠ y
  symm := Std.Symm.mk (fun x y h => ⟨h.1.symm, h.2.symm⟩)
  loopless := Std.Irrefl.mk (fun x h => h.2 rfl)

/-- The blow-up of a cycle, transported to the vertex type `Fin (k * m)`. -/
def cycleBlowUp (k m : ℕ) [NeZero k] : SimpleGraph (Fin (k * m)) :=
  SimpleGraph.comap finProdFinEquiv.symm (cycleBlowUpProd k m)

/-! ## Merging two cycles of a `1`-factor -/

/-- **The elementary cycle merge.**  Delete the edges `a₁a₂` and `b₁b₂` from `F` and add the
cross edges `a₁b₁` and `a₂b₂`.  If `a₁a₂` and `b₁b₂` are edges of `F` lying on *different* cycles
of the `1`-factor `F`, this merges those two cycles (see
`Work.KOApproxHam.merge_two_cycles`). -/
def mergeEdges (F : SimpleGraph (Fin n)) (a₁ a₂ b₁ b₂ : Fin n) : SimpleGraph (Fin n) :=
  (F \ SimpleGraph.fromEdgeSet {s(a₁, a₂), s(b₁, b₂)}) ⊔
    SimpleGraph.fromEdgeSet {s(a₁, b₁), s(a₂, b₂)}

/-! ## Packings indexed by a general finite type -/

/-- A packing of edge-disjoint Hamilton cycles of `G` indexed by an arbitrary type.  This is the
form in which packings of different slices are combined: the union of the index types is a sigma
type, whose cardinality transport gives `HamiltonCyclePacking` again. -/
def HamPackingI (G : SimpleGraph (Fin n)) (ι : Type*) (C : ι → SimpleGraph (Fin n)) : Prop :=
  (∀ i, C i ≤ G) ∧ (∀ i, IsHamiltonCycle' (C i)) ∧
    (∀ i j, i ≠ j → Disjoint (C i).edgeSet (C j).edgeSet)

/-- A packing indexed by a finite type gives a packing indexed by `Fin` of its cardinality. -/
theorem HamPackingI.toPacking {G : SimpleGraph (Fin n)} {ι : Type*} [Fintype ι]
    {C : ι → SimpleGraph (Fin n)} (h : HamPackingI G ι C) :
    HamiltonCyclePacking G (Fintype.card ι) := by
  classical
  refine ⟨fun j => C ((Fintype.equivFin ι).symm j), ?_, ?_, ?_⟩
  · intro j; exact h.1 _
  · intro j; exact h.2.1 _
  · intro i j hij
    exact h.2.2 _ _ (fun hc => hij ((Fintype.equivFin ι).symm.injective hc))

/-- The cycles of a slice packing, as a family over the sigma type of the slice index and the
cycle index. -/
def sigmaPacking {t : ℕ} {u : Fin t → ℕ}
    (Cs : ∀ i : Fin t, Fin (u i) → SimpleGraph (Fin n)) :
    (Σ i : Fin t, Fin (u i)) → SimpleGraph (Fin n) :=
  fun x => Cs x.1 x.2

/-- **Combining the packings of edge-disjoint slices.** -/
theorem hamPackingI_sigma {t : ℕ} {u : Fin t → ℕ} {G : SimpleGraph (Fin n)}
    {Gs : Fin t → SimpleGraph (Fin n)} {Cs : ∀ i : Fin t, Fin (u i) → SimpleGraph (Fin n)}
    (hslice : ∀ i : Fin t, Gs i ≤ G)
    (hdisj : ∀ i j : Fin t, i ≠ j → Disjoint (Gs i).edgeSet (Gs j).edgeSet)
    (hpack : ∀ i : Fin t, HamPackingI (Gs i) (Fin (u i)) (Cs i)) :
    HamPackingI G (Σ i : Fin t, Fin (u i)) (sigmaPacking Cs) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, j⟩
    change Cs i j ≤ G
    exact le_trans ((hpack i).1 j) (hslice i)
  · rintro ⟨i, j⟩
    change IsHamiltonCycle' (Cs i j)
    exact (hpack i).2.1 j
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hne
    change Disjoint (Cs i j).edgeSet (Cs i' j').edgeSet
    by_cases hii : i = i'
    · subst hii
      have hjj : j ≠ j' := by
        intro hc; exact hne (by simp [hc])
      exact (hpack i).2.2 j j' hjj
    · exact Disjoint.mono (SimpleGraph.edgeSet_mono ((hpack i).1 j))
        (SimpleGraph.edgeSet_mono ((hpack i').1 j')) (hdisj i i' hii)

/-! ## Blow-up slices -/

/-! ## The number of cycles of a permutation -/

/-- The orbit of `i` under the cyclic group generated by `σ`, as a finset. -/
noncomputable def orbitFinset {k : ℕ} (σ : Fin k ≃ Fin k) (i : Fin k) : Finset (Fin k) := by
  classical exact Finset.univ.filter (fun j => ∃ t : ℕ, (σ ^ t) i = j)

/-- **The number of cycles of the permutation `σ`**: the number of orbits of the cyclic subgroup
generated by `σ`.  This is the number of *cycles of the cycle cover* `permGraph σ`, and it is the
quantity that controls the merging step of Osthus–Staden §7: each cycle of the cover needs a
*bridge* (an exceptional vertex) to be merged into the next one. -/
noncomputable def permCycleCount {k : ℕ} (σ : Fin k ≃ Fin k) : ℕ :=
  (Finset.univ.image (fun i : Fin k => orbitFinset σ i)).card

theorem permCycleCount_le {k : ℕ} (σ : Fin k ≃ Fin k) : permCycleCount σ ≤ k := by
  classical
  unfold permCycleCount
  calc (Finset.univ.image (fun i : Fin k => orbitFinset σ i)).card
      ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
    _ = k := by simp

theorem orbitFinset_self {k : ℕ} (σ : Fin k ≃ Fin k) (i : Fin k) : i ∈ orbitFinset σ i := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨0, ?_⟩⟩
  simp

/-- If the number of cycles of `σ` is at most one, then `σ` is a single cycle (transitive), with
the convention that the empty permutation (on `Fin 0`) is a single cycle vacuously. -/
theorem isSingleCyclePerm_of_permCycleCount_le_one {k : ℕ} (σ : Fin k ≃ Fin k)
    (h : permCycleCount σ ≤ 1) : IsSingleCyclePerm σ := by
  classical
  intro i j
  unfold permCycleCount at h
  have hi : orbitFinset σ i ∈ Finset.univ.image (fun i : Fin k => orbitFinset σ i) :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hj : orbitFinset σ j ∈ Finset.univ.image (fun i : Fin k => orbitFinset σ i) :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have heq : orbitFinset σ i = orbitFinset σ j := (Finset.card_le_one.mp h) _ hi _ hj
  have hmem : j ∈ orbitFinset σ j := orbitFinset_self σ j
  rw [← heq] at hmem
  exact (Finset.mem_filter.mp hmem).2

/-- **A blow-up slice along a cycle cover `σ` of the reduced graph.**  Every edge of `H` joins
`σ`-matched clusters or is incident to an exceptional vertex, and each `σ`-matched pair of clusters
is `(ε,d)`-dense-uniform in `H`.

**Why the adjacency clause is stated for both orderings (the fifth interface defect).**  The
clause has to allow an edge `xy` with `x ∈ parts i`, `y ∈ parts (σ i)` in *either* order — i.e. it
must be the symmetric condition

`(∃ i, x ∈ parts i ∧ y ∈ parts (σ i)) ∨ (∃ i, y ∈ parts i ∧ x ∈ parts (σ i)) ∨ x ∈ exc ∨ y ∈ exc`.

The earlier form kept only the first disjunct, and since it was quantified over *ordered* pairs
`x y` it was applied to both orderings of every edge; because the pair `(parts i, parts (σ i))`
carries an edge whenever `d > 0` (the last conjunct of this definition is dense-uniformity of
positive density), that version forced `σ (σ i) = i` for **every** `i` — the cycle cover had to be
an involution, so no blow-up of a long cycle was ever a slice, and the slicing statements were
refuted outright (see `NOTES.md` §12.8 and the review gate's `Work.KOApproxHam.blowUpSlice_involution`
in the session log).  With the symmetric clause, the blow-up of a `k`-cycle is a slice, as intended.

**The bridge (counting) condition** — the second conjunct — is what makes the merging step of
Osthus–Staden §7 available: either `σ` is a *single* cycle of the reduced graph (so the slice is a
blow-up of one cycle and the unwinding argument of their §4 merges it into a Hamilton cycle without
any bridge), or `σ` has at most `|V_exc|` cycles, i.e. there are enough *bridge* vertices (the
exceptional vertices, which the paper uses as `x_1, …, x_ℓ` between consecutive cycles
`D_1 x_1 D_2 x_2 … x_ℓ D_1` of the cover) to merge the cycles of the cover one into the next.

**Why `|V_exc|` and not `|V_exc| + 1` (fourth interface defect, `NOTES.md` §12.7).**  The bound is
*necessary* and the review gate refuted the `+1` form twice: `H ∖ V_exc` is a disjoint union of the
`permCycleCount σ` blocks of the cover, and a Hamilton cycle minus `|V_exc|` vertices is a union of
at most `|V_exc|` paths, each inside one block, which therefore forces
`permCycleCount σ ≤ |V_exc|`.  In the boundary case `permCycleCount σ = |V_exc| + 1` (e.g. `σ` a
product of transpositions with the exceptional vertices attached in a path linking the blocks) all
the other hypotheses hold, `H` is connected and even-regular, and yet there is no Hamilton cycle at
all.

**Why not simply drop `IsSingleCyclePerm` (read this before changing the definition).**  The
relaxation *without* the counting condition is **false**: with `σ` a product of `2`-cycles, no
exceptional vertices and each matched pair complete bipartite, the slice is a disjoint union of
`K_{m,m}`'s with no Hamilton cycle at all; and with one exceptional vertex adjacent to every block
the slice is connected (even `2`-connected with two such vertices) but still has no Hamilton cycle,
because every cycle would have to hop between the `k/2` blocks through at most four exceptional
endpoints.  Both are recorded in `NOTES.md` §9, and the counting condition excludes them
(`work.KOApproxHam.not_isBlowUpSlice_twoCycleCover` below).  The single-cycle form
(`IsBlowUpSliceSingle` below) *implies* the condition used here, so this definition is a genuine
relaxation: it is what turns `SliceStatement` from a demand for a *Hamiltonian* cover of the reduced
graph — a cover of `E(R)` by Hamilton cycles, i.e. essentially a Hamilton decomposition of `R`, the
very theorem being proved — into the paper's demand for a cover of `R` by *`1`-factors / cycle
covers*, which `Petersen` (`Work.KOApproxHam.exists_twoFactorDecomposition`) supplies. -/
def IsBlowUpSlice (𝓒 : ClusterSystem n k) (R : SimpleGraph (Fin k)) (σ : Fin k ≃ Fin k)
    (ε d : ℝ) (H : SimpleGraph (Fin n)) : Prop :=
  IsCycleCover R σ ∧
    (IsSingleCyclePerm σ ∨ permCycleCount σ ≤ 𝓒.exc.card) ∧
    (∀ x y : Fin n, H.Adj x y →
      (∃ i : Fin k, x ∈ 𝓒.parts i ∧ y ∈ 𝓒.parts (σ i)) ∨
      (∃ i : Fin k, y ∈ 𝓒.parts i ∧ x ∈ 𝓒.parts (σ i)) ∨ x ∈ 𝓒.exc ∨ y ∈ 𝓒.exc) ∧
    (∀ i : Fin k, IsDenseUniform H ε d (𝓒.parts i) (𝓒.parts (σ i)))

/-- The **single-cycle** form of a blow-up slice: the form in which the chapter's earlier sessions
stated the slicing and merging steps (`σ` a *Hamilton* cycle of the reduced graph).  It is stronger
than `IsBlowUpSlice` — hence a slice family in this form is also a family in the relaxed form — and
it is the form that `Work.Deep.GKO.exists_cycleCover_of_robustExpander` and
`Work.KOApproxHam.exists_cycleCover_and_singleCyclePerm` produce.  Its drawback is that a family of
such slices covering all but `ζ` of the degree has to cover *every* edge of `R` by Hamilton cycles
of `R` (see the docstring of `IsBlowUpSlice`), which is why the statements are phrased with the
relaxed form. -/
def IsBlowUpSliceSingle (𝓒 : ClusterSystem n k) (R : SimpleGraph (Fin k)) (σ : Fin k ≃ Fin k)
    (ε d : ℝ) (H : SimpleGraph (Fin n)) : Prop :=
  IsCycleCover R σ ∧ IsSingleCyclePerm σ ∧
    (∀ x y : Fin n, H.Adj x y →
      (∃ i : Fin k, x ∈ 𝓒.parts i ∧ y ∈ 𝓒.parts (σ i)) ∨
      (∃ i : Fin k, y ∈ 𝓒.parts i ∧ x ∈ 𝓒.parts (σ i)) ∨ x ∈ 𝓒.exc ∨ y ∈ 𝓒.exc) ∧
    (∀ i : Fin k, IsDenseUniform H ε d (𝓒.parts i) (𝓒.parts (σ i)))

theorem isBlowUpSlice_of_single {𝓒 : ClusterSystem n k} {R : SimpleGraph (Fin k)}
    {σ : Fin k ≃ Fin k} {ε d : ℝ} {H : SimpleGraph (Fin n)}
    (h : IsBlowUpSliceSingle 𝓒 R σ ε d H) : IsBlowUpSlice 𝓒 R σ ε d H :=
  ⟨h.1, Or.inl h.2.1, h.2.2.1, h.2.2.2⟩



/-- **Machine-checked evidence for the bridge (counting) condition**: if the cluster system has *no*
exceptional vertices then a blow-up slice can only be a blow-up of a *single* cycle of the reduced
graph.  This is precisely what excludes the counterexamples to the `IsSingleCyclePerm`-free
relaxation of the slicing/merging steps (recorded in `NOTES.md` §9): the disjoint union of blown-up
`K_{m,m}`'s along a product of `2`-cycles — with or without exceptional vertices attached to every
block — is a blow-up along a cover with `k/2 ≥ 2` cycles and is *not* a slice in the sense of
`IsBlowUpSlice`, because there are not enough bridge vertices. -/
theorem isSingleCyclePerm_of_isBlowUpSlice_of_no_exc {𝓒 : ClusterSystem n k}
    {R : SimpleGraph (Fin k)} {σ : Fin k ≃ Fin k} {ε d : ℝ} {H : SimpleGraph (Fin n)}
    (hexc : 𝓒.exc.card = 0) (h : IsBlowUpSlice 𝓒 R σ ε d H) : IsSingleCyclePerm σ := by
  rcases h.2.1 with h1 | h2
  · exact h1
  · exact isSingleCyclePerm_of_permCycleCount_le_one σ (by omega)/-- **A family of slices**: pairwise edge-disjoint regular spanning subgraphs of `G`, each a
blow-up slice of the reduced graph (along a Hamilton cycle of `R`), covering all but a
`ζ`-fraction of the degree *of the pure part*: `(1-ζ)(r - γn) ≤ ∑ rs i`.  The coverage is measured
against the pure part because neither the edges lost to the degree form nor the edges inside
clusters can be covered by a slice, and it is uniform over the vertices because the slices are
regular. -/
structure SliceFamily (n k : ℕ) (G : SimpleGraph (Fin n)) (𝓒 : ClusterSystem n k)
    (R : SimpleGraph (Fin k)) (r : ℕ) (εp dp ζ : ℝ) where
  /-- the loss fraction of the certificate (every non-exceptional vertex keeps all but `γ n` of its
  neighbours in the pure subgraph, so no slice can cover those edges either) -/
  γ : ℝ
  /-- the attachment fraction of exceptional vertices (a slice must attach each exceptional vertex
  to some cluster, otherwise the exceptional vertices form a component of their own and there is no
  spanning Hamiltonian subgraph) -/
  c : ℝ
  /-- the number of slices -/
  t : ℕ
  /-- the slices -/
  Gs : Fin t → SimpleGraph (Fin n)
  /-- their degrees -/
  rs : Fin t → ℕ
  /-- their cycle covers -/
  σs : Fin t → (Fin k ≃ Fin k)
  hle : ∀ i, Gs i ≤ G
  hreg : ∀ i, IsRegularOf (Gs i) (rs i)
  hdisj : ∀ i j, i ≠ j → Disjoint (Gs i).edgeSet (Gs j).edgeSet
  hslice : ∀ i, IsBlowUpSlice 𝓒 R (σs i) εp dp (Gs i)
  hcover : (1 - ζ) * ((r : ℝ) - γ * (n : ℝ)) ≤ ∑ i, (rs i : ℝ)
  hcpos : 0 < c
  /-- the slices have **even** degree`; an odd degree would force a leftover of at least one edge
  per vertex, which no `η`-bound can absorb -/
  heven : ∀ i, Even (rs i)
  /-- every slice attaches each exceptional vertex to a cluster -/
  hatt : ∀ i, ∀ x ∈ 𝓒.exc, ∃ j : Fin k,
    c * ((𝓒.parts j).card : ℝ) ≤ (degIn (Gs i) x (𝓒.parts j) : ℝ)
  /-- **every slice is connected.**  This is a *genuine* requirement of the merging step and not a
  consequence of the other fields: the blow-up of a multi-cycle cover `σ` is a disjoint union of its
  `σ`-blocks, so the exceptional vertices have to *bridge* the blocks.  The merging step
  (`SlicePackingStatement`) consumes it, and the slicing step has to produce it — see `NOTES.md`
  §12.7, where the counting condition `permCycleCount σ ≤ |exc| + 1` is shown (machine-checked, by
  the review gate) to be *insufficient* on its own: a "slice" that is a disjoint union of dense
  blocks, with all the exceptional vertices attached inside the first block, satisfies every other
  field and has no Hamilton cycle at all. -/
  hconn : ∀ i, (Gs i).Preconnected

/-! ## The two named steps of the blow-up packing -/

/-- **The slicing step** (Osthus–Staden §5–§6): the regularised reduced graph is decomposed into
cycle covers and lifted to a family of edge-disjoint regular blow-up slices covering all but a
`ζ`-fraction of the degree of `G`.

**Read this before attacking it (a second structural defect, found by this chapter's fleet).**  The
certificate's pair hypothesis `hpairs` is only `IsDenseUniform` — uniformity of density `≥ dp`, which
constrains *pairs of large subsets* and gives **no per-vertex control**.  The lifting step, however,
needs a spanning bipartite subgraph of prescribed degree `κ - (red degree)` on each matched pair,
and that requires every vertex of a cluster to see `(1 ± ε) dp m` neighbours in the adjacent cluster:
a pair of density `dp ≥ 1/4` can split as `A = A₁ ⊔ A₂`, `B = B₁ ⊔ B₂` with all `A₁`-neighbours
inside `B₁`, whence `e(A₁, B∖B₁) = 0` while Ore's cut condition demands `e(X, B∖Y) ≥ κ(|X| - |Y|)` —
false at `X = A₁`, `Y = B₁`.  The repair is Osthus–Staden's §6 *consistent system*: refine the
certificate so that every adjacent pair carries the per-vertex degree window.  That is the named
input `Work.KOApproxHam.ConsistentSystemStatement`, and the slicing step with the window is
`Work.KOApproxHam.SliceStatementW` (`ConsistentSystem.lean`); the *pair* of them replaces this
statement in the assembly of the chapter
(`Work.KOApproxHam.approxHamDecompStatement_of_stepsW`, `AssemblyW.lean`).  What this statement
records is the degree plan itself, which is the same in both forms. -/
def SliceStatement : Prop :=
  ∀ (εp dp c γ ζ : ℝ), 0 < εp → εp ≤ dp → dp ≤ c → c ≤ 1 / 4 → 0 < γ → 0 < ζ →
    ∃ K n₀ : ℕ, 1 ≤ K ∧ 1 ≤ n₀ ∧ ∀ k ≥ K, ∀ n ≥ n₀, ∀ m : ℕ, 1 ≤ m →
      ∀ (r : ℕ) (G : SimpleGraph (Fin n)) (Cert : BlowUpCert n k m εp dp c γ G r),
        ∃ S : SliceFamily n k G Cert.𝓒 Cert.R r εp dp ζ, S.γ ≤ γ ∧ S.c = c

/-- **The merging step** (Osthus–Staden §7): a *connected* regular blow-up slice of *even* degree,
whose exceptional vertices are attached to the clusters, contains edge-disjoint Hamilton cycles
covering all but an `η`-fraction of its degree.

**Read this before attacking it (the fourth interface defect of the chapter, `NOTES.md` §12.7).**
The hypothesis `H.Preconnected` is not decorative: the review gate refuted the earlier form (without
it) by taking `k = 2s`, `σ` the product of the `s` transpositions `(C_{2j+1} C_{2j+2})` with
`exc = {x₁, …, x_{s−1}}` (so the counting condition `permCycleCount σ ≤ |exc| + 1` of
`IsBlowUpSlice` *does* hold) and attaching every exceptional vertex only to the clusters `C₁`, `C₂`
of the *first* block.  All the other hypotheses hold, `H` is a disjoint union of `s` dense blocks,
hence has no Hamilton cycle at all — while the conclusion demands one.  The counting condition is
therefore only a cardinality bound; the bridges have to be *placed*, and connectedness is the
weakest placement condition that rules the refutation out (the paper's `H₀`-structure is what
actually places them, see `NOTES.md` §12.7).  The merging uses, for a `2`-factor whose cycles wind around
the cover `σ`, edges outside the factors, which are supplied by the residual `2κ`-regular part of
the slice and by the *bridge* exceptional vertices (one per cycle of the cover, the paper's
`D_1 x_1 D_2 … x_ℓ D_1`, and hence the counting condition inside `IsBlowUpSlice`).  (Both extra hypotheses are needed: an odd-degree slice
forces a leftover of at least one edge per vertex, and an unattached exceptional vertex forms a
component of its own, so neither can be spanned by Hamilton cycles.) -/
def SlicePackingStatement : Prop :=
  ∀ (εp dp c γ η : ℝ), 0 < εp → εp ≤ dp → dp ≤ c → c ≤ 1 / 4 → 0 < γ → 0 < η →
    ∃ K n₀ : ℕ, 1 ≤ K ∧ 1 ≤ n₀ ∧ ∀ k ≥ K, ∀ n ≥ n₀, ∀ m : ℕ, 1 ≤ m →
      ∀ (rH : ℕ) (H : SimpleGraph (Fin n)) (𝓒 : ClusterSystem n k) (R : SimpleGraph (Fin k))
        (σ : Fin k ≃ Fin k),
        IsRegularOf H rH → Even rH → (∀ i : Fin k, (𝓒.parts i).card = m) →
        (∀ x : Fin n, x ∉ 𝓒.exc → ∃ i : Fin k, x ∈ 𝓒.parts i) →
        (∀ x ∈ 𝓒.exc, ∃ i : Fin k, c * (m : ℝ) ≤ (degIn H x (𝓒.parts i) : ℝ)) →
        IsBlowUpSlice 𝓒 R σ εp dp H → H.Preconnected →
        ∃ t : ℕ, HamiltonCyclePacking H t ∧ (rH : ℝ) - 2 * (t : ℝ) ≤ η * (rH : ℝ)

end

end Work.KOApproxHam
