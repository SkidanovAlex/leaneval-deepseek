import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.RelCover

/-!
# The `KahnStatement`-route to `RelCoverStatement`: vocabulary

The chapter `Submission/Work/Deep/Nibble/relCoverStatement_of_Kahn.lean` derives
`Work.Deep.Nibble.RelCoverStatement` from `ErdosFaberLovaszConjecture.KahnStatement`
by the *random-partition* route: split the vertex set randomly into `p` parts,
colour each induced sub-hypergraph with Kahn's soft `(1+α)Δ` result, and then
choose one colour class in every part uniformly at random.

This module only fixes the vocabulary of that route (the notation for the parts
of the partition, the induced sub-hypergraphs, the induced degrees, the property
of a "good" partition, and the edge set / vertex set of a colour class).

Everything is written with fully qualified names (`ErdosFaberLovaszConjecture…`)
because Mathlib's root `Hypergraph` would clash with the challenge's
`ErdosFaberLovaszConjecture.Hypergraph` once `import Mathlib` is in scope.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Deep.Nibble

open scoped BigOperators

/-- A hypergraph on `Fin n` (fully qualified, to avoid the root `Hypergraph`). -/
abbrev HG (n : ℕ) : Type := ErdosFaberLovaszConjecture.Hypergraph (Fin n)

/-- The vertices assigned to part `i` by the "partition" `π : Fin n → Fin p`. -/
def partSet {n p : ℕ} (π : Fin n → Fin p) (i : Fin p) : Set (Fin n) := {v | π v = i}

/-- The sub-hypergraph of `𝓗` induced by part `i`: its edges are the edges of
`𝓗` all of whose vertices lie in part `i`. -/
def partHyp {n p : ℕ} (𝓗 : HG n) (π : Fin n → Fin p) (i : Fin p) : HG n :=
  {e | e ∈ 𝓗 ∧ e ⊆ partSet π i}

/-- The number of edges of `𝓗` through `v` inside part `i` — i.e. the degree of
`v` in the induced sub-hypergraph `partHyp 𝓗 π i`. -/
noncomputable def degInPart {n p : ℕ} (𝓗 : HG n) (π : Fin n → Fin p) (v : Fin n)
    (i : Fin p) : ℕ :=
  ErdosFaberLovaszConjecture.hypergraphDegree (partHyp 𝓗 π i) v

/-- The edge set of a colour class `j` of a colouring `φ` of `𝓖`, viewed as a
family of edges of the ambient hypergraph. -/
def classEdges {n : ℕ} {𝓖 : HG n} {c : ℕ} (φ : 𝓖.Coloring (Fin c)) (j : Fin c) : HG n :=
  (fun e : 𝓖 => (e : Set (Fin n))) '' (φ.colorClass j)

/-- The vertex set covered by a colour class. -/
def classVert {n : ℕ} {𝓖 : HG n} {c : ℕ} (φ : 𝓖.Coloring (Fin c)) (j : Fin c) : Set (Fin n) :=
  ⋃₀ (classEdges φ j)

/-- **The property of a "good" random partition.**  With `κ` the degree spread of
`𝓗` and `ε'` the partition accuracy:

* the degree of every vertex in its own part deviates from `d(v)/p^{r-1}` by a
  relative error of at most `ε'` (for `v ∉ partSet π i` the induced degree is `0`,
  which is why the clause is restricted to `v ∈ partSet π i`);
* every prescribed set `S ∈ 𝓕` which is large (`D^{1/20} ≤ |S|`) meets every part
  in at most `2|S|/p` vertices. -/
def GoodPartition {n p : ℕ} (𝓗 : HG n) (r : ℕ) (ε' D : ℝ) (𝓕 : Set (Set (Fin n)))
    (π : Fin n → Fin p) : Prop :=
  (∀ (i : Fin p) (v : Fin n), v ∈ partSet π i →
      |((degInPart 𝓗 π v i : ℕ) : ℝ)
          - ((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ) / (p : ℝ) ^ (r - 1)|
        ≤ ε' * (((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ)
            / (p : ℝ) ^ (r - 1)))
  ∧ (∀ S ∈ 𝓕, D ^ ((1 : ℝ) / 20) ≤ (S.ncard : ℝ) →
      ∀ i : Fin p,
        ((S ∩ partSet π i).ncard : ℝ) ≤ 2 * ((S.ncard : ℝ) / (p : ℝ)))

end Work.Deep.Nibble
