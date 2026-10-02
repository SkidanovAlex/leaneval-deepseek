import Submission.Work.Deep.Nibble.ObjDefs
import Submission.Work.Deep.Nibble.nibble_defs
import Submission.Work.Deep.Nibble.nibble_step
import Submission.Work.Deep.Nibble.nibble_main

/-!
# The per-set (family) clauses of the nibble

The Rödl–Pippenger–Spencer engine of this chapter (`nibble_main` →
`exists_matching_covering_most`) produces a matching covering all but a
`γ`-fraction of *all* vertices.  To obtain `cor:sparse_egj` — a matching leaving
a `γ`-fraction of every set of a prescribed family, with *relative* error — one
must track, in every round, the number of vertices of each prescribed set that
the round covers, and the multiplicity of colliding kept edges inside it.

This module adds exactly those two quantities (`covIn`, `collMultIn`) and the
per-set clause `RoundGoodFam`.  The plan (see `NOTES_SESSION5.md` §4) is

* `nibble_round2_fam` — one round as above, simultaneously with `RoundGood`;
* `nibble_iter_fam` — the iteration, tracking `|S ∩ U_j|` and `|S ∩ Acc_j|` per
  set, giving a matching leaving at most `3κ|S|` vertices of every (large enough)
  `S ∈ 𝓕`;
* the `γ`-thinning (random edge deletion with the weighted two-sided Chernoff
  bound and a union bound over `𝓕`) turning that into
  `|S ∖ V(M)| = (γ ± 4κ)|S|`, i.e. `SparseMatchingBody`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Deep.Nibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices of `S` covered by the kept edges of one round. -/
noncomputable def covIn (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Set V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v => v ∈ S ∧ v ∈ covX 𝓖 ω)).card

/-- The vertices of `S` left uncovered by one round. -/
noncomputable def uncovIn (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Set V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v => v ∈ S ∧ v ∉ covX 𝓖 ω)).card

/-- The collision multiplicity inside `S`: `∑_{v ∈ S} k_v 1[k_v ≥ 2]`, where
`k_v` is the number of kept edges through `v`. -/
noncomputable def collMultIn (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Set V) : ℕ := by
  classical
  exact ∑ v ∈ Finset.univ.filter (fun v : V => v ∈ S),
    (if 2 ≤ kAt 𝓖 ω v then kAt 𝓖 ω v else 0)

/-- **The per-set clauses of one round**: for every `S ∈ 𝓕` the round covers a
`(1-e^{-θ})`-fraction of `S` up to `δ|S|`, and the collision multiplicity inside
`S` — which bounds the vertices of `S` that are covered only by *deleted*
colliding kept edges, i.e. the "waste" inside `S` — is at most
`(1+δ)(θ-θe^{-θ})|S|`. -/
noncomputable def RoundGoodFam (𝓖 : Set (Set V)) (θ δ : ℝ) (𝓕 : Set (Set V))
    (ω : 𝓖 → Bool) : Prop :=
  (∀ S ∈ 𝓕,
      |((covIn 𝓖 ω S : ℝ)) - (1 - Real.exp (-θ)) * (S.ncard : ℝ)| ≤ δ * (S.ncard : ℝ)) ∧
  (∀ S ∈ 𝓕,
      ((collMultIn 𝓖 ω S : ℝ)) ≤ (1 + δ) * (θ - θ * Real.exp (-θ)) * (S.ncard : ℝ))

/-- **The family-nibble conclusion**: a matching of `𝓗` leaving at most `3κ|S|`
vertices of every (sufficiently large) `S ∈ 𝓕`. -/
def RelCoverBody (n : ℕ) (r : ℕ) (_γ κ : ℝ) : Prop :=
  ∀ D : ℝ, (n : ℝ) ^ ((1 : ℝ) / 100) ≤ D →
  ∀ 𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n),
    𝓗.IsLinear → (∀ e ∈ 𝓗, ErdosFaberLovaszConjecture.edgeSize e = r) →
    (∀ v : Fin n, |((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℝ)) - D| ≤ κ * D) →
    ∀ 𝓕 : Set (Set (Fin n)), (𝓕.ncard : ℝ) ≤ (n : ℝ) ^ (2 * Real.log n) →
      ∃ M : Set 𝓗, ErdosFaberLovaszConjecture.IsMatching 𝓗 M ∧
        ∀ S ∈ 𝓕, D ^ ((1 : ℝ) / 20) ≤ (S.ncard : ℝ) →
          ((S \ ErdosFaberLovaszConjecture.matchVert M).ncard : ℝ) ≤ 3 * κ * (S.ncard : ℝ)

/-- The family-nibble conclusion for every vertex count above a threshold. -/
def RelCoverAbove (N₀ : ℕ) (r : ℕ) (γ κ : ℝ) : Prop :=
  ∀ n : ℕ, N₀ ≤ n → RelCoverBody n r γ κ

end Work.Deep.Nibble
