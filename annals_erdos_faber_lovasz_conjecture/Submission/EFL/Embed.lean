import Submission.EFL.MultiHypergraph
import Submission.EFL.Counting

/-!
# §8: the embedding lemma `lem:embed`

This module records — as a faithful input statement — the case of Lemma
`lem:embed` of the paper (`efl.tex:535`) that is actually consumed by the proof
of `lem:pseudorandom_matching`.

The paper's statement is

> Let `0 < 1/N₀, 1/D₀, 1/C₀ ≪ 1/r ≤ 1/3`, where `r ∈ ℕ`. Let `N ≥ N₀`, `C ≥ C₀`,
> `D ≥ D₀`, and let `𝓗` be an `N`-vertex linear multi-hypergraph with
> `Δ(𝓗) ≤ D` and `|e| ≤ r` for every `e ∈ 𝓗`. Then there exists an `r`-uniform
> linear hypergraph `𝓗_unif` such that
>
> * **(E1)** `𝓗 ⊆ 𝓗_unif|_V` and `𝓗_unif|_V ∖ 𝓗` only contains singleton edges;
> * **(E2)** for any `v ∈ V(𝓗_unif)`, `D - C ≤ d_{𝓗_unif}(v) ≤ D`, and moreover
>   if `d_𝓗(v) ≥ D - C` for `v ∈ V(𝓗)` then `d_{𝓗_unif}(v) = d_𝓗(v)`;
> * **(E3)** `v(𝓗_unif) ≤ r(r-1)²D³N`.

## Why the statement below is the *regular* case

The proof (a modification of Lemma 8.1 of KKMO 2020) is: add `r - |e|` fresh
vertices to every edge of `𝓗` to obtain the `r`-uniform linear `𝓗*`; take
`T = r·p` vertex-disjoint copies of `𝓗*` (`p` a prime `≥ D`, so `T ≤ 2rD` and
(E3) follows); and, for each `v ∈ V(𝓗*)` of degree `< D - C`, glue on the `T`
clones of `v` a copy of an auxiliary `d`-regular linear `r`-uniform design
(`d := D - d_{𝓗*}(v)`), which exists by
`Commons.Combinatorics.Hypergraph.exists_linear_regular_uniform`.

Now, **in the application of `lem:embed` inside `lem:pseudorandom_matching`**
the input `𝓗'` satisfies `d_{𝓗'}(w) = (1 ± β)D` at every `w ∈ V(𝓗')`, and
`lem:embed` is invoked with `D ↦ (1+β)D` and `C ↦ 2βD`; hence
`d_{𝓗'}(w) ≥ (1-β)D = D - C` for every `w ∈ V(𝓗')`, so **no design at all is
glued at a non-isolated old vertex**.  Consequently `E_meet := {e ∈ 𝓗_unif :
e ∩ V(𝓗') ≠ ∅}` is exactly the set of copy-`0` edges of `𝓗_unif`, and the map
`ψ : e ↦ e ∩ V(𝓗')` really is a *bijection* onto the edges of `𝓗'` counted with
multiplicity — which is the form in which the proof of
`lem:pseudorandom_matching` uses it (`efl.tex:1670`).

Without that regularity hypothesis, `κ` below is only an injection (a design
edge glued at a *non-isolated* vertex `v` with `d_𝓗(v) < D - C` also meets
`V(𝓗)`), and `ψ` is not surjective onto `𝓗`'s edge multiset.  Rather than
formalise the general (and, as written in the paper, imprecisely stated) case,
we record the regular case, which is *weaker* as a `Prop` than the paper's
lemma and hence is implied by it.

## The cone's formulation

The cone's `MultiHypergraph N` already carries multiplicities (the proper edges
`edges` together with a *multiplicity* `singles v` of the singleton edge `{v}`),
which is exactly the input form used in `lem:pseudorandom_matching`.

`V := {v : Fin N | 0 < 𝓗.deg v}` is the vertex set of `𝓗`; the vertex set of
`𝓗_unif` is `Fin M` and `ι : Fin N ↪ Fin M` embeds the old vertices; the
bijection `κ` identifies the `𝓗_unif`-edges meeting `ι '' V` — the `ψ` of the
paper — with the edges of `𝓗` counted with multiplicity.

In particular, when `𝓗` has no isolated vertices and every degree lies in
`[D - C, D]`, `V = univ` and this is `lem:embed` verbatim.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

/-- **`lem:embed` (the regular case).**  For `2 ≤ r`, there is `C₀ ≫ r` (in
fact any `C ≥ C₀`) such that for every linear `N`-vertex multi-hypergraph `𝓗`
with `|e| ≤ r`, degrees at most `D`, and `D - C ≤ d_𝓗(v)` at every
*non-isolated* vertex `v`, there is an `r`-uniform linear hypergraph `𝓖` on
`M ≤ r(r-1)²D³N` vertices, an embedding `ι : Fin N ↪ Fin M`, and a bijection
`κ` (`ψ` of the paper) between the edges of `𝓖` meeting `ι '' V(𝓗)` and the
edges of `𝓗` counted with multiplicity, such that the degrees of `𝓖` lie in
`[D - C, D]` and agree with those of `𝓗` at non-isolated vertices. -/
def EmbedStatement : Prop :=
  ∀ r : ℕ, 3 ≤ r →
    ∃ C₀ : ℝ, 0 < C₀ ∧ (r : ℝ) ≤ C₀ ∧
    -- `D ≥ 1`: the paper's `D ≥ D₀` (with `1/D₀ ≪ 1/r`).  Without it the
    -- statement is false: an edgeless `𝓗` with `D < (r(r-1)²)^{-1/3}` forces
    -- `N ≤ M ≤ r(r-1)²D³N < N` (found by `Deep/Nibble`).
    ∀ N : ℕ, ∀ C D : ℝ, C₀ ≤ C → 0 < D → (1 : ℝ) ≤ D →
    ∀ 𝓗 : MultiHypergraph N, 𝓗.IsLinear →
      (∀ e ∈ 𝓗.edges, edgeSize e ≤ r) →
      (∀ v : Fin N, (𝓗.deg v : ℝ) ≤ D) →
      (∀ v : Fin N, 0 < 𝓗.deg v → D - C ≤ (𝓗.deg v : ℝ)) →
      ∃ (M : ℕ) (ι : Fin N ↪ Fin M) (𝓖 : Hypergraph (Fin M))
        (κ : ({e : Set (Fin N) // e ∈ 𝓗.edges} ⊕
              {p : Fin N × ℕ // p.2 < 𝓗.singles p.1}) ≃
              {e : Set (Fin M) //
                e ∈ 𝓖 ∧ (e ∩ ι '' {v : Fin N | 0 < 𝓗.deg v}).Nonempty}),
        -- `𝓖` is `r`-uniform and linear
        (∀ e ∈ 𝓖, edgeSize e = r) ∧
        𝓖.IsLinear ∧
        -- **(E3)** the number of vertices
        (M : ℝ) ≤ (r : ℝ) * ((r : ℝ) - 1) ^ 2 * D ^ 3 * (N : ℝ) ∧
        -- **(E1)** the identification of the edges (`ψ e* = e* ∩ V(𝓗)`)
        (∀ (e : Set (Fin N)) (he : e ∈ 𝓗.edges),
            ((κ (Sum.inl ⟨e, he⟩) : Set (Fin M)) ∩ ι '' {v : Fin N | 0 < 𝓗.deg v})
              = ι '' e) ∧
        (∀ (v : Fin N) (k : ℕ) (hk : k < 𝓗.singles v),
            (κ (Sum.inr ⟨(v, k), hk⟩) : Set (Fin M)) ∩ ι '' {v : Fin N | 0 < 𝓗.deg v}
              = {ι v}) ∧
        -- **(E2)** the degree conditions
        (∀ w : Fin M, D - C ≤ (MultiHypergraph.hdeg 𝓖 w : ℝ) ∧
          (MultiHypergraph.hdeg 𝓖 w : ℝ) ≤ D) ∧
        (∀ v : Fin N, 0 < 𝓗.deg v → MultiHypergraph.hdeg 𝓖 (ι v) = 𝓗.deg v)

end

end ErdosFaberLovaszConjecture
