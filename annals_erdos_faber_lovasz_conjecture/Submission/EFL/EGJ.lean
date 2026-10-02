import Submission.EFL.DeepInputs
import Submission.EFL.Matching
import Submission.EFL.Reservoir

/-!
# The Ehard–Glock–Joos matching theorem (§8, `thm:egj`) and its sparsified form

The Nibble Lemma (`lem:pseudorandom_matching`) of §8 rests on a special case of
a result of Ehard, Glock and Joos, which gives a matching covering almost all
vertices of every set in a prescribed collection of vertex sets.  Following the
pattern of `KahnStatement` in `DeepInputs.lean`, we record it (and its
"sparsified" corollary `cor:sparse_egj`) as `Prop`-valued input statements so
that §8 can be formalised conditionally on these deep inputs.

* `degreeSum 𝓗 S = ∑_{v ∈ S} d_𝓗(v)`;
* `EGJStatement` — Theorem `thm:egj`;
* `SparseEGJStatement` — Corollary `cor:sparse_egj`.
-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The sum of the degrees `∑_{v ∈ S} d_𝓗(v)` of the vertices of a set `S`. -/
def degreeSum (𝓗 : Hypergraph (Fin n)) (S : Set (Fin n)) : ℝ := by
  classical
  exact ((Finset.univ : Finset (Fin n)).filter (fun v => v ∈ S)).sum
    (fun v => (hypergraphDegree 𝓗 v : ℝ))

/-- **Theorem `thm:egj` (Ehard–Glock–Joos) as an input statement.**  For
`r ≥ 2`, with `ε := 1/(1500 r²)`, there is `Δ₀` such that for every `Δ ≥ Δ₀`,
every `r`-uniform linear hypergraph `𝓗` on `Fin n` with maximum degree at most
`Δ` and at most `exp(Δ^{ε²})` edges, and every family `𝓕` of at most
`exp(Δ^{ε²})` vertex sets with `∑_{v ∈ S} d_𝓗(v) ≥ Δ^{26/25}` for every
`S ∈ 𝓕`, there is a matching `M` of `𝓗` with
`|S ∩ V(M)| = (1 ± Δ^{-ε²}) · (∑_{v ∈ S} d_𝓗(v))/Δ` for every `S ∈ 𝓕`. -/
def EGJStatement : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
    ∀ Δ : ℝ, Δ₀ ≤ Δ → ∀ n : ℕ, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear →
      (∀ e ∈ 𝓗, edgeSize e = r) →
      ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) ≤ Δ →
      (Nat.card 𝓗 : ℝ) ≤ Real.exp (Δ ^ ((1 / (1500 * (r : ℝ) ^ 2)) ^ 2)) →
      ∀ 𝓕 : Set (Set (Fin n)),
        (𝓕.ncard : ℝ) ≤ Real.exp (Δ ^ ((1 / (1500 * (r : ℝ) ^ 2)) ^ 2)) →
        (∀ S ∈ 𝓕, Δ ^ ((26 : ℝ) / 25) ≤ degreeSum 𝓗 S) →
        ∃ M : Set 𝓗, IsMatching 𝓗 M ∧
          ∀ S ∈ 𝓕,
            |(((S ∩ matchVert M).ncard : ℝ) - degreeSum 𝓗 S / Δ)| ≤
              Δ ^ (-((1 / (1500 * (r : ℝ) ^ 2)) ^ 2)) * (degreeSum 𝓗 S / Δ)

/-- **Corollary `cor:sparse_egj` as an input statement.**  For `r ≥ 2` and
`0 < 1/n₀ ≪ 1/r, κ, γ < 1` (i.e. `n₀ = n₀(r, κ, γ)`), for an `r`-uniform linear
hypergraph on `Fin n` with `n ≥ n₀` all of whose degrees are `(1 ± κ)D` with
`D ≥ n^{1/100}`, and any family `𝓕` of at most `n^{2 log n}` vertex sets, there
is a matching `M` with `|S ∖ V(M)| = (γ ± 4κ)|S|` for every `S ∈ 𝓕` with
`|S| ≥ D^{1/20}`.

**Quantifier order corrected (2026-09-22, found by the `Deep/Nibble`
subproject).**  In the first formalisation the threshold `n₀` came *before*
`κ, γ` (`∀ r, ∃ n₀, ∀ n ≥ n₀, ∀ κ γ, …`), which makes the statement FALSE:
for `r = 2`, `D` odd, `𝓗 = K_{D+1} ⊔ K_{D+1}` on `n = 2(D+1)` vertices (every
degree exactly `D`), `𝓕` the two vertex sets, `γ = 1/2` and `κ` small, every
matching covers an *even* number of vertices of each clique while
`γ|S| = (D+1)/2` is odd, so `|S ∖ V(M)| ≥ 1` whereas the conclusion demands a
deviation `≤ 4κ|S| = 1/4`.  The paper's notation `0 < 1/n₀ ≪ 1/r, κ, γ < 1`
means `n₀ = n₀(r, κ, γ)`, which is the order used below.  (This statement is
*not* consumed by the final assembly, which takes `NibbleStatement` directly;
it is recorded here for the §8 layer.) -/
def SparseEGJStatement : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∀ κ γ : ℝ, 0 < κ → κ ≤ 1 → 0 < γ → γ ≤ 1 →
    ∃ n₀ : ℝ, 0 < n₀ ∧
    ∀ n : ℕ, n₀ ≤ (n : ℝ) →
    ∀ D : ℝ, (n : ℝ) ^ ((1 : ℝ) / 100) ≤ D →
    ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear → (∀ e ∈ 𝓗, edgeSize e = r) →
      (∀ v : Fin n, |((hypergraphDegree 𝓗 v : ℝ)) - D| ≤ κ * D) →
      ∀ 𝓕 : Set (Set (Fin n)), (𝓕.ncard : ℝ) ≤ (n : ℝ) ^ (2 * Real.log n) →
        ∃ M : Set 𝓗, IsMatching 𝓗 M ∧ ∀ S ∈ 𝓕, D ^ ((1 : ℝ) / 20) ≤ (S.ncard : ℝ) →
          |(((S \ matchVert M).ncard : ℝ) - γ * (S.ncard : ℝ))| ≤ 4 * κ * (S.ncard : ℝ)

end

end ErdosFaberLovaszConjecture
