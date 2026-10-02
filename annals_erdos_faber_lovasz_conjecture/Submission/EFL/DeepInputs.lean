import Submission.EFL.Counting
import Submission.EFL.Basic
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Finset.Lattice.Basic

/-!
# The deep external inputs of the proof, and the degree of a hypergraph

The proof of the EFL conjecture rests on several deep theorems of the
literature (Vizing, Kahn, Lovász's `(g,f)`-factor theorem, Molloy–Reed,
Alon–Krivelevich–Sudakov, Ehard–Glock–Joos, Glock–Kühn–Osthus).  Where a
result is recorded here rather than proved, it is stated as a `Prop`-valued
*input statement* (following `MolloyReedStatement`/`AKSStatement` of
`LocallySparse.lean`), so that the surrounding combinatorial assembly can be
formalised and machine-checked *conditionally* on the deep input.

This module contains

* `hypergraphDegree`/`hypergraphMaxDegree` — the vertex degree `d_𝓗(v)` and
  the maximum degree `Δ(𝓗) = max_v d_𝓗(v)` of a hypergraph on `Fin n`,
  with monotonicity under taking subfamilies;
* `KahnStatement` — the paper's Theorem 4.6 (Kahn's theorem on list edge
  colourings of linear hypergraphs), and the plain (list-free) consequence
  `kahn_colorable`.
-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The degree `d_𝓗(v)` of a vertex `v` in the hypergraph `𝓗`: the number of
edges of `𝓗` containing `v`. -/
def hypergraphDegree (𝓗 : Hypergraph (Fin n)) (v : Fin n) : ℕ :=
  Nat.card {e : 𝓗 // v ∈ (e : Set (Fin n))}

/-- The maximum degree `Δ(𝓗) = max_v d_𝓗(v)`. -/
def hypergraphMaxDegree (𝓗 : Hypergraph (Fin n)) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup (fun v => hypergraphDegree 𝓗 v)

lemma hypergraphDegree_le_maxDegree (𝓗 : Hypergraph (Fin n)) (v : Fin n) :
    hypergraphDegree 𝓗 v ≤ hypergraphMaxDegree 𝓗 :=
  Finset.le_sup (Finset.mem_univ v)

/-- **Degree monotonicity**: subfamilies have no larger degrees. -/
lemma hypergraphDegree_mono {𝓖 𝓗 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗) (v : Fin n) :
    hypergraphDegree 𝓖 v ≤ hypergraphDegree 𝓗 v := by
  refine Nat.card_le_card_of_injective (fun e : {e : 𝓖 // v ∈ (e : Set (Fin n))} =>
    (⟨⟨(e.1 : Set (Fin n)), hsub e.1.2⟩, e.2⟩ :
      {e : 𝓗 // v ∈ (e : Set (Fin n))})) ?_
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : {e : 𝓗 // v ∈ (e : Set (Fin n))} => (x.1 : Set (Fin n))) hab

/-- **Maximum-degree monotonicity**: subfamilies have no larger maximum
degree. -/
lemma hypergraphMaxDegree_mono {𝓖 𝓗 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗) :
    hypergraphMaxDegree 𝓖 ≤ hypergraphMaxDegree 𝓗 := by
  classical
  show (Finset.univ : Finset (Fin n)).sup (fun v => hypergraphDegree 𝓖 v) ≤
      (Finset.univ : Finset (Fin n)).sup (fun v => hypergraphDegree 𝓗 v)
  exact Finset.sup_le (fun v _ =>
    (hypergraphDegree_mono hsub v).trans (Finset.le_sup (Finset.mem_univ v)))

/-- `v ∈ e` gives a bound on the degree: `d_𝓗(v) ≤ e(𝓗)`. -/
lemma hypergraphDegree_le_card (𝓗 : Hypergraph (Fin n)) (v : Fin n) :
    hypergraphDegree 𝓗 v ≤ Nat.card 𝓗 :=
  Nat.card_le_card_of_injective (fun e : {e : 𝓗 // v ∈ (e : Set (Fin n))} => e.1)
    (fun _a _b hab => Subtype.val_injective hab)

/-! ## Kahn's theorem (paper Theorem 4.6) as an input statement -/

/-- **Kahn's theorem** (paper Theorem 4.6, from Kahn's asymptotically
optimal list-edge-colouring theorem): for every `α > 0` and `r ≥ 2` there is
`D₀` such that a linear hypergraph `𝓗` with maximum degree at most `D ≥ D₀`
and every edge of size at most `r` has a proper edge-colouring from any
colour set `C` of size at least `(1+α)D` avoiding the lists `C(e)` of size at
most `αD/2`. -/
def KahnStatement : Prop :=
  ∀ α : ℝ, 0 < α → ∀ r : ℕ, 2 ≤ r → ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ D : ℝ, D₀ ≤ D → ∀ n : ℕ, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear →
      ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) ≤ D →
      (∀ e : 𝓗, (edgeSize (e : Set (Fin n)) : ℝ) ≤ (r : ℝ)) →
      ∀ c : ℕ, (1 + α) * D ≤ (c : ℝ) → ∀ C : 𝓗 → Finset (Fin c),
        (∀ e : 𝓗, ((C e).card : ℝ) ≤ α * D / 2) →
        ∃ φ : 𝓗.Coloring (Fin c), ∀ e : 𝓗, φ.labels e ∉ C e

/-- **Kahn's theorem, list-free form**: the colouring version used in the
paper's proof of Theorem 1.3 and Proposition 6.10 — a linear hypergraph with
`Δ(𝓗) ≤ D` and all edge sizes at most `r` is colourable with any `c` colours
satisfying `(1+α)D ≤ c`. -/
theorem kahn_colorable (hK : KahnStatement) {α : ℝ} (hα : 0 < α) {r : ℕ} (hr : 2 ≤ r) :
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ n : ℕ, ∀ 𝓗 : Hypergraph (Fin n),
      𝓗.IsLinear → ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) ≤ D →
      (∀ e : 𝓗, (edgeSize (e : Set (Fin n)) : ℝ) ≤ (r : ℝ)) →
      ∀ c : ℕ, (1 + α) * D ≤ (c : ℝ) → 𝓗.Colorable c := by
  obtain ⟨D₀, hD₀, h⟩ := hK α hα r hr
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD n 𝓗 hlin hdeg hsize c hc
  have hDpos : 0 < D := lt_of_lt_of_le hD₀ hD
  obtain ⟨φ, _⟩ := h D hD n 𝓗 hlin hdeg hsize c hc (fun _ => ∅)
    (by intro e; simp only [Finset.card_empty, Nat.cast_zero]; positivity)
  exact ⟨φ⟩

end

end ErdosFaberLovaszConjecture
