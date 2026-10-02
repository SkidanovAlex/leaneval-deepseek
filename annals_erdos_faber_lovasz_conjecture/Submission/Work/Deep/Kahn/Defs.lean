import Submission.EFL.DeepInputs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.SetNotation

/-!
# Kahn's list-edge-colouring theorem: the vocabulary

This module fixes the vocabulary for the subproject `Work.Deep.Kahn`, whose
target is Kahn's theorem in the form used by the paper (Theorem 4.6 of
Kang--Kelly--Kühn--Methuku--Osthus, `ErdosFaberLovaszConjecture.KahnStatement`).

## Contents

* `Hypergraph.IsListColoring`, `Hypergraph.ListColorable` — proper edge
  colourings from a *list assignment* `L : 𝓗 → Finset α`;
* `Hypergraph.IsMatching` — a family of pairwise disjoint edges of `𝓗`
  (a colour class of a proper edge colouring);
* `Hypergraph.Coloring.ofColourClasses` — reassembling a colouring from
  matching colour classes plus a colouring of the leftover;
* `availableLists` — the list assignment attached to a family of *forbidden*
  lists `C e`: the available colours for `e` are `univ \ C e`;
* `KahnListStatement` — Kahn's theorem in list form;
* `KahnCoreStatement` — Kahn's theorem in list form, restricted to edges of
  size at least two (the genuinely hard part: the theorem for edges of size
  `0` or `1` follows by a greedy argument, `kahnList_of_kahnCore`).

## Conventions

* Colours of the list statements live in `Fin c` for a natural number `c`; this
  is the convention of `KahnStatement`.
* `D` is a *real* number, as in `KahnStatement`; `Δ(𝓗)` is compared with it
  through the coercion `((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) ≤ D`.
* Lists are `Finset`s, and their sizes are compared as reals (so that the
  statements are literally of the same shape as `KahnStatement`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {V : Type*} {α : Type*}

namespace Hypergraph

/-- A colouring `φ` of `𝓗` **respects** the list assignment `L` when every
edge receives a colour belonging to its own list. -/
def IsListColoring {𝓗 : Hypergraph V} (L : 𝓗 → Finset α) (φ : 𝓗.Coloring α) : Prop :=
  ∀ e : 𝓗, φ.labels e ∈ L e

/-- `𝓗` has a **proper edge colouring from the lists `L`**. -/
def ListColorable {𝓗 : Hypergraph V} (L : 𝓗 → Finset α) : Prop :=
  ∃ φ : 𝓗.Coloring α, IsListColoring L φ

/-- `M` is a **matching** in `𝓗`: a family of pairwise disjoint edges of `𝓗`.
These are precisely the colour classes of a proper edge colouring. -/
def IsMatching (𝓗 : Hypergraph V) (M : Set (Set V)) : Prop :=
  M ⊆ 𝓗 ∧ M.Pairwise fun e₁ e₂ => Disjoint e₁ e₂

/-- The hypergraph obtained from `𝓗` by deleting a family of edges. -/
def edgeDiff (𝓗 : Hypergraph V) (M : Set (Set V)) : Hypergraph V := 𝓗 \ M

/-- The label of the edge `e` in the colouring reassembled from the matching
colour classes `N i` (for the edges lying in one of them) and the leftover
colouring `χ` (for the other edges). -/
noncomputable def colourClassLabel {𝓗 : Hypergraph V} {ι : Type*} (N : ι → Set (Set V))
    (χ : (𝓗 \ ⋃ i, N i).Coloring α) (e : 𝓗) : ι ⊕ α := by
  classical
  exact if h : (e : Set V) ∈ ⋃ i, N i then
      Sum.inl (Classical.choose (Set.mem_iUnion.mp h))
    else Sum.inr (χ.labels ⟨(e : Set V), ⟨e.2, h⟩⟩)

lemma colourClassLabel_eq_inl {𝓗 : Hypergraph V} {ι : Type*} (N : ι → Set (Set V))
    (χ : (𝓗 \ ⋃ i, N i).Coloring α) {e : 𝓗} (h : (e : Set V) ∈ ⋃ i, N i) :
    colourClassLabel N χ e = Sum.inl (Classical.choose (Set.mem_iUnion.mp h)) := by
  classical
  rw [colourClassLabel, dif_pos h]

lemma colourClassLabel_eq_inr {𝓗 : Hypergraph V} {ι : Type*} (N : ι → Set (Set V))
    (χ : (𝓗 \ ⋃ i, N i).Coloring α) {e : 𝓗} (h : ¬ (e : Set V) ∈ ⋃ i, N i) :
    colourClassLabel N χ e = Sum.inr (χ.labels ⟨(e : Set V), ⟨e.2, h⟩⟩) := by
  classical
  rw [colourClassLabel, dif_neg h]

/-- Reassembling a proper edge colouring from matching colour classes `N i`
plus a colouring of the leftover `𝓗 \ ⋃ i, N i`.  The colour type is the sum
`ι ⊕ α`. -/
noncomputable def Coloring.ofColourClasses {𝓗 : Hypergraph V} {ι : Type*}
    (N : ι → Set (Set V))
    (_hdisj : ∀ i j, i ≠ j → Disjoint (N i) (N j))
    (hmat : ∀ i, (N i).Pairwise fun e₁ e₂ => Disjoint e₁ e₂)
    (χ : (𝓗 \ ⋃ i, N i).Coloring α) : 𝓗.Coloring (ι ⊕ α) where
  labels := colourClassLabel N χ
  isColoring e₁ e₂ he hnon := by
    classical
    by_cases h₁ : (e₁ : Set V) ∈ ⋃ i, N i
    · by_cases h₂ : (e₂ : Set V) ∈ ⋃ i, N i
      · rw [colourClassLabel_eq_inl N χ h₁, colourClassLabel_eq_inl N χ h₂]
        intro hcon
        have hij : Classical.choose (Set.mem_iUnion.mp h₁)
            = Classical.choose (Set.mem_iUnion.mp h₂) := Sum.inl_injective hcon
        have hm₁ : (e₁ : Set V) ∈ N (Classical.choose (Set.mem_iUnion.mp h₁)) :=
          Classical.choose_spec (Set.mem_iUnion.mp h₁)
        have hm₂ : (e₂ : Set V) ∈ N (Classical.choose (Set.mem_iUnion.mp h₂)) :=
          Classical.choose_spec (Set.mem_iUnion.mp h₂)
        have hm₁' : (e₁ : Set V) ∈ N (Classical.choose (Set.mem_iUnion.mp h₂)) :=
          hij ▸ hm₁
        have hd := hmat (Classical.choose (Set.mem_iUnion.mp h₂)) hm₁' hm₂
          (fun hEq => he (Subtype.ext hEq))
        exact hnon.ne_empty (Set.disjoint_iff_inter_eq_empty.mp hd)
      · rw [colourClassLabel_eq_inl N χ h₁, colourClassLabel_eq_inr N χ h₂]
        exact Sum.inl_ne_inr
    · by_cases h₂ : (e₂ : Set V) ∈ ⋃ i, N i
      · rw [colourClassLabel_eq_inr N χ h₁, colourClassLabel_eq_inl N χ h₂]
        exact Sum.inr_ne_inl
      · rw [colourClassLabel_eq_inr N χ h₁, colourClassLabel_eq_inr N χ h₂]
        intro hcon
        have hne : (e₁ : Set V) ≠ (e₂ : Set V) := fun hEq => he (Subtype.ext hEq)
        have hne' : (⟨(e₁ : Set V), ⟨e₁.2, h₁⟩⟩ : (𝓗 \ ⋃ i, N i : Set (Set V)))
            ≠ ⟨(e₂ : Set V), ⟨e₂.2, h₂⟩⟩ :=
          fun hEq =>
            hne (congrArg (fun x : (𝓗 \ ⋃ i, N i : Set (Set V)) => (x : Set V)) hEq)
        exact χ.isColoring ⟨(e₁ : Set V), ⟨e₁.2, h₁⟩⟩ ⟨(e₂ : Set V), ⟨e₂.2, h₂⟩⟩ hne'
          (by simpa using hnon) (Sum.inr_injective hcon)

end Hypergraph

/-- The list assignment of **available** colours attached to a family of
forbidden lists `C e` (in `KahnStatement` the set `C e` is the list of colours
that are forbidden for `e`). -/
def availableLists {n c : ℕ} {𝓗 : Hypergraph (Fin n)} (C : 𝓗 → Finset (Fin c)) :
    𝓗 → Finset (Fin c) :=
  fun e => (Finset.univ : Finset (Fin c)) \ C e

/-- Kahn's theorem in **list form**: every linear hypergraph on `Fin n` of
maximum degree at most `D` whose edges have size at most `r` admits a proper
edge colouring from any list assignment whose lists all have size at least
`(1+β)D`, the colour set having at least `(1+β)D` elements. -/
def KahnListStatement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ r : ℕ, 2 ≤ r → ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ D : ℝ, D₀ ≤ D → ∀ n : ℕ, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear →
      ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) ≤ D →
      (∀ e : 𝓗, (edgeSize (e : Set (Fin n)) : ℝ) ≤ (r : ℝ)) →
      ∀ c : ℕ, (1 + β) * D ≤ (c : ℝ) → ∀ L : 𝓗 → Finset (Fin c),
        (∀ e : 𝓗, (1 + β) * D ≤ ((L e).card : ℝ)) →
        𝓗.ListColorable L

/-- Kahn's theorem in list form for hypergraphs all of whose edges have size at
least two.  This is the core of the theorem: singleton edges (and the empty
edge) are dealt with by a greedy argument, see `kahnList_of_kahnCore`. -/
def KahnCoreStatement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ r : ℕ, 2 ≤ r → ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ D : ℝ, D₀ ≤ D → ∀ n : ℕ, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear →
      ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) ≤ D →
      (∀ e : 𝓗, 2 ≤ edgeSize (e : Set (Fin n))) →
      (∀ e : 𝓗, (edgeSize (e : Set (Fin n)) : ℝ) ≤ (r : ℝ)) →
      ∀ c : ℕ, (1 + β) * D ≤ (c : ℝ) → ∀ L : 𝓗 → Finset (Fin c),
        (∀ e : 𝓗, (1 + β) * D ≤ ((L e).card : ℝ)) →
        𝓗.ListColorable L

end

end ErdosFaberLovaszConjecture
