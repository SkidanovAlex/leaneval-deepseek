import Submission.Work.Deep.Kahn.Defs
import Submission.Work.Deep.Conc.Pi
import Submission.Work.ConeSwitch.MathlibNoHG

/-!
# The one-round semi-random step of Kahn's theorem: vocabulary

This module fixes the *procedure* of the semi-random (nibble) proof of Kahn's theorem on the
list-chromatic index of linear hypergraphs (Kang--Kelly--Kühn--Methuku--Osthus, Theorem 4.6,
`ErdosFaberLovaszConjecture.KahnStatement`; Kahn 1996).

Everything is phrased directly for hypergraphs:

* `Round.Coord K 𝓗 L e` — the coordinate space of the edge `e`: `K` activation classes
  together with an index into the list of `e`;
* `Round.Space K 𝓗 L` — an outcome of the round: every edge independently gets a uniform
  activation class and a uniform index into its list;
* `Round.active` (the edge meets activation class `0`), `Round.colour`, `Round.kept`,
  `Round.lost` (the colours of the activated edges meeting it) and `Round.residual`.

The combinatorial part of the one-round analysis is proved here: the kept edges are properly
coloured and the residual lists are *sound* (they avoid every colour used at a vertex of the
edge in this round).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

namespace Round

variable {n c : ℕ}

/-- The coordinate space of the edge `e` in one round: an activation class in `Fin K` and an
index into the list of `e`. -/
abbrev Coord (K : ℕ) (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (L : 𝓗 → Finset (Fin c)) (e : 𝓗) : Type := Fin K × Fin (L e).card

/-- A full outcome of one round. -/
abbrev Space (K : ℕ) (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (L : 𝓗 → Finset (Fin c)) : Type := ∀ e : 𝓗, Coord K 𝓗 L e

variable {K : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
  {L : 𝓗 → Finset (Fin c)}

/-- The *colour* assigned to the edge `e` by the outcome `ω`. -/
noncomputable def colour (ω : Space K 𝓗 L) (e : 𝓗) : Fin c :=
  ((Finset.equivFin (L e)).symm (ω e).2 : L e).1

lemma colour_mem (ω : Space K 𝓗 L) (e : 𝓗) : colour ω e ∈ L e :=
  ((Finset.equivFin (L e)).symm (ω e).2 : L e).2

/-- The edge `e` is *activated* in the outcome `ω`. -/
def active [NeZero K] (ω : Space K 𝓗 L) (e : 𝓗) : Prop := (ω e).1 = 0

/-- The edge `e` *keeps* its colour: it is activated and no *other* activated edge meeting it
carries the same colour. -/
def kept [NeZero K] (ω : Space K 𝓗 L) (e : 𝓗) : Prop :=
  active ω e ∧ ∀ g : 𝓗, g ≠ e → ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty →
    active ω g → colour ω g ≠ colour ω e

lemma kept_iff [NeZero K] (ω : Space K 𝓗 L) (e : 𝓗) :
    kept ω e ↔ active ω e ∧ ∀ g : 𝓗, g ≠ e →
      ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty → active ω g →
        colour ω g ≠ colour ω e := Iff.rfl

lemma kept_active [NeZero K] {ω : Space K 𝓗 L} {e : 𝓗} (h : kept ω e) : active ω e := h.1

/-- The set of edges kept in the round, as a subhypergraph. -/
def keptSub [NeZero K] (ω : Space K 𝓗 L) :
    ErdosFaberLovaszConjecture.Hypergraph (Fin n) :=
  {e | ∃ he : e ∈ 𝓗, kept ω ⟨e, he⟩}

lemma mem_keptSub [NeZero K] {ω : Space K 𝓗 L} {e : Set (Fin n)} :
    e ∈ keptSub ω ↔ ∃ he : e ∈ 𝓗, kept ω ⟨e, he⟩ := Iff.rfl

lemma keptSub_subset [NeZero K] (ω : Space K 𝓗 L) : keptSub ω ⊆ 𝓗 :=
  fun _e he => (mem_keptSub.mp he).choose

/-- The colouring of the kept edges induced by the round. -/
noncomputable def keptColoring [NeZero K] (ω : Space K 𝓗 L) : (keptSub ω).Coloring (Fin c) :=
  { labels := fun e => colour ω ⟨(e : Set (Fin n)), e.2.choose⟩
    isColoring := by
      intro e₁ e₂ hne hnon hc
      obtain ⟨v, hv₁, hv₂⟩ := hnon
      set i₁ : 𝓗 := ⟨(e₁ : Set (Fin n)), e₁.2.choose⟩ with hi₁
      set i₂ : 𝓗 := ⟨(e₂ : Set (Fin n)), e₂.2.choose⟩ with hi₂
      have hk₁ : kept ω i₁ := e₁.2.choose_spec
      have hk₂ : kept ω i₂ := e₂.2.choose_spec
      have hne' : i₂ ≠ i₁ := by
        intro hEq
        exact hne (Subtype.ext (by simpa [hi₁, hi₂] using (congrArg Subtype.val hEq).symm))
      have hint : ((i₂ : Set (Fin n)) ∩ (i₁ : Set (Fin n))).Nonempty := by
        refine ⟨v, ?_, ?_⟩
        · simpa [hi₂] using hv₂
        · simpa [hi₁] using hv₁
      exact hk₁.2 i₂ hne' hint hk₂.1 hc.symm }

/-- The colours lost by the edge `e` in the round: the colours of activated edges meeting it. -/
noncomputable def lost [NeZero K] (ω : Space K 𝓗 L) (e : 𝓗) : Finset (Fin c) := by
  classical
  exact (L e).filter fun γ => ∃ g : 𝓗, active ω g ∧ colour ω g = γ ∧
    ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty

lemma mem_lost [NeZero K] {ω : Space K 𝓗 L} {e : 𝓗} {γ : Fin c} :
    γ ∈ lost ω e ↔ γ ∈ L e ∧ ∃ g : 𝓗, active ω g ∧ colour ω g = γ ∧
      ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty := by
  classical
  simp only [lost, Finset.mem_filter]

/-- The residual list of the edge `e` after the round. -/
noncomputable def residual [NeZero K] (ω : Space K 𝓗 L) (e : 𝓗) : Finset (Fin c) :=
  L e \ lost ω e

lemma residual_subset [NeZero K] (ω : Space K 𝓗 L) (e : 𝓗) : residual ω e ⊆ L e :=
  Finset.sdiff_subset

lemma mem_residual [NeZero K] {ω : Space K 𝓗 L} {e : 𝓗} {γ : Fin c} :
    γ ∈ residual ω e ↔ γ ∈ L e ∧ ∀ g : 𝓗, active ω g → colour ω g = γ →
      ¬ ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty := by
  classical
  rw [residual, Finset.mem_sdiff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun g hg hc hint => h2 ?_⟩
    rw [mem_lost]
    exact ⟨h1, g, hg, hc, hint⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [mem_lost]
    rintro ⟨-, g, hg, hc, hint⟩
    exact h2 g hg hc hint

/-- **Soundness of the residual lists.**  A colour used by a kept edge at a vertex of an
uncoloured edge `e` is no longer available for `e`. -/
theorem not_mem_residual_of_kept [NeZero K] {ω : Space K 𝓗 L} {e g : 𝓗} {v : Fin n}
    {γ : Fin c} (hg : kept ω g) (hv : v ∈ (g : Set (Fin n)))
    (hve : v ∈ (e : Set (Fin n))) (hγ : colour ω g = γ) : γ ∉ residual ω e := by
  intro h
  obtain ⟨-, h2⟩ := mem_residual.mp h
  exact h2 g hg.1 hγ ⟨v, hv, hve⟩

/-- A kept edge is coloured with a colour of its own list. -/
theorem keptColoring_mem [NeZero K] (ω : Space K 𝓗 L) (e : keptSub ω) :
    (keptColoring ω).labels e ∈ L ⟨(e : Set (Fin n)), e.2.choose⟩ :=
  colour_mem ω _

end Round

end Work.Deep.Kahn
