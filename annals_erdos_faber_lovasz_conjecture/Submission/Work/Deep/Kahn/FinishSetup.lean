import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.Defs
import Submission.Work.Deep.Prob.Spaces

/-!
# The finishing step of Kahn's theorem: setup

This module fixes the vocabulary of the *finishing step* of Kahn's list
colouring theorem (`Work.Deep.Kahn.finishing_step`): a linear-ish hypergraph
whose edges have size at most `r`, whose *colour degrees*
`D_x(γ) = #{e ∋ x : γ ∈ L e}` are at most `D`, and whose lists all have size
at least `8 r D` is list-colourable.

The proof is the Lovász local lemma applied to the *pair events*

`A_{ef} = {φ : φ` gives the edges `e` and `f` the same colour`}`,

one for each unordered pair `{e, f}` of distinct edges that meet, together with
the product measure on the space `ListSpace L` of all choices of a colour from
each list.  This module contains the definitions; the probability estimates are
in `Submission/Work/Deep/Kahn/listProb_facts` and the counting estimates in
`Submission/Work/Deep/Kahn/pair_ratio_bounds`.

## Contents

* `ListSpace L` — the space of list-respecting colourings, a finite product of
  the lists: `(e : E) → {γ : Fin c // γ ∈ L e}`;
* `listProb L hL` — the uniform probability measure on it;
* `edgeRank` — an arbitrary injective ranking of the edges, used to pick a
  canonical order inside an unordered pair;
* `canonPair`, `canonIdx` — the canonical ordered pair of two distinct meeting
  edges;
* `BadIdx 𝓗` — the index type of the bad events: canonically ordered pairs of
  distinct meeting edges;
* `badEvent L i` — the event that both edges of `i` receive the same colour;
* `badWeight L i` — the probability `ℙ[badEvent L i]`
  `= |L e ∩ L f| / (|L e| |L f|)`;
* `badX L i = 2 * badWeight L i` — the LLL witness;
* `Dep 𝓗 i` — the neighbours of `i`: all indices sharing one of the two edges,
  realised as the union of the two images `g ↦ {e, g}` and `g ↦ {f, g}`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

/-! ## The sample space -/

/-- The space of colourings of a finite set of edges `E` by colours drawn from
their own lists. -/
abbrev ListSpace {E : Type*} [Fintype E] {c : ℕ} (L : E → Finset (Fin c)) :=
  (e : E) → {γ : Fin c // γ ∈ L e}

/-- The uniform probability measure on the list space. -/
noncomputable def listProb {E : Type*} [Fintype E] [DecidableEq E] {c : ℕ}
    (L : E → Finset (Fin c)) (hL : ∀ e, (L e).Nonempty) :
    Work.Deep.Prob.FinProbSpace (ListSpace L) := by
  haveI : Nonempty (ListSpace L) := ⟨fun e => ⟨(hL e).choose, (hL e).choose_spec⟩⟩
  exact Work.Deep.Prob.FinProbSpace.uniform (ListSpace L)

/-! ## The bad events -/

variable {n c : ℕ}

/-- An injective ranking of the edges of a finite hypergraph. -/
noncomputable def edgeRank (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗] : 𝓗 → ℕ :=
  fun e => (Fintype.equivFin 𝓗 e : ℕ)

lemma edgeRank_injective (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗] :
    Function.Injective (edgeRank 𝓗) := by
  intro a b h
  exact (Fintype.equivFin 𝓗).injective (Fin.ext h)

/-- The canonical ordering of the unordered pair `{g, h}`: the smaller rank first. -/
noncomputable def canonPair (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗] (g h : 𝓗) : 𝓗 × 𝓗 :=
  if edgeRank 𝓗 g < edgeRank 𝓗 h then (g, h) else (h, g)

lemma canonPair_eq_or (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗] (g h : 𝓗) :
    canonPair 𝓗 g h = (g, h) ∨ canonPair 𝓗 g h = (h, g) := by
  rw [canonPair]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma canonPair_comm (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗] {g h : 𝓗} (hgh : g ≠ h) :
    canonPair 𝓗 g h = canonPair 𝓗 h g := by
  have hne : edgeRank 𝓗 g ≠ edgeRank 𝓗 h := fun hh => hgh (edgeRank_injective 𝓗 hh)
  rw [canonPair, canonPair]
  by_cases h1 : edgeRank 𝓗 g < edgeRank 𝓗 h
  · rw [if_pos h1, if_neg (not_lt.mpr h1.le)]
  · have h2 : edgeRank 𝓗 h < edgeRank 𝓗 g := lt_of_le_of_ne (le_of_not_gt h1) (Ne.symm hne)
    rw [if_neg h1, if_pos h2]

lemma canonPair_lt (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗] {g h : 𝓗} (hgh : g ≠ h) :
    edgeRank 𝓗 (canonPair 𝓗 g h).1 < edgeRank 𝓗 (canonPair 𝓗 g h).2 := by
  have hne : edgeRank 𝓗 g ≠ edgeRank 𝓗 h := fun hh => hgh (edgeRank_injective 𝓗 hh)
  rw [canonPair]
  by_cases h1 : edgeRank 𝓗 g < edgeRank 𝓗 h
  · rw [if_pos h1]; exact h1
  · have h2 : edgeRank 𝓗 h < edgeRank 𝓗 g := lt_of_le_of_ne (le_of_not_gt h1) (Ne.symm hne)
    rw [if_neg h1]; exact h2

/-- Membership in the `verts`-intersection of two edges is membership in their intersection. -/
lemma verts_inter_nonempty_iff {n : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    [Fintype 𝓗] (e f : 𝓗) :
    (verts (e : Set (Fin n)) ∩ verts (f : Set (Fin n))).Nonempty ↔
      ((e : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    rw [Finset.mem_inter] at hx
    exact ⟨x, (mem_verts _ x).mp hx.1, (mem_verts _ x).mp hx.2⟩
  · rintro ⟨x, hx1, hx2⟩
    exact ⟨x, Finset.mem_inter.mpr ⟨(mem_verts _ x).mpr hx1, (mem_verts _ x).mpr hx2⟩⟩

/-- The index type of the bad events: canonically ordered pairs of distinct
meeting edges. -/
noncomputable def BadIdx (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗] : Type :=
  {p : 𝓗 × 𝓗 // p.1 ≠ p.2 ∧
    (verts (p.1 : Set (Fin n)) ∩ verts (p.2 : Set (Fin n))).Nonempty ∧
    edgeRank 𝓗 p.1 < edgeRank 𝓗 p.2}

instance (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗] : Fintype (BadIdx 𝓗) := by
  unfold BadIdx
  infer_instance

instance (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗] : DecidableEq (BadIdx 𝓗) := by
  unfold BadIdx
  infer_instance

/-- The index attached to the unordered pair `{g, h}` of distinct meeting edges. -/
noncomputable def canonIdx (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗] (g h : 𝓗) (hgh : g ≠ h)
    (hint : (verts (g : Set (Fin n)) ∩ verts (h : Set (Fin n))).Nonempty) : BadIdx 𝓗 := by
  refine ⟨canonPair 𝓗 g h, ?_, ?_, canonPair_lt 𝓗 hgh⟩
  · rcases canonPair_eq_or 𝓗 g h with heq | heq <;> rw [heq]
    · exact hgh
    · exact fun hcon => hgh hcon.symm
  · rcases canonPair_eq_or 𝓗 g h with heq | heq <;> rw [heq]
    · exact hint
    · rwa [Finset.inter_comm]

lemma canonIdx_val (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗] {g h : 𝓗} (hgh : g ≠ h)
    (hint : (verts (g : Set (Fin n)) ∩ verts (h : Set (Fin n))).Nonempty) :
    (canonIdx 𝓗 g h hgh hint).1 = (g, h) ∨ (canonIdx 𝓗 g h hgh hint).1 = (h, g) :=
  canonPair_eq_or 𝓗 g h

lemma canonIdx_comm (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗] {g h : 𝓗} (hgh : g ≠ h)
    (hint : (verts (g : Set (Fin n)) ∩ verts (h : Set (Fin n))).Nonempty)
    (hint' : (verts (h : Set (Fin n)) ∩ verts (g : Set (Fin n))).Nonempty) :
    canonIdx 𝓗 g h hgh hint = canonIdx 𝓗 h g hgh.symm hint' :=
  Subtype.ext (canonPair_comm 𝓗 hgh)

/-- The bad event attached to an index: both edges receive the same colour. -/
def badEvent {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗] (L : 𝓗 → Finset (Fin c))
    (i : BadIdx 𝓗) : Set (ListSpace L) :=
  {φ | (φ i.1.1).val = (φ i.1.2).val}

/-- The weight of an index: the probability that both its edges receive the
same colour. -/
noncomputable def badWeight {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗] (L : 𝓗 → Finset (Fin c))
    (i : BadIdx 𝓗) : ℝ :=
  ((L i.1.1 ∩ L i.1.2).card : ℝ) / (((L i.1.1).card : ℝ) * ((L i.1.2).card : ℝ))

/-- The LLL witness attached to an index. -/
noncomputable def badX {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗] (L : 𝓗 → Finset (Fin c))
    (i : BadIdx 𝓗) : ℝ := 2 * badWeight L i

lemma badWeight_nonneg {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗] (L : 𝓗 → Finset (Fin c))
    (i : BadIdx 𝓗) : 0 ≤ badWeight L i := by
  unfold badWeight
  positivity

lemma badWeight_congr {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗] {L : 𝓗 → Finset (Fin c)}
    {i j : BadIdx 𝓗} (h1 : i.1.1 = j.1.1) (h2 : i.1.2 = j.1.2) :
    badWeight L i = badWeight L j := by
  unfold badWeight
  rw [h1, h2]

lemma badWeight_of_val {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
    {L : 𝓗 → Finset (Fin c)} {i : BadIdx 𝓗} {g h : 𝓗}
    (hval : i.1 = (g, h) ∨ i.1 = (h, g)) :
    badWeight L i
      = ((L g ∩ L h).card : ℝ) / (((L g).card : ℝ) * ((L h).card : ℝ)) := by
  rcases hval with hv | hv
  · unfold badWeight
    rw [hv]
  · unfold badWeight
    rw [hv, Finset.inter_comm, mul_comm]

lemma badWeight_canonIdx {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
    (L : 𝓗 → Finset (Fin c)) {g h : 𝓗} (hgh : g ≠ h)
    (hint : (verts (g : Set (Fin n)) ∩ verts (h : Set (Fin n))).Nonempty) :
    badWeight L (canonIdx 𝓗 g h hgh hint)
      = ((L g ∩ L h).card : ℝ) / (((L g).card : ℝ) * ((L h).card : ℝ)) :=
  badWeight_of_val (canonIdx_val 𝓗 hgh hint)

lemma badX_eq {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗] (L : 𝓗 → Finset (Fin c))
    (i : BadIdx 𝓗) : badX L i = 2 * badWeight L i := rfl

/-! ## The neighbourhood structure -/

/-- The neighbours of an index: all indices sharing one of its edges.  It is
the union of the two families `g ↦ {e, g}` (for `g` an edge meeting `e`) and
`g ↦ {f, g}`. -/
noncomputable def Dep (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗]
    (i : BadIdx 𝓗) : Finset (BadIdx 𝓗) := by
  classical
  exact (Finset.univ : Finset (BadIdx 𝓗)).filter (fun j => j ≠ i ∧
    (j.1.1 ∈ ({i.1.1, i.1.2} : Finset 𝓗) ∨ j.1.2 ∈ ({i.1.1, i.1.2} : Finset 𝓗)))

lemma mem_Dep_iff {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
    {i j : BadIdx 𝓗} :
    j ∈ Dep 𝓗 i ↔ j ≠ i ∧
      (j.1.1 ∈ ({i.1.1, i.1.2} : Finset 𝓗) ∨ j.1.2 ∈ ({i.1.1, i.1.2} : Finset 𝓗)) := by
  classical
  unfold Dep
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end

end Work.Deep.Kahn
