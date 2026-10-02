import Submission.EFL.Basic
import Submission.EFL.Reformulation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FinCases

/-!
# Reduction to hypergraphs without singleton/empty edges

The proof of the Erdős–Faber–Lovász conjecture in the paper begins by removing
the "small" edges (those with at most one vertex) from a linear hypergraph:
if every *large* edge (with at least two vertices) of a linear hypergraph
`𝓗` on `n` vertices can be coloured with `n` colours, then so can all of `𝓗`.
Indeed every vertex lies in at most `n - 1` large edges, and all large edges
through a fixed vertex intersect pairwise, hence use pairwise different colours,
so for every vertex there is at least one colour not used by any large edge
through it; assign such a colour to the singleton edge.

This file formalises that reduction, together with the elementary counting
facts about linear hypergraphs that it needs:

* two distinct edges of a linear hypergraph share at most one vertex
  (`IsLinear.eq_of_mem_intersection`);
* if two vertices lie in a common edge, that edge is unique
  (`IsLinear.eq_of_mem_pair`);
* the large edges through a fixed vertex can be injected into the other
  vertices (`BigEdgesCounting.card_edgesThroughBig_le`), so there are at most
  `n - 1` of them;
* a colouring of the large edges extends to all edges
  (`colorable_of_colorable_bigEdges`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace ErdosFaberLovaszConjecture

variable {V : Type*}

/-- An edge `e` of a hypergraph has *two (distinct) vertices*. -/
def HasTwoVertices (e : Set V) : Prop :=
  ∃ x : V, ∃ y : V, x ∈ e ∧ y ∈ e ∧ x ≠ y

/-- An edge with at most one vertex: the complement of `HasTwoVertices`. -/
def AtMostOneVertex (e : Set V) : Prop :=
  ¬ HasTwoVertices e

/-- The sub-hypergraph of a hypergraph consisting of its edges of size at least two. -/
def Hypergraph.bigEdges (𝓗 : Hypergraph V) : Hypergraph V :=
  {e : Set V | e ∈ 𝓗 ∧ HasTwoVertices e}

/-- `bigEdges` is a sub-hypergraph. -/
theorem bigEdges_subset (𝓗 : Hypergraph V) : 𝓗.bigEdges ⊆ 𝓗 := by
  intro e he
  exact he.1

/-- The big-edge sub-hypergraph of a linear hypergraph is linear. -/
theorem IsLinear.bigEdges {𝓗 : Hypergraph V} (hlin : 𝓗.IsLinear) : (𝓗.bigEdges).IsLinear := by
  exact hlin.mono (bigEdges_subset 𝓗)

/-- Every edge of `bigEdges` has two distinct vertices. -/
theorem bigEdges_mem_hasTwoVertices {𝓗 : Hypergraph V} {e : Set V} (he : e ∈ 𝓗.bigEdges) :
    HasTwoVertices e := he.2

/-- An edge with at most one vertex is "subsingleton" as a set: any two elements are equal. -/
theorem AtMostOneVertex.eq_of_mem {e : Set V} (hsmall : AtMostOneVertex e) {x y : V}
    (hx : x ∈ e) (hy : y ∈ e) : x = y := by
  by_contra hxy
  exact hsmall ⟨x, y, hx, hy, hxy⟩

/-- If an edge has two distinct vertices, then for every `v` it contains some `x ≠ v`. -/
theorem HasTwoVertices.exists_ne {e : Set V} (he : HasTwoVertices e) (v : V) :
    ∃ x : V, x ∈ e ∧ x ≠ v := by
  rcases he with ⟨x, y, hx, hy, hxy⟩
  by_cases hxv : x = v
  · refine ⟨y, hy, ?_⟩
    intro hyv
    exact hxy (by rw [hxv, hyv])
  · exact ⟨x, hx, hxv⟩

/-- In a linear hypergraph, two distinct edges sharing two vertices force those vertices to
coincide; equivalently any two elements of the intersection of two distinct edges agree. -/
theorem IsLinear.eq_of_mem_intersection {𝓗 : Hypergraph V} (hlin : 𝓗.IsLinear)
    {e₁ e₂ : Set V} (he₁ : e₁ ∈ 𝓗) (he₂ : e₂ ∈ 𝓗) (hne : e₁ ≠ e₂) {x y : V}
    (hx₁ : x ∈ e₁) (hx₂ : x ∈ e₂) (hy₁ : y ∈ e₁) (hy₂ : y ∈ e₂) : x = y := by
  have hsub : (e₁ ∩ e₂ : Set V).Subsingleton := hlin he₁ he₂ hne
  exact hsub ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩

/-- If two distinct vertices lie in a common edge of a linear hypergraph, that edge is unique. -/
theorem IsLinear.eq_of_mem_pair {𝓗 : Hypergraph V} (hlin : 𝓗.IsLinear)
    {e₁ e₂ : Set V} (he₁ : e₁ ∈ 𝓗) (he₂ : e₂ ∈ 𝓗) {x y : V} (hxy : x ≠ y)
    (hx₁ : x ∈ e₁) (hy₁ : y ∈ e₁) (hx₂ : x ∈ e₂) (hy₂ : y ∈ e₂) : e₁ = e₂ := by
  by_contra hne
  exact hxy (IsLinear.eq_of_mem_intersection hlin he₁ he₂ hne hx₁ hx₂ hy₁ hy₂)

namespace BigEdgesCounting

variable {n : ℕ} {𝓗 : Hypergraph (Fin n)} {v : Fin n}

/-- The large edges of `𝓗 : Hypergraph (Fin n)` containing a vertex `v`. -/
abbrev edgesThroughBig (n : ℕ) (𝓗 : Hypergraph (Fin n)) (v : Fin n) :=
  {e : 𝓗.bigEdges // v ∈ (e : Set (Fin n))}

/-- Choosing an element of a large edge `e` containing `v` different from `v`. -/
noncomputable def otherVertex (e : edgesThroughBig n 𝓗 v) : Fin n :=
  Classical.choose (HasTwoVertices.exists_ne (bigEdges_mem_hasTwoVertices e.1.2) v)

theorem otherVertex_mem (e : edgesThroughBig n 𝓗 v) : otherVertex e ∈ (e : Set (Fin n)) :=
  (Classical.choose_spec (HasTwoVertices.exists_ne (bigEdges_mem_hasTwoVertices e.1.2) v)).1

theorem otherVertex_ne (e : edgesThroughBig n 𝓗 v) : otherVertex e ≠ v :=
  (Classical.choose_spec (HasTwoVertices.exists_ne (bigEdges_mem_hasTwoVertices e.1.2) v)).2

/-- The map `e ↦ otherVertex e` is injective on the large edges through `v` when the
hypergraph is linear (two such edges can only meet at `v`). -/
theorem otherVertex_injective (hlin : 𝓗.IsLinear) :
    Function.Injective (otherVertex (n := n) (𝓗 := 𝓗) (v := v)) := by
  intro e₁ e₂ hEq
  by_contra hne
  have hv₁ : v ∈ (e₁ : Set (Fin n)) := e₁.2
  have hv₂ : v ∈ (e₂ : Set (Fin n)) := e₂.2
  have hw₁ : otherVertex e₁ ∈ (e₁ : Set (Fin n)) := otherVertex_mem e₁
  have hw₂' : otherVertex e₂ ∈ (e₂ : Set (Fin n)) := otherVertex_mem e₂
  have hw₂ : otherVertex e₁ ∈ (e₂ : Set (Fin n)) := by
    simpa [hEq] using hw₂'
  have hne_v : (e₁.1 : Set (Fin n)) ≠ (e₂.1 : Set (Fin n)) := by
    intro hEqv
    apply hne
    apply Subtype.ext
    apply Subtype.ext
    exact hEqv
  have hsub : (𝓗.bigEdges).IsLinear := IsLinear.bigEdges hlin
  have hv_eq : v = otherVertex e₁ := by
    apply IsLinear.eq_of_mem_intersection hsub e₁.1.2 e₂.1.2 hne_v hv₁ hv₂ hw₁ hw₂
  exact (otherVertex_ne e₁) hv_eq.symm

/-- The map `e ↦ otherVertex e`, viewed as landing in the vertices other than `v`. -/
noncomputable def otherVertexEmb (e : edgesThroughBig n 𝓗 v) : {w : Fin n // w ≠ v} :=
  ⟨otherVertex e, otherVertex_ne e⟩

theorem otherVertexEmb_injective (hlin : 𝓗.IsLinear) :
    Function.Injective (otherVertexEmb (n := n) (𝓗 := 𝓗) (v := v)) := by
  intro e₁ e₂ hEq
  exact otherVertex_injective hlin (by
    simpa [otherVertexEmb] using congrArg (fun x : {w : Fin n // w ≠ v} => x.1) hEq)

/-- In a linear hypergraph on `Fin n`, at most `n - 1` large edges contain a given vertex. -/
theorem card_edgesThroughBig_le (n : ℕ) (𝓗 : Hypergraph (Fin n)) (hlin : 𝓗.IsLinear)
    (v : Fin n) : Nat.card (edgesThroughBig n 𝓗 v) ≤ n - 1 := by
  classical
  let A := edgesThroughBig n 𝓗 v
  let B := {w : Fin n // w ≠ v}
  have hAB : Nat.card A ≤ Nat.card B := by
    haveI : Finite B := inferInstance
    exact Nat.card_le_card_of_injective (α := A) (β := B)
      (fun e : A => otherVertexEmb (n := n) (𝓗 := 𝓗) (v := v) e)
      (otherVertexEmb_injective (n := n) (𝓗 := 𝓗) (v := v) hlin)
  have hB : Nat.card B = n - 1 := by
    letI : Fintype B := Fintype.ofFinite B
    rw [Nat.card_eq_fintype_card]
    -- equivalence Fin n ≃ B ⊕ PUnit
    let e : Fin n ≃ B ⊕ Fin 1 := {
      toFun := fun x => if hx : x ≠ v then Sum.inl ⟨x, hx⟩ else Sum.inr 0
      invFun := fun s => Sum.elim (fun b : B => b.1) (fun _ : Fin 1 => v) s
      left_inv := by
        intro x
        by_cases hx : x ≠ v
        · simp [hx]
        · have hxv : x = v := by by_contra h; exact hx h
          dsimp
          rw [dif_neg hx]
          simp [hxv]
      right_inv := by
        intro s
        cases s with
        | inl b =>
            cases b with
            | mk b1 hb =>
                dsimp
                rw [dif_pos hb]
        | inr u =>
            fin_cases u
            dsimp
            simp
    }
    have hsum : Fintype.card B + 1 = n := by
      calc
        Fintype.card B + 1 = Fintype.card B + Fintype.card (Fin 1) := by simp
        _ = Fintype.card (B ⊕ Fin 1) := (Fintype.card_sum (α := B) (β := Fin 1)).symm
        _ = Fintype.card (Fin n) := (Fintype.card_congr e).symm
        _ = n := by simp
    rw [← hsum]
    exact (Nat.add_sub_cancel (Fintype.card B) 1).symm
  exact hAB.trans (le_of_eq hB)

end BigEdgesCounting

/-- Pigeonhole: an injective family `g : ι → Fin n` with `card ι ≤ n - 1` misses a colour. -/
theorem exists_color_unused_of_card_lt {n : ℕ} (hn : 1 ≤ n) {ι : Type*} [Fintype ι]
    (g : ι → Fin n) (hinj : Function.Injective g) (hcard : Fintype.card ι ≤ n - 1) :
    ∃ c : Fin n, ∀ i : ι, g i ≠ c := by
  classical
  let s : Finset (Fin n) := Finset.univ.image g
  have hs : s.card < Fintype.card (Fin n) := by
    calc
      s.card = (Finset.univ : Finset ι).card := by
        exact Finset.card_image_of_injective (s := Finset.univ) (f := g) hinj
      _ = Fintype.card ι := by simp
      _ ≤ n - 1 := hcard
      _ < n := by omega
      _ = Fintype.card (Fin n) := by simp
  have hmiss : ∃ c : Fin n, c ∉ s := by
    by_contra hx
    push Not at hx
    have huniv : (Finset.univ : Finset (Fin n)) ⊆ s := by
      intro x hx'
      exact hx x
    have hcard' : Fintype.card (Fin n) ≤ s.card := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card huniv
    exact not_lt_of_ge hcard' hs
  rcases hmiss with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro i hi
  exact hc (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)

/-- In a linear hypergraph, at every vertex `v` there is a colour not used by any large edge
through `v` (there are at most `n - 1` of those, all with distinct colours). -/
theorem exists_color_unused_at {n : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (C₂ : (𝓗.bigEdges).Coloring (Fin n)) (v : Fin n) :
    ∃ c : Fin n, ∀ e : BigEdgesCounting.edgesThroughBig n 𝓗 v,
      C₂.labels (e : 𝓗.bigEdges) ≠ c := by
  classical
  have hn : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst n
    exact Fin.elim0 v
  let A := BigEdgesCounting.edgesThroughBig n 𝓗 v
  haveI : Fintype A := Fintype.ofFinite A
  have hInj : Function.Injective (fun e : A => C₂.labels (e : 𝓗.bigEdges)) := by
    intro e₁ e₂ hEq
    by_contra hne
    have hne' : (e₁ : 𝓗.bigEdges) ≠ (e₂ : 𝓗.bigEdges) := by
      intro hEqv
      exact hne (Subtype.ext hEqv)
    have hcol := C₂.isColoring (e₁ : 𝓗.bigEdges) (e₂ : 𝓗.bigEdges) hne' ⟨v, e₁.2, e₂.2⟩
    exact hcol (by simpa using hEq)
  have hcardNat : Nat.card A ≤ n - 1 := by
    simpa [A] using BigEdgesCounting.card_edgesThroughBig_le n 𝓗 hlin v
  have hcard : Fintype.card A ≤ n - 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardNat
  rcases exists_color_unused_of_card_lt (n := n) hn (fun e : A => C₂.labels (e : 𝓗.bigEdges)) hInj hcard with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro e
  exact hc e

/-- Colour of a small edge: an unused colour at its (canonical) vertex, or `0` if the
edge is empty (an empty edge never intersects anything, so its colour is irrelevant). -/
noncomputable def smallColor {n : ℕ} {𝓗 : Hypergraph (Fin n)} (hn : 1 ≤ n)
    (hlin : 𝓗.IsLinear) (C₂ : (𝓗.bigEdges).Coloring (Fin n)) (e : 𝓗) : Fin n := by
  classical
  exact
    if hne : (e : Set (Fin n)).Nonempty then
      let v : Fin n := Classical.choose hne
      Classical.choose (exists_color_unused_at hlin C₂ v)
    else
      ⟨0, by omega⟩

/-- The colouring of all of `𝓗` extending `C₂`: large edges keep their colour, small ones
are coloured as in `smallColor`. -/
noncomputable def extCol {n : ℕ} {𝓗 : Hypergraph (Fin n)} (hn : 1 ≤ n) (hlin : 𝓗.IsLinear)
    (C₂ : (𝓗.bigEdges).Coloring (Fin n)) (e : 𝓗) : Fin n := by
  classical
  exact
    if hbig : HasTwoVertices (e : Set (Fin n)) then
      C₂.labels ⟨(e : Set (Fin n)), ⟨e.2, hbig⟩⟩
    else
      smallColor hn hlin C₂ e

/-- If `e₁` is large, `e₂` small and they intersect, then `extCol` gives them different
colours. -/
lemma extCol_ne_big_small {n : ℕ} {𝓗 : Hypergraph (Fin n)} (hn : 1 ≤ n) (hlin : 𝓗.IsLinear)
    (C₂ : (𝓗.bigEdges).Coloring (Fin n)) {e₁ e₂ : 𝓗} (h₁ : HasTwoVertices (e₁ : Set (Fin n)))
    (h₂ : ¬ HasTwoVertices (e₂ : Set (Fin n))) (hnon : ((e₁ : Set (Fin n)) ∩ (e₂ : Set (Fin n))).Nonempty) :
    extCol hn hlin C₂ e₁ ≠ extCol hn hlin C₂ e₂ := by
  classical
  rcases hnon with ⟨x, hx₁, hx₂⟩
  by_cases he₂ : (e₂ : Set (Fin n)).Nonempty
  · let v : Fin n := Classical.choose he₂
    have hvm : v ∈ (e₂ : Set (Fin n)) := Classical.choose_spec he₂
    have hxv : x = v := AtMostOneVertex.eq_of_mem h₂ hx₂ hvm
    have hve₁ : v ∈ (e₁ : Set (Fin n)) := by simpa [hxv] using hx₁
    let e₁big : BigEdgesCounting.edgesThroughBig n 𝓗 v := ⟨⟨(e₁ : Set (Fin n)), ⟨e₁.2, h₁⟩⟩, hve₁⟩
    have hused : C₂.labels (e₁big : 𝓗.bigEdges) ≠
        Classical.choose (exists_color_unused_at hlin C₂ v) :=
      Classical.choose_spec (exists_color_unused_at hlin C₂ v) e₁big
    dsimp [extCol, smallColor]
    rw [dif_pos h₁, dif_neg h₂, dif_pos he₂]
    simpa [v] using hused
  · exfalso
    exact he₂ ⟨x, hx₂⟩

/-- `extCol` is a proper colouring of `𝓗`. -/
lemma extCol_isColoring {n : ℕ} {𝓗 : Hypergraph (Fin n)} (hn : 1 ≤ n) (hlin : 𝓗.IsLinear)
    (C₂ : (𝓗.bigEdges).Coloring (Fin n)) :
    ∀ ⦃e₁ e₂ : 𝓗⦄, e₁ ≠ e₂ → ((e₁ : Set (Fin n)) ∩ (e₂ : Set (Fin n))).Nonempty →
      extCol hn hlin C₂ e₁ ≠ extCol hn hlin C₂ e₂ := by
  classical
  intro e₁ e₂ he hnon
  by_cases h₁ : HasTwoVertices (e₁ : Set (Fin n))
  · by_cases h₂ : HasTwoVertices (e₂ : Set (Fin n))
    · dsimp [extCol]
      rw [dif_pos h₁, dif_pos h₂]
      have hneq : (⟨(e₁ : Set (Fin n)), ⟨e₁.2, h₁⟩⟩ : 𝓗.bigEdges) ≠
          ⟨(e₂ : Set (Fin n)), ⟨e₂.2, h₂⟩⟩ := by
        intro hEq
        apply he
        apply Subtype.ext
        exact congrArg (fun x : 𝓗.bigEdges => x.1) hEq
      have hnon' : ((⟨(e₁ : Set (Fin n)), ⟨e₁.2, h₁⟩⟩ : 𝓗.bigEdges).1 ∩
          (⟨(e₂ : Set (Fin n)), ⟨e₂.2, h₂⟩⟩ : 𝓗.bigEdges).1 : Set (Fin n)).Nonempty := by
        simpa using hnon
      exact C₂.isColoring ⟨(e₁ : Set (Fin n)), ⟨e₁.2, h₁⟩⟩ ⟨(e₂ : Set (Fin n)), ⟨e₂.2, h₂⟩⟩
        hneq hnon'
    · exact extCol_ne_big_small hn hlin C₂ h₁ h₂ hnon
  · by_cases h₂ : HasTwoVertices (e₂ : Set (Fin n))
    · have hres := extCol_ne_big_small hn hlin C₂ h₂ h₁ (by simpa [Set.inter_comm] using hnon)
      exact hres.symm
    · exfalso
      apply he
      apply Subtype.ext
      rcases hnon with ⟨x, hx₁, hx₂⟩
      ext y
      constructor
      · intro hy
        have hyx : y = x := AtMostOneVertex.eq_of_mem h₁ hy hx₁
        rw [hyx]
        exact hx₂
      · intro hy
        have hyx : y = x := AtMostOneVertex.eq_of_mem h₂ hy hx₂
        rw [hyx]
        exact hx₁

/-- The colouring of all of `𝓗` extending `C₂`. -/
noncomputable def extendColoring {n : ℕ} {𝓗 : Hypergraph (Fin n)} (hn : 1 ≤ n)
    (hlin : 𝓗.IsLinear) (C₂ : (𝓗.bigEdges).Coloring (Fin n)) : 𝓗.Coloring (Fin n) where
  labels := extCol hn hlin C₂
  isColoring := extCol_isColoring hn hlin C₂

/-- If the large edges of a linear hypergraph on `n ≥ 1` vertices can be coloured with `n`
colours then all of its edges can be. -/
theorem colorable_of_colorable_bigEdges {n : ℕ} (hn : 1 ≤ n) {𝓗 : Hypergraph (Fin n)}
    (hlin : 𝓗.IsLinear) : (𝓗.bigEdges).Colorable n → 𝓗.Colorable n := by
  rintro ⟨C₂⟩
  exact ⟨extendColoring hn hlin C₂⟩

/-- Theorem 1.1 for all hypergraphs follows from Theorem 1.1 restricted to hypergraphs
without small edges (edges of size at most one). -/
theorem eflStatement_of_bigEdges :
    (∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear →
      (∀ e ∈ 𝓗, HasTwoVertices (e : Set (Fin n))) → 𝓗.chromaticIndex ≤ n) →
    eflStatement := by
  rintro ⟨N₀, h₀⟩
  rw [eflStatement_iff_threshold]
  refine ⟨max N₀ 1, ?_⟩
  intro n hn
  have hn₀ : N₀ ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  intro 𝓗 hlin
  have hc : (𝓗.bigEdges).chromaticIndex ≤ n := by
    exact h₀ n hn₀ 𝓗.bigEdges (IsLinear.bigEdges hlin) (by intro e he; exact he.2)
  have hcol : (𝓗.bigEdges).Colorable n := by
    exact (Hypergraph.chromaticIndex_le_iff_colorable (𝓗.bigEdges)
      (Hypergraph.colorable_of_finite_vertices 𝓗.bigEdges)).1 hc
  have hfull : 𝓗.Colorable n := colorable_of_colorable_bigEdges hn1 hlin hcol
  exact Hypergraph.chromaticIndex_le_of_colorable 𝓗 hfull

end ErdosFaberLovaszConjecture
