/-
# Greedy list colouring and the extension proposition of the naive colouring procedure

This module contains the *deterministic* half of the proof of `SparseGraphStatement`
(`Submission/Deep/Reed.lean`), the Molloy–Reed bound for `δ`-sparse graphs.

The naive colouring procedure (Molloy–Reed, *Graph Colouring and the Probabilistic Method*,
Chapter 10; Bruhn–Joos; Bonamy–Perrett–Postle, arXiv:1810.06704, Section 3) produces a
*partial* proper colouring of `G` and then extends it.  The extension step is purely
deterministic and is isolated here:

* `exists_list_coloring` — the greedy list-colouring engine: a finite graph in which every
  vertex has more available colours in its list than neighbours is list-colourable.
* `PartialColoring G k` — a partial colouring with the colours `Fin k` (uncoloured vertices
  are those mapped to `none`), proper on the coloured vertices.
* `PartialColoring.coloredNbrs`, `PartialColoring.colCount`, `PartialColoring.distinctColors`
  — the vocabulary of the analysis: the coloured neighbours of a vertex `v`, the number of
  coloured neighbours of `v` of each colour, and the number of distinct colours among them
  (the paper's `Col(v)` and `Dist(v)`).
* `PartialColoring.pairTerm`, `PartialColoring.tripleTerm` — the paper's `P_v` and `T_v`
  (`P_v = ∑_c C(Col_c(v), 2)`, `T_v = ∑_c C(Col_c(v), 3)`, where `Col_c(v)` is the number of
  coloured neighbours of `v` of colour `c`).
* `PartialColoring.colMinusDist_ge_pair_sub_triple` — the elementary inclusion–exclusion
  inequality `Col(v) - Dist(v) ≥ P_v - T_v`, valid for *every* partial colouring.
* `PartialColoring.colorable_of_partial` — **the extension proposition** (Proposition 3.2 of
  Bonamy–Perrett–Postle / Proposition 10.4 of Molloy–Reed): a partial proper `k`-colouring of
  a graph such that `Col(v) - Dist(v) ≥ d(v) + 1 - k` at every vertex extends to a proper
  `k`-colouring.

Everything in this file is deterministic and sorry-free.
-/
import Submission.Deep.Reed
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*}

/-! ## 1. The greedy list-colouring engine -/

/-- **Greedy list colouring.**  If `L v` has more elements than `v` has neighbours, for every
vertex `v`, then there is a proper colouring of `G` with `c v ∈ L v` for all `v`. -/
theorem exists_list_coloring (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (L : V → Finset (Fin k)) (h : ∀ v, (G.neighborFinset v).card < (L v).card) :
    ∃ c : V → Fin k, (∀ v, c v ∈ L v) ∧ ∀ v w, G.Adj v w → c v ≠ c w := by
  classical
  have hne : ∀ v, (L v).Nonempty := fun v =>
    Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) (h v))
  have key : ∀ S : Finset V, ∃ c : V → Fin k, (∀ v ∈ S, c v ∈ L v) ∧
      (∀ v ∈ S, ∀ w ∈ S, G.Adj v w → c v ≠ c w) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨fun v => Classical.choose (hne v), by simp, by simp⟩
    | insert a s ha ih =>
        obtain ⟨c', hc'L, hc'P⟩ := ih
        let F : Finset (Fin k) := (s.filter (fun w => G.Adj a w)).image c'
        have hFcard : F.card ≤ (G.neighborFinset a).card := by
          have h1 : F.card ≤ (s.filter (fun w => G.Adj a w)).card := Finset.card_image_le
          have h2 : (s.filter (fun w => G.Adj a w)).card ≤ (G.neighborFinset a).card := by
            apply Finset.card_le_card
            intro w hw
            rw [Finset.mem_filter] at hw
            rw [SimpleGraph.mem_neighborFinset]
            exact hw.2
          exact le_trans h1 h2
        obtain ⟨x, hxL, hxF⟩ :=
          Finset.exists_mem_notMem_of_card_lt_card (lt_of_le_of_lt hFcard (h a))
        have hupd : ∀ w : V, w ≠ a → Function.update c' a x w = c' w :=
          fun w hw => Function.update_of_ne hw x c'
        refine ⟨Function.update c' a x, ?_, ?_⟩
        · intro v hv
          rw [Finset.mem_insert] at hv
          rcases hv with hva | hv
          · rw [hva, Function.update_self]; exact hxL
          · rw [hupd v (by rintro rfl; exact ha hv)]; exact hc'L v hv
        · intro v hv w hw hadj hcontra
          rw [Finset.mem_insert] at hv hw
          rcases hv with hva | hv
          · rcases hw with hwa | hw
            · rw [hva, hwa] at hadj; exact G.irrefl hadj
            · have hmem : c' w ∈ F := by
                refine Finset.mem_image.mpr ⟨w, ?_, rfl⟩
                rw [Finset.mem_filter]
                exact ⟨hw, by rw [hva] at hadj; exact hadj⟩
              rw [hva, Function.update_self,
                hupd w (by rintro rfl; exact ha hw)] at hcontra
              exact hxF (hcontra ▸ hmem)
          · rcases hw with hwa | hw
            · have hmem : c' v ∈ F := by
                refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
                rw [Finset.mem_filter]
                exact ⟨hv, by rw [hwa] at hadj; exact (G.adj_comm v a).mp hadj⟩
              rw [hwa, Function.update_self,
                hupd v (by rintro rfl; exact ha hv)] at hcontra
              exact hxF (hcontra.symm ▸ hmem)
            · rw [hupd v (by rintro rfl; exact ha hv),
                hupd w (by rintro rfl; exact ha hw)] at hcontra
              exact hc'P v hv w hw hadj hcontra
  obtain ⟨c, hcL, hcP⟩ := key Finset.univ
  exact ⟨c, fun v => hcL v (Finset.mem_univ v),
    fun v w hadj => hcP v (Finset.mem_univ v) w (Finset.mem_univ w) hadj⟩

/-! ## 2. Partial colourings and the inclusion–exclusion inequality -/

/-- A **partial proper colouring** of `G` with the colours `Fin k`: `col v = none` means that
`v` is uncoloured, and two adjacent vertices may not receive the same colour. -/
structure PartialColoring (G : SimpleGraph V) (k : ℕ) where
  /-- The colour of each vertex, if any. -/
  col : V → Option (Fin k)
  /-- The colouring is proper on the coloured vertices. -/
  isProper : ∀ u v : V, G.Adj u v → col u = col v → col u = none

namespace PartialColoring

variable {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {k : ℕ}

/-- The set of *coloured* neighbours of `v`. -/
def coloredNbrs (φ : PartialColoring G k) (v : V) : Finset V :=
  (G.neighborFinset v).filter (fun w => φ.col w ≠ none)

/-- The number of coloured neighbours of `v` of colour `c`. -/
def colCount (φ : PartialColoring G k) (v : V) (c : Fin k) : ℕ :=
  ((G.neighborFinset v).filter (fun w => φ.col w = some c)).card

/-- The set of colours that occur on at least one coloured neighbour of `v`. -/
def distinctColors (φ : PartialColoring G k) (v : V) : Finset (Fin k) :=
  Finset.univ.filter (fun c => φ.colCount v c ≠ 0)

/-- `Col(v)`: the number of coloured neighbours of `v`. -/
def numColored (φ : PartialColoring G k) (v : V) : ℕ := ∑ c, φ.colCount v c

/-- `Dist(v)`: the number of distinct colours on the coloured neighbours of `v`. -/
def numDistinct (φ : PartialColoring G k) (v : V) : ℕ := (φ.distinctColors v).card

/-- The paper's `P_v`: the number of pairs of coloured neighbours of `v` carrying the same
colour, i.e. `∑_c C(Col_c(v), 2)`. -/
def pairTerm (φ : PartialColoring G k) (v : V) : ℕ :=
  ∑ c, (φ.colCount v c).choose 2

/-- The paper's `T_v`: the number of triples of coloured neighbours of `v` carrying the same
colour, i.e. `∑_c C(Col_c(v), 3)`. -/
def tripleTerm (φ : PartialColoring G k) (v : V) : ℕ :=
  ∑ c, (φ.colCount v c).choose 3

variable (φ : PartialColoring G k)

@[simp] lemma mem_coloredNbrs {v w : V} :
    w ∈ φ.coloredNbrs v ↔ G.Adj v w ∧ φ.col w ≠ none := by
  simp [coloredNbrs]

lemma colCount_eq_zero_iff {v : V} {c : Fin k} :
    φ.colCount v c = 0 ↔ ∀ w : V, G.Adj v w → φ.col w ≠ some c := by
  rw [colCount, Finset.card_eq_zero]
  constructor
  · intro h w haw hw
    have hmem : w ∈ (G.neighborFinset v).filter (fun w => φ.col w = some c) := by
      rw [Finset.mem_filter]
      exact ⟨by rwa [SimpleGraph.mem_neighborFinset], hw⟩
    rw [h] at hmem
    simp at hmem
  · intro h
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨w, hw⟩
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hw
    exact h w hw.1 hw.2

@[simp] lemma mem_distinctColors {v : V} {c : Fin k} :
    c ∈ φ.distinctColors v ↔ φ.colCount v c ≠ 0 := by
  simp [distinctColors]

/-- The number of coloured neighbours is the sum of the colour counts. -/
lemma coloredNbrs_card (v : V) : (φ.coloredNbrs v).card = φ.numColored v := by
  classical
  have hdisj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun c => (G.neighborFinset v).filter (fun w => φ.col w = some c)) := by
    intro c _ c' _ hcc'
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    rw [Finset.mem_filter] at hw hw'
    exact hcc' (Option.some.inj (hw.2.symm.trans hw'.2))
  have hunion : φ.coloredNbrs v = (Finset.univ : Finset (Fin k)).disjiUnion
      (fun c => (G.neighborFinset v).filter (fun w => φ.col w = some c)) hdisj := by
    ext w
    rw [coloredNbrs, Finset.mem_filter, Finset.mem_disjiUnion]
    constructor
    · rintro ⟨hw, hne⟩
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hne
      exact ⟨c, Finset.mem_univ c, by rw [Finset.mem_filter]; exact ⟨hw, hc⟩⟩
    · rintro ⟨c, -, hw⟩
      rw [Finset.mem_filter] at hw
      exact ⟨hw.1, by rw [hw.2]; simp⟩
  rw [hunion, Finset.card_disjiUnion, numColored]
  rfl

/-- The number of *uncoloured* neighbours of `v`. -/
lemma card_uncoloredNbrs (v : V) :
    ((G.neighborFinset v).filter (fun w => φ.col w = none)).card
      = (G.neighborFinset v).card - φ.numColored v := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := G.neighborFinset v)
    (p := fun w => φ.col w ≠ none)
  have hc : ((G.neighborFinset v).filter (fun w => φ.col w ≠ none)).card = φ.numColored v :=
    φ.coloredNbrs_card v
  have hu : ((G.neighborFinset v).filter (fun w => ¬ φ.col w ≠ none))
      = ((G.neighborFinset v).filter (fun w => φ.col w = none)) := by
    congr 1
    ext w
    simp
  rw [hc, hu] at h
  omega

lemma numDistinct_eq_sum (v : V) :
    φ.numDistinct v = ∑ c, (if φ.colCount v c = 0 then 0 else 1) := by
  rw [numDistinct, distinctColors, Finset.card_filter]
  exact Finset.sum_congr rfl fun c _ => by split_ifs <;> simp_all

/-- `Col(v) - Dist(v) = ∑_c max (Col_c(v) - 1) 0`. -/
lemma numColored_sub_numDistinct (v : V) :
    (φ.numColored v : ℤ) - (φ.numDistinct v : ℤ)
      = ∑ c, max ((φ.colCount v c : ℤ) - 1) 0 := by
  rw [φ.numDistinct_eq_sum v, numColored, Nat.cast_sum, Nat.cast_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : φ.colCount v c = 0
  · rw [if_pos h, h]
    norm_num
  · rw [if_neg h]
    have h1 : (1 : ℤ) ≤ (φ.colCount v c : ℤ) := by
      have : 1 ≤ φ.colCount v c := Nat.one_le_iff_ne_zero.mpr h
      exact_mod_cast this
    rw [max_eq_left (by linarith)]
    norm_num

/-- `Dist(v) ≤ Col(v)`: the distinct colours on the coloured neighbours of `v` are at most
the number of coloured neighbours. -/
lemma numDistinct_le_numColored (v : V) : φ.numDistinct v ≤ φ.numColored v := by
  rw [numDistinct_eq_sum, numColored]
  refine Finset.sum_le_sum fun c _ => ?_
  by_cases h : φ.colCount v c = 0
  · simp [h]
  · simp [h]
    exact Nat.one_le_iff_ne_zero.mpr h

/-- The number of coloured neighbours of `v` is at most the degree of `v`. -/
lemma numColored_le_degree (v : V) : φ.numColored v ≤ G.degree v := by
  rw [← φ.coloredNbrs_card v, coloredNbrs]
  exact Finset.card_filter_le _ _

/-- `Col(v) - Dist(v) ≥ 0`. -/
lemma numDistinct_le_numColored_int (v : V) :
    (0 : ℤ) ≤ (φ.numColored v : ℤ) - (φ.numDistinct v : ℤ) := by
  have := φ.numDistinct_le_numColored v
  omega

/-- **Inclusion–exclusion**: for *every* partial colouring, `Col(v) - Dist(v) ≥ P_v - T_v`. -/
theorem colMinusDist_ge_pair_sub_triple (v : V) :
    (φ.pairTerm v : ℤ) - (φ.tripleTerm v : ℤ)
      ≤ (φ.numColored v : ℤ) - (φ.numDistinct v : ℤ) := by
  have harith : ∀ n : ℕ, (((n.choose 2 : ℕ)) : ℤ) - (((n.choose 3 : ℕ)) : ℤ)
      ≤ max ((n : ℤ) - 1) 0 := by
    intro n
    rcases Nat.lt_or_ge n 5 with h | h
    · interval_cases n <;> decide
    · have hstep : n.choose 3 * 3 = n.choose 2 * (n - 2) := by
        have := Nat.choose_succ_right_eq n 2
        simpa using this
      have hle : n.choose 2 * 3 ≤ n.choose 3 * 3 := by
        rw [hstep]
        exact Nat.mul_le_mul_left _ (by omega)
      have h32 : n.choose 2 ≤ n.choose 3 := Nat.le_of_mul_le_mul_right hle (by norm_num)
      have hcast : ((n.choose 3 : ℕ) : ℤ) ≥ ((n.choose 2 : ℕ) : ℤ) := by exact_mod_cast h32
      have : (((n.choose 2 : ℕ)) : ℤ) - (((n.choose 3 : ℕ)) : ℤ) ≤ 0 := by linarith
      exact le_trans this (le_max_right _ _)
  rw [pairTerm, tripleTerm, Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib,
    φ.numColored_sub_numDistinct v]
  exact Finset.sum_le_sum fun c _ => harith _

end PartialColoring

/-! ## 3. The extension proposition -/

namespace PartialColoring

variable {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {k : ℕ}

/-- The list of colours available at an *uncoloured* vertex `v`: those that do not occur on a
coloured neighbour of `v`. -/
def availList (φ : PartialColoring G k) (v : V) : Finset (Fin k) :=
  Finset.univ.filter (fun c => ∀ w : V, G.Adj v w → φ.col w ≠ some c)

lemma availList_eq_sdiff (φ : PartialColoring G k) (v : V) :
    φ.availList v = Finset.univ \ φ.distinctColors v := by
  ext c
  simp only [availList, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    mem_distinctColors, colCount_eq_zero_iff, not_not]

lemma card_availList (φ : PartialColoring G k) (v : V) :
    (φ.availList v).card = k - φ.numDistinct v := by
  rw [availList_eq_sdiff, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
    Fintype.card_fin]
  rfl

/-- **The extension proposition**: a partial proper `k`-colouring of `G` such that
`Col(v) - Dist(v) ≥ d(v) + 1 - k` at every vertex extends to a proper `k`-colouring. -/
theorem colorable_of_partial (φ : PartialColoring G k)
    (h : ∀ v : V, (G.degree v : ℤ) + 1 - k
      ≤ (φ.numColored v : ℤ) - (φ.numDistinct v : ℤ)) :
    G.Colorable k := by
  classical
  set U : Set V := {v | φ.col v = none} with hU
  have hnum : ∀ v : V, ((G.neighborFinset v).filter (fun w => φ.col w = none)).card
      = G.degree v - φ.numColored v := fun v => φ.card_uncoloredNbrs v
  -- the neighbourhood of an uncoloured vertex inside the induced graph on `U`
  have himg : ∀ v : ↥U, ((G.induce U).neighborFinset v).image Subtype.val
      = (G.neighborFinset v.1).filter (fun w => φ.col w = none) := by
    intro v
    ext w
    constructor
    · intro hw
      obtain ⟨w', hw', hweq⟩ := Finset.mem_image.mp hw
      rw [SimpleGraph.mem_neighborFinset] at hw'
      rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      refine ⟨?_, ?_⟩
      · rw [← hweq]
        rwa [SimpleGraph.induce_adj] at hw'
      · rw [← hweq]; exact w'.2
    · intro hw
      rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hw
      refine Finset.mem_image.mpr ⟨⟨w, hw.2⟩, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj]
      exact hw.1
  have hdeg : ∀ v : ↥U, ((G.induce U).neighborFinset v).card < (φ.availList v.1).card := by
    intro v
    have hcard : ((G.induce U).neighborFinset v).card
        = ((G.neighborFinset v.1).filter (fun w => φ.col w = none)).card := by
      rw [← Finset.card_image_of_injective _ Subtype.coe_injective, himg v]
    have hmain := h v.1
    have hnumcol : φ.numColored v.1 ≤ G.degree v.1 := by
      rw [← φ.coloredNbrs_card v.1, coloredNbrs]
      exact Finset.card_filter_le _ _
    have hnumdis : φ.numDistinct v.1 ≤ k := by
      have := Finset.card_le_univ (φ.distinctColors v.1)
      simpa [numDistinct, Fintype.card_fin] using this
    have hgoal : G.degree v.1 - φ.numColored v.1 < k - φ.numDistinct v.1 := by
      have h1 : (φ.numColored v.1 : ℤ) ≤ (G.degree v.1 : ℤ) := by exact_mod_cast hnumcol
      have h2 : (φ.numDistinct v.1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hnumdis
      omega
    rw [hcard, hnum v.1, φ.card_availList v.1]
    exact hgoal
  obtain ⟨c, hcL, hcP⟩ := exists_list_coloring (G.induce U) (fun v : ↥U => φ.availList v.1) hdeg
  -- a total colouring: the list colouring on the uncoloured vertices, `φ` elsewhere
  have hcolSome : ∀ v : V, φ.col v ≠ none → ∃ a, φ.col v = some a :=
    fun v hv => Option.ne_none_iff_exists'.mp hv
  let f : V → Fin k := fun v =>
    if h : φ.col v = none then c ⟨v, h⟩ else Classical.choose (hcolSome v h)
  have hchoose : ∀ (v : V) (h : φ.col v ≠ none) {b : Fin k}, φ.col v = some b →
      Classical.choose (hcolSome v h) = b := by
    intro v h b hb
    have hspec : φ.col v = some (Classical.choose (hcolSome v h)) :=
      Classical.choose_spec (hcolSome v h)
    exact Option.some.inj (hspec.symm.trans hb)
  have hf_none : ∀ v : V, (h : φ.col v = none) → f v = c ⟨v, h⟩ := by
    intro v h
    simp only [f, dif_pos h]
  have hf_some : ∀ (v : V) (h : φ.col v ≠ none) {b : Fin k}, φ.col v = some b → f v = b := by
    intro v h b hb
    simp only [f, dif_neg h, hchoose v h hb]
  refine ⟨SimpleGraph.Coloring.mk f ?_⟩
  intro u v huv hEq
  by_cases hu : φ.col u = none
  · by_cases hv : φ.col v = none
    · -- both uncoloured: use the list colouring of the induced graph
      have hadj : (G.induce U).Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
        rw [SimpleGraph.induce_adj]; exact huv
      have hne := hcP ⟨u, hu⟩ ⟨v, hv⟩ hadj
      rw [hf_none u hu, hf_none v hv] at hEq
      exact hne hEq
    · -- `u` uncoloured, `v` coloured: `c u` avoids the colour of `v`
      obtain ⟨a, ha⟩ : ∃ a, φ.col v = some a := Option.ne_none_iff_exists'.mp hv
      have hmem := hcL ⟨u, hu⟩
      rw [availList, Finset.mem_filter] at hmem
      have hcontra := hmem.2 v huv
      rw [hf_none u hu, hf_some v hv ha] at hEq
      rw [hEq] at hcontra
      exact hcontra ha
  · by_cases hv : φ.col v = none
    · -- `v` uncoloured, `u` coloured
      obtain ⟨b, hb⟩ : ∃ b, φ.col u = some b := Option.ne_none_iff_exists'.mp hu
      have hmem := hcL ⟨v, hv⟩
      rw [availList, Finset.mem_filter] at hmem
      have hcontra := hmem.2 u ((G.adj_comm u v).mp huv)
      rw [hf_none v hv, hf_some u hu hb] at hEq
      rw [← hEq] at hcontra
      exact hcontra hb
    · -- both coloured: properness of the partial colouring
      obtain ⟨a, ha⟩ : ∃ a, φ.col v = some a := Option.ne_none_iff_exists'.mp hv
      obtain ⟨b, hb⟩ : ∃ b, φ.col u = some b := Option.ne_none_iff_exists'.mp hu
      rw [hf_some u hu hb, hf_some v hv ha] at hEq
      have hnone := φ.isProper u v huv (by rw [hb, ha, hEq])
      rw [hb] at hnone
      exact absurd hnone (by simp)

end PartialColoring

end Work.Deep.Sparse
