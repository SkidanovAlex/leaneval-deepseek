/-
# Fired colours of a random colouring

This module sets up the combinatorial core of the naive colouring procedure
(`Submission/Work/Deep/Sparse/ncp_core.lean`).

For a finite simple graph `G`, a vertex `v` and a colouring `f : V → Fin k`, a colour `c`
*fire*s at `v` if there are two non-adjacent neighbours `x`, `y` of `v` of colour `c` such
that no neighbour of `x` or of `y` has colour `c`.  Then both `x` and `y` keep the colour `c`
in the partial colouring `ofColoring G f` (the naive colouring procedure), so `c` is a
*repeated* colour at `v`.

The deterministic content of this file is the reduction

`firingCard_le : firingCard G v f ≤ Col(v) - Dist(v)`,

i.e. the number of fired colours is at most `numColored v - numDistinct v` of the partial
colouring.  The probabilistic bounds for `firingCard` (its expectation and its concentration)
are stated and proved in the sibling modules `FiringExpect` and `FiringConc`.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.Basic
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.ProbModel

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A colour `c` **fires** at `v` under the colouring `f` if two non-adjacent neighbours `x`,
`y` of `v` both have colour `c` and no neighbour of either of them has colour `c`. -/
abbrev Fires (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) {k : ℕ} (f : V → Fin k)
    (c : Fin k) : Prop :=
  ∃ x y : V, x ≠ y ∧ G.Adj v x ∧ G.Adj v y ∧ ¬ G.Adj x y ∧ f x = c ∧ f y = c ∧
    ∀ u : V, (G.Adj x u ∨ G.Adj y u) → u ≠ x → u ≠ y → f u ≠ c

/-- The number of colours firing at `v`. -/
noncomputable def firingCard (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) {k : ℕ}
    (f : V → Fin k) : ℕ :=
  (Finset.univ.filter (fun c => Fires G v f c)).card

lemma firingCard_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) {k : ℕ}
    (f : V → Fin k) :
    firingCard G v f = ∑ c : Fin k, (if Fires G v f c then 1 else 0) := by
  rw [firingCard, Finset.card_filter]

/-- A firing pair witnesses that the colour is retained on at least two neighbours of `v` in
the partial colouring `ofColoring G f`. -/
lemma two_le_colourClassCount_of_fires (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    {k : ℕ} (f : V → Fin k) {c : Fin k} (h : Fires G v f c) :
    2 ≤ colourClassCount G f v c := by
  classical
  obtain ⟨x, y, hxyne, hvx, hvy, hnadj, hxc, hyc, havoid⟩ := h
  set S : Finset V := (G.neighborFinset v).filter (fun z => Retained G f z ∧ f z = c) with hS
  have hx : x ∈ S := by
    rw [hS, Finset.mem_filter]
    refine ⟨by rw [SimpleGraph.mem_neighborFinset]; exact hvx, ?_, hxc⟩
    intro w hw
    have hwx : w ≠ x := fun hwx => G.irrefl (hwx ▸ hw)
    have hwy : w ≠ y := fun hwy => hnadj (hwy ▸ hw)
    rw [hxc]
    exact havoid w (Or.inl hw) hwx hwy
  have hy : y ∈ S := by
    rw [hS, Finset.mem_filter]
    refine ⟨by rw [SimpleGraph.mem_neighborFinset]; exact hvy, ?_, hyc⟩
    intro w hw
    have hwy : w ≠ y := fun hwy => G.irrefl (hwy ▸ hw)
    have hwx : w ≠ x := fun hwx => hnadj ((hwx ▸ hw).symm)
    rw [hyc]
    exact havoid w (Or.inr hw) hwx hwy
  have hsub : ({x, y} : Finset V) ⊆ S := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hcard : ({x, y} : Finset V).card = 2 := by
    rw [Finset.card_pair]; exact hxyne
  calc 2 = ({x, y} : Finset V).card := hcard.symm
    _ ≤ S.card := Finset.card_le_card hsub
    _ = colourClassCount G f v c := by rw [hS, colourClassCount]

/-- `Col(v) - Dist(v) = ∑_c max (Col_c(v) - 1) 0` for the partial colouring `ofColoring G f`. -/
lemma numColored_sub_numDistinct_eq (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (f : V → Fin k) (v : V) :
    ((ofColoring G f).numColored v : ℤ) - ((ofColoring G f).numDistinct v : ℤ)
      = ∑ c : Fin k, max ((colourClassCount G f v c : ℤ) - 1) 0 := by
  classical
  have hc : ∀ c : Fin k, (ofColoring G f).colCount v c = colourClassCount G f v c := by
    intro c
    rw [PartialColoring.colCount, colourClassCount]
    congr 1
    ext x
    by_cases hx : Retained G f x
    · simp [ofColoring, hx]
    · simp [ofColoring, hx]
  rw [PartialColoring.numColored_sub_numDistinct]
  exact Finset.sum_congr rfl fun c _ => by rw [hc c]

/-- **The deterministic reduction.**  Every fired colour is a repeated colour, so the number
of fired colours is at most `Col(v) - Dist(v)` for the partial colouring `ofColoring G f`. -/
theorem firingCard_le (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (f : V → Fin k) (v : V) :
    (firingCard G v f : ℤ) ≤
      ((ofColoring G f).numColored v : ℤ) - ((ofColoring G f).numDistinct v : ℤ) := by
  classical
  rw [numColored_sub_numDistinct_eq]
  have h1 : (firingCard G v f : ℤ)
      = ∑ c : Fin k, (if Fires G v f c then (1 : ℤ) else 0) := by
    rw [firingCard_eq_sum]; push_cast; rfl
  rw [h1]
  refine Finset.sum_le_sum fun c _ => ?_
  by_cases h : Fires G v f c
  · rw [if_pos h]
    have h2 : (2 : ℤ) ≤ (colourClassCount G f v c : ℤ) := by
      exact_mod_cast two_le_colourClassCount_of_fires G v f h
    have h3 : (1 : ℤ) ≤ (colourClassCount G f v c : ℤ) - 1 := by linarith
    exact le_trans h3 (le_max_left _ _)
  · rw [if_neg h]
    simpa using le_max_right ((colourClassCount G f v c : ℤ) - 1) (0 : ℤ)

/-- The set of vertices whose colours determine the fired colours at `v`: the neighbours of
`v` together with their neighbours (the vertices at distance at most two from `v`). -/
def ball (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  G.neighborFinset v ∪ (G.neighborFinset v).biUnion (fun x => G.neighborFinset x)

lemma mem_ball_iff (G : SimpleGraph V) [DecidableRel G.Adj] {v u : V} :
    u ∈ ball G v ↔ G.Adj v u ∨ ∃ x : V, G.Adj v x ∧ G.Adj x u := by
  rw [ball, Finset.mem_union, SimpleGraph.mem_neighborFinset, Finset.mem_biUnion]
  constructor
  · rintro (h | ⟨x, hx, hxu⟩)
    · exact Or.inl h
    · exact Or.inr ⟨x, (SimpleGraph.mem_neighborFinset G v x).mp hx,
        (SimpleGraph.mem_neighborFinset G x u).mp hxu⟩
  · rintro (h | ⟨x, hvx, hxu⟩)
    · exact Or.inl h
    · exact Or.inr ⟨x, (SimpleGraph.mem_neighborFinset G v x).mpr hvx,
        (SimpleGraph.mem_neighborFinset G x u).mpr hxu⟩

lemma mem_ball_of_adj (G : SimpleGraph V) [DecidableRel G.Adj] {v x : V} (h : G.Adj v x) :
    x ∈ ball G v := mem_ball_iff G |>.mpr (Or.inl h)

lemma mem_ball_of_adj₂ (G : SimpleGraph V) [DecidableRel G.Adj] {v x u : V}
    (hvx : G.Adj v x) (hxu : G.Adj x u) : u ∈ ball G v :=
  mem_ball_iff G |>.mpr (Or.inr ⟨x, hvx, hxu⟩)

/-- **Determining coordinates.**  The fired colours at `v` (hence `firingCard G v f`) depend
only on the colours of the vertices of `ball G v`. -/
lemma firingCard_congr (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {f g : V → Fin k}
    {v : V} (h : ∀ u ∈ ball G v, f u = g u) :
    firingCard G v f = firingCard G v g := by
  classical
  have hfires : ∀ c : Fin k, Fires G v f c ↔ Fires G v g c := by
    intro c
    constructor
    · rintro ⟨x, y, hxy, hvx, hvy, hnadj, hxc, hyc, havoid⟩
      refine ⟨x, y, hxy, hvx, hvy, hnadj, ?_, ?_, ?_⟩
      · rw [← h x (mem_ball_of_adj G hvx)]; exact hxc
      · rw [← h y (mem_ball_of_adj G hvy)]; exact hyc
      · intro u hu hux huy
        rcases hu with hxu | hyu
        · rw [← h u (mem_ball_of_adj₂ G hvx hxu)]
          exact havoid u (Or.inl hxu) hux huy
        · rw [← h u (mem_ball_of_adj₂ G hvy hyu)]
          exact havoid u (Or.inr hyu) hux huy
    · rintro ⟨x, y, hxy, hvx, hvy, hnadj, hxc, hyc, havoid⟩
      refine ⟨x, y, hxy, hvx, hvy, hnadj, ?_, ?_, ?_⟩
      · rw [h x (mem_ball_of_adj G hvx)]; exact hxc
      · rw [h y (mem_ball_of_adj G hvy)]; exact hyc
      · intro u hu hux huy
        rcases hu with hxu | hyu
        · rw [h u (mem_ball_of_adj₂ G hvx hxu)]
          exact havoid u (Or.inl hxu) hux huy
        · rw [h u (mem_ball_of_adj₂ G hvy hyu)]
          exact havoid u (Or.inr hyu) hux huy
  rw [firingCard_eq_sum, firingCard_eq_sum]
  exact Finset.sum_congr rfl fun c _ => by
    by_cases hc : Fires G v f c
    · rw [if_pos hc, if_pos ((hfires c).mp hc)]
    · rw [if_neg hc, if_neg (fun hg => hc ((hfires c).mpr hg))]

end Work.Deep.Sparse
