/-
# Determination of the naive-colouring statistics on a ball

The colour counts `Col(v) - Dist(v)` of the partial colouring `ofColoring G f` produced by the
naive colouring procedure depend only on the colours of the vertices at distance at most two
from `v` (the set `ball G v` of `Submission.Work.Deep.Sparse.FiringDefs`).  This is the input
needed by the Lovász Local Lemma: the "bad" events are coordinate-local.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbModel
import Submission.Work.Deep.Sparse.FiringDefs

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Agreement of the partial colouring on the neighbourhood.**  If two colourings agree on
`ball G v`, then the partial colourings `ofColoring G f` and `ofColoring G g` have the same
colour on every neighbour of `v`. -/
lemma ofColoring_col_agree (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {f g : V → Fin k}
    {v : V} (h : ∀ u ∈ ball G v, f u = g u) :
    ∀ x ∈ G.neighborFinset v, (ofColoring G f).col x = (ofColoring G g).col x := by
  intro x hx
  have hxv : G.Adj v x := (G.mem_neighborFinset (v := v) (w := x)).mp hx
  have hfx : f x = g x := h x (mem_ball_of_adj G hxv)
  have hret : Retained G f x ↔ Retained G g x := by
    constructor
    · intro hr w hw
      rw [← hfx, ← h w (mem_ball_of_adj₂ G hxv hw)]
      exact hr w hw
    · intro hr w hw
      rw [hfx, h w (mem_ball_of_adj₂ G hxv hw)]
      exact hr w hw
  rw [ofColoring, ofColoring]
  simp only [hret, hfx]

/-- The colour class counts at `v` are determined by the colours on `ball G v`. -/
lemma colCount_agree (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {f g : V → Fin k}
    {v : V} (h : ∀ u ∈ ball G v, f u = g u) (c : Fin k) :
    (ofColoring G f).colCount v c = (ofColoring G g).colCount v c := by
  rw [PartialColoring.colCount, PartialColoring.colCount]
  congr 1
  refine Finset.filter_congr ?_
  intro x hx
  rw [ofColoring_col_agree G h x hx]

/-- `Col(v)` is determined by the colours on `ball G v`. -/
lemma numColored_agree (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {f g : V → Fin k}
    {v : V} (h : ∀ u ∈ ball G v, f u = g u) :
    (ofColoring G f).numColored v = (ofColoring G g).numColored v := by
  rw [PartialColoring.numColored, PartialColoring.numColored]
  exact Finset.sum_congr rfl fun c _ => colCount_agree G h c

/-- `Dist(v)` is determined by the colours on `ball G v`. -/
lemma numDistinct_agree (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {f g : V → Fin k}
    {v : V} (h : ∀ u ∈ ball G v, f u = g u) :
    (ofColoring G f).numDistinct v = (ofColoring G g).numDistinct v := by
  rw [PartialColoring.numDistinct, PartialColoring.numDistinct, PartialColoring.distinctColors,
    PartialColoring.distinctColors]
  congr 1
  refine Finset.filter_congr ?_
  intro c _
  rw [colCount_agree G h c]

/-- **The statistic of the naive colouring procedure is coordinate-local**: if two colourings
agree on `ball G v`, then `Col(v) - Dist(v)` takes the same value. -/
lemma numColored_sub_numDistinct_agree (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    {f g : V → Fin k} {v : V} (h : ∀ u ∈ ball G v, f u = g u) :
    ((ofColoring G f).numColored v : ℝ) - ((ofColoring G f).numDistinct v : ℝ)
      = ((ofColoring G g).numColored v : ℝ) - ((ofColoring G g).numDistinct v : ℝ) := by
  rw [numColored_agree G h, numDistinct_agree G h]

end Work.Deep.Sparse
