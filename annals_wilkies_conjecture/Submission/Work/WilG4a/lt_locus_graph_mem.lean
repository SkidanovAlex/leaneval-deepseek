import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.fiber_defs
import Submission.Work.WilG4a.setOf_lt_graph_mem
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG0.API
import Submission.Work.WilG1.Calc.lt_mem

namespace Work.WilG4a

/-- The strict comparison locus `{l | lo l < hi l}` of two functions whose graphs are
`Ω`-definable is again `Ω`-definable, with a format depending only on `F` and `p`, and a
degree that is a fixed polynomial in `D` (valid for every `r`).

This is exactly `Work.WilG4a.setOf_lt_graph_mem` with `lo`/`hi` renamed from `f`/`g`.  The
underlying construction lifts `graphOf lo` into the ambient space `ℝ^{p+2}` with coordinates
`(l, y, t)` (so that `y = lo l`), pulls back `graphOf hi` along `iota1 p` (so that `t = hi l`),
intersects with the strict half-space `y < t`, and projects out `t` and then `y`; the result is
`{l | lo l < hi l}`. -/
theorem lt_locus_graph_mem (S : WilkiesDesign.SOMin) (p F : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) {lo hi : (Fin p → ℝ) → ℝ},
        WilkiesDesign.graphOf lo ∈ S.Ω F D (p + 1) →
        WilkiesDesign.graphOf hi ∈ S.Ω F D (p + 1) →
        {l : Fin p → ℝ | lo l < hi l} ∈ S.Ω a (MvPolynomial.eval ![D, r] b) p :=
  setOf_lt_graph_mem S p F

end Work.WilG4a
