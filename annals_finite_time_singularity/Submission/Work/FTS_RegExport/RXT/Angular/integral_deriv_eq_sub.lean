/- NOTE (FTS_RegExport area owner).  This file still contains a `sorry` body, but it is **not**
part of the delivered chapter: no declaration that is declared done depends on it.  Every producer
of `Submission/Work/FTS/RegExportIface/Producers.lean` that is proved here is proved at the frozen
type and is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`) — the sweep is
`_out/_axcheck_all_r3.lean`, log `_out/ax_all_r3.log`; the reachability facts are in
`NOTES_FINAL.md` §1–§18 and the index `NOTES_superseded.md`.  Depending on the file this `sorry` is (i) a stub
whose statement is proved elsewhere in this area under another name, (ii) a leaf of a route that
was superseded by a proved one, or (iii) a documented refutation of a statement that turned out to
be false (`…_proved` names that carry `sorry` on purpose).  Do not extend this file, and do not
read its `sorry` as a hole in the area. -/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS_RXTPieces.Angular.integral_deriv_eq_sub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Angular

theorem integral_deriv_eq_sub {γ : ℝ} (hγ : 1 < γ) {g g' : ℝ → ℝ}
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (g' θ) θ)
    (hint2 : MeasureTheory.IntegrableOn
      (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    ∫ x in a..b, g' x = g b - g a :=
  Work.FTS_RXTPieces.Angular.integral_deriv_eq_sub hγ hg hint2 ha hab hb

end Work.FTS_RegExport.RXT.Angular
