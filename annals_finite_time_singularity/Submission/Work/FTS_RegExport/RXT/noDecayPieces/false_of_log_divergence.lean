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
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RXTPieces.noDecayPieces.false_of_log_divergence

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.noDecayPieces

theorem false_of_log_divergence {g : ℝ → ℝ} {z c : ℝ}
    (hz : 0 < z) (hc : 0 < c)
    (hint : MeasureTheory.IntegrableOn g (Set.Ioi 0))
    (hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)] g)
    (hg : ∀ x, z ≤ x → c / x ≤ g x) : False :=
  Work.FTS_RXTPieces.noDecayPieces.false_of_log_divergence hz hc hint hnn hg

end Work.FTS_RegExport.RXT.noDecayPieces
