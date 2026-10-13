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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RXTPieces.noDecayPieces.le_sub_setIntegral_of_deriv_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.noDecayPieces

theorem le_sub_setIntegral_of_deriv_le {F F' G : ℝ → ℝ}
    (hcont : ContinuousOn F (Set.Ioi (0 : ℝ)))
    (hmeas : MeasureTheory.AEStronglyMeasurable F' (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt F (F' x) x)
    (hbd : ∀ x ∈ Set.Ioi (0 : ℝ), |F' x| ≤ G x)
    (hGint : MeasureTheory.IntegrableOn G (Set.Ioi 0))
    (hGnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)] G)
    {z : ℝ} (hz : 0 < z) :
    ∀ x, z ≤ x → F z - (∫ t in Set.Ioi 0, G t) ≤ F x :=
  Work.FTS_RXTPieces.noDecayPieces.le_sub_setIntegral_of_deriv_le
    hcont hmeas hderiv hbd hGint hGnn hz

end Work.FTS_RegExport.RXT.noDecayPieces
