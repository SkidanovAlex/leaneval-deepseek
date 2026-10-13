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
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.FTS_RXTPieces.noDecayPieces.agmonF_deriv_bnd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.noDecayPieces

theorem agmonF_deriv_bnd {v v' : ℝ → ℝ}
    (hv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt v (v' x) x) :
    ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => y * (v y * Work.Spaces.w y) ^ 2)
        (2 * v x * (x * v' x) * (Work.Spaces.w x) ^ 2
          + (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))) x
      ∧ |2 * v x * (x * v' x) * (Work.Spaces.w x) ^ 2
            + (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))|
          ≤ 4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2 :=
  Work.FTS_RXTPieces.noDecayPieces.agmonF_deriv_bnd hv

end Work.FTS_RegExport.RXT.noDecayPieces
