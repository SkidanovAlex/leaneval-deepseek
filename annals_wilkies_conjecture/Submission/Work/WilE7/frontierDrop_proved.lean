/-
  WilE7: the fibrewise frontier dimension drop, unconditionally.

  `Work.WilE7.FrontierDrop` (`Submission/Work/WilE7/FiberCutInputs.lean`) is the geometric input
  that BV's Proposition 9 uses for the *bad cells*: a `Good` stratum lying in the fibrewise frontier
  `fiberClosure S.X.set \ S.X.set` of another `Good` stratum has strictly larger fibre codimension
  (`S.j < S'.j`).  It is the formal counterpart of "the count-change loci are thin", and it is what
  makes the secondary (dimension) induction of the assembly applicable to the base cells that the
  frontier projections force the decomposition to contain.

  The chain now available in the workspace is

  * `Work.WilE7.DimDrop` — the classical dimension drop for real *analytic* level sets, in chart
    form (`Submission/Work/WilE7/FrontierDropFromDimDrop.lean`);
  * `Work.WilE7.FrontierCS.dimDrop_proved : DimDrop` — proved from the delivered C4a curve
    selection (`Submission/Work/WilE7/FrontierCS/Main.lean`, sorry-free);
  * `Work.WilE7.frontierDrop_of_dimDrop : DimDrop → FrontierDrop` — the reduction
    (`FrontierDropFromDimDrop.lean`, sorry-free).

  This file only performs the composition, so that the assembly can import one name.
-/
import Mathlib
import Submission.Work.WilE7.FrontierDropFromDimDrop
import Submission.Work.WilE7.FrontierCS.Main

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7

/-- **The fibrewise frontier dimension drop, unconditionally.**

A `Good` stratum `S'` whose set lies in the fibrewise frontier of a `Good` stratum `S` (and is
nonempty) has strictly larger fibre codimension: `S.j < S'.j`.  Proved from `DimDrop` (the
classical Łojasiewicz/analytic curve-selection dimension drop, delivered by the C4a chain in
`Work.WilE7.FrontierCS`) via `frontierDrop_of_dimDrop`. -/
theorem frontierDrop_proved : FrontierDrop :=
  frontierDrop_of_dimDrop FrontierCS.dimDrop_proved

end Work.WilE7
