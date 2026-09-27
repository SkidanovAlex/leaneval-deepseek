import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers
import Submission.Work.Final.All
import Submission.Work.Engulf.EngulfOfForms

open Metric (sphere)
open ContinuousMap

universe u

namespace Submission

/-- **Generalized topological Poincaré conjecture in dimensions `≥ 5`** (Smale 1961; topological
case Newman 1966 / Connell 1967), the challenge statement.

This is the target of the final assembly in `Submission/Work/Final`: it is proved as
`Submission.poincare_high_dim_topological_of_inputs` modulo the single remaining holder
`Work.Final.FinalInputs n` (Newman's engulfing theorem), which the `Submission/Work/Engulf` area
owns.  Once `FinalInputs n` is inhabited (equivalently: once `Work.Engulf.engulf_of_forms` has its
four forms), the proof below becomes
`exact poincare_high_dim_topological_of_inputs _h5 _h (a proof of FinalInputs n)`. -/
theorem poincare_high_dim_topological {n : ℕ} (_h5 : 5 ≤ n)
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (_h : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  exact Work.Final.poincare_high_dim_topological_of_inputs _h5 _h
    (Work.Final.FinalInputs.ofEngulf (Work.Engulf.engulf_unconditional n))

/-- **The final assembly**, in the exact shape of the challenge but with the single holder
`Work.Final.FinalInputs n` as an extra argument: `I.engulf` is Newman's engulfing theorem
(`E0`, the form `Work.Cells.Connell.EngulfForm` consumed by the Connell cell-count reduction).

Everything else is discharged: compactness (`Work.Compact`), the compatible metric, the local cube
charts and a finite cell cover (`Work.Metric`), the connectivity (`Work.Conn`), the dual stretch and
the skeleta (`Work.Geo.DualStretch`, through `Work.Final.skeletonData`), the cube triangulation and
the affine invariance of `PL.DomDim` (`Work.Final.Forms`), the radial data `G8`/`G9`/`C0`/`C1`
(`Work.Geo.Radial`), Brown's criterion (`Work.Brown`) and the one-point compactification endgame
(`Work.Endgame`).

The theorem is proved for `M : Type*` in an arbitrary universe (the challenge's). -/
theorem poincare_high_dim_topological_of_inputs {n : ℕ} (h5 : 5 ≤ n)
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (h : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (I : Work.Final.FinalInputs.{u} n) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  Work.Final.poincare_high_dim_topological_of_inputs h5 h I

end Submission
