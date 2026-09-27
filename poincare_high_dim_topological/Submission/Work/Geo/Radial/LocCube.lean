import Submission.Work.Metric.locCube_open_subset
import Submission.Work.Metric.locCube_chartedSpace

/-!
# `LocCube` for open subspaces and for charted spaces

Area `A7` (`Geo/Radial+Conn-rel`).  The blueprint asks for two lemmas about the frozen
vocabulary `PL.LocCube n M` ("every point lies in the image of the open `1/2`-cube of a cube
chart").  Both are already proved, with exactly these statements, in the `Metric` area
(`Submission/Work/Metric/locCube_open_subset.lean`, `locCube_chartedSpace.lean`); this file
re-exports them under the names the blueprint uses, so that consumers of `Work.Geo.Radial` can
reach them with one import.
-/

open Set Metric

namespace Work.Geo.Radial

/-- Blueprint A7 (`LocCube.open_subset`): a space with local cube charts has local cube charts in
each of its open subspaces. -/
theorem LocCube_open_subset {n : ℕ} {M : Type*} [TopologicalSpace M] {O : Set M}
    (h : PL.LocCube n M) (hO : IsOpen O) : PL.LocCube n ↥O :=
  Work.Metric.locCube_open_subset n M h O hO

/-- Blueprint A7 (`LocCube.of_chartedSpace`): a charted space over `ℝⁿ` has local cube charts. -/
theorem LocCube_of_chartedSpace {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : PL.LocCube n M :=
  Work.Metric.locCube_chartedSpace n M

end Work.Geo.Radial
