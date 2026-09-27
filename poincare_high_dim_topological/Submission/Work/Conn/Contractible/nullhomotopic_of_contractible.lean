import Mathlib
import Submission.Work.Conn.Basic

namespace Work.Conn.Contractible

open ContinuousMap

/-- Any map into a contractible space is null-homotopic: `id_nullhomotopic` gives a homotopy from
the identity of `Y` to a constant map, and `ContinuousMap.Nullhomotopic.comp_left` pushes it
along `f`. -/
theorem nullhomotopic_of_contractible {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace Y] (f : C(X, Y)) : f.Nullhomotopic :=
  (id_nullhomotopic Y).comp_left f

end Work.Conn.Contractible
