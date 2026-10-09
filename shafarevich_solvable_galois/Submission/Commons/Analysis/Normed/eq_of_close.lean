import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Normed

lemma eq_of_close {L : Type*} [NormedField L] [IsUltrametricDist L] {α α' β : L} {δ : ℝ}
    (hδ : δ ≤ ‖α - α'‖) (h1 : ‖α - β‖ < δ) (h2 : ‖α' - β‖ < δ) : α = α' := by
  exfalso
  have h : ‖α - α'‖ < δ := by
    calc ‖α - α'‖ = dist α α' := (dist_eq_norm α α').symm
      _ ≤ max (dist α β) (dist β α') := IsUltrametricDist.dist_triangle_max α β α'
      _ = max ‖α - β‖ ‖α' - β‖ := by
            rw [dist_eq_norm α β, dist_comm β α', dist_eq_norm α' β]
      _ < δ := max_lt h1 h2
  linarith

end Commons.Analysis.Normed