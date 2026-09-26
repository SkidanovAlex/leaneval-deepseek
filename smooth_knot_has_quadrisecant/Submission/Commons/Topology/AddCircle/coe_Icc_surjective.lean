import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Instances.AddCircle.Defs

namespace Commons.Topology.AddCircle

theorem coe_Icc_surjective (p a : ℝ) (hp : 0 < p) :
    ((↑) : ℝ → AddCircle p) '' Set.Icc a (a + p) = Set.univ := by
  have : Fact (0 < p) := ⟨hp⟩
  exact _root_.AddCircle.coe_image_Icc_eq p a

end Commons.Topology.AddCircle