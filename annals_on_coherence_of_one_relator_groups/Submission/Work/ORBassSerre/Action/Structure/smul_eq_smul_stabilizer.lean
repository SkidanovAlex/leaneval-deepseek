import Mathlib
import Submission.Work.ORBassSerre.Action.Basic

namespace Work.ORBassSerre.Action.Structure

theorem smul_eq_smul_stabilizer {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V] (u : Quiver.Total V) (g h : G) : g • u = h • u ↔ h⁻¹ * g ∈ MulAction.stabilizer G u := by
  rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]

end Work.ORBassSerre.Action.Structure
