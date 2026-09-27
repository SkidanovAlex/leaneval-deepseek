import Mathlib
import Submission.Work.Conn.PathConnected.pathConnectedSpace_of_homotopyEquiv_sphere

namespace Work.Compact.Connected

/-- A space homotopy equivalent to `𝕊ⁿ` (`n ≥ 1`) is connected.

Route: `𝕊ⁿ` is path connected for `n ≥ 1`, and path connectedness is a homotopy
invariant preserved by a homotopy equivalence `M ≃ₕ 𝕊ⁿ`
(`Work.Conn.PathConnected.pathConnectedSpace_of_homotopyEquiv_sphere`). A path connected
space is connected (`PathConnectedSpace.connectedSpace`). -/
theorem connectedSpace_of_homotopyEquiv_sphere (n : ℕ) (hn : 1 ≤ n) {M : Type} [TopologicalSpace M]
    (e : ContinuousMap.HomotopyEquiv M
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) : ConnectedSpace M := by
  have h : PathConnectedSpace M :=
    Work.Conn.PathConnected.pathConnectedSpace_of_homotopyEquiv_sphere hn e
  exact h.connectedSpace

end Work.Compact.Connected
