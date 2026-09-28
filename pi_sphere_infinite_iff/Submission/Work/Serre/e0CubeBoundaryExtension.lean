import Mathlib
import Submission.Work.Stems.exists_collapsingMap
import Submission.Work.ThomBordism.TwoSet.ConeDescent
import Submission.Work.Stems.subsingleton_homotopyGroup_change_basepoint
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.ThomBordism.TwoSet.Push

namespace Work.Serre

open scoped Topology unitInterval

/-- **Every map on the boundary of a cube extends over the cube, when `π_{m-1}` vanishes.**

Let `m ≥ 2`, let `X` be path connected and suppose `π_{m-1}(X,y)` is trivial for every basepoint
`y` (the cube model: `Subsingleton (HomotopyGroup (Fin (m-1)) X y)`).  Then every continuous map
on the boundary `∂I^m ≅ S^{m-1}` of the `m`-cube extends to the cube `I^m`.

This is `Work.ThomBordism.TwoSet.exists_extension_succ` at cube dimension `m = (m-1) + 1`: it
proves the extension for `π_{m-1}`-trivial targets without any other connectivity hypothesis
(the base case `m = 1` uses only path connectedness). -/
theorem e0CubeBoundaryExtension {m : ℕ} (hm : 2 ≤ m) {X : Type} [TopologicalSpace X]
    (hpath : PathConnectedSpace X)
    (hπ : ∀ y : X, Subsingleton (HomotopyGroup (Fin (m - 1)) X y))
    (f : C(↥(Cube.boundary (Fin m)), X)) :
    ∃ g : C(Fin m → unitInterval, X), ∀ z : ↥(Cube.boundary (Fin m)), g z.1 = f z := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hπ' : ∀ y : X, Subsingleton (HomotopyGroup (Fin k) X y) := fun y => by simpa using hπ y
  exact Work.ThomBordism.TwoSet.exists_extension_succ (Z := X) hπ' f

end Work.Serre
