import Mathlib
import Submission.Work.StemsB.PiMap
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv

/-!
# Homeomorphism invariance of the homotopy groups

A homeomorphism `e : X ≃ₜ Y` is in particular a homotopy equivalence, and homotopy equivalences
induce group isomorphisms of the homotopy groups
(`Work.Stems.mulEquiv_of_homotopyEquiv`).  This file records the specialisation to homeomorphisms,
in the exact form needed by the STEMS-B area (with index type `Fin (n+1)` and base points `x`,
`e x`).
-/

namespace Work.StemsB

/-- **Homeomorphisms induce isomorphisms of homotopy groups.**  The isomorphism
`π_{n+1}(X, x) ≃* π_{n+1}(Y, e x)` is the one induced by postcomposition with `e`. -/
theorem pi_homeo_invariance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (n : ℕ) (x : X) :
    Nonempty (HomotopyGroup (Fin (n + 1)) X x ≃* HomotopyGroup (Fin (n + 1)) Y (e x)) :=
  Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin (n + 1)) e.toHomotopyEquiv x

end Work.StemsB
