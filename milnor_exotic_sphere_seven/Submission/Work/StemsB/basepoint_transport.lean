import Mathlib
import Submission.Work.Stems.basepoint_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Change of basepoint for the homotopy groups (STEMS-B interface)

For a path `γ : Path x y` in a topological space `X` and any `n`, the homotopy groups
`π_{n+1}(X, x)` and `π_{n+1}(X, y)` are isomorphic as groups; the isomorphism is realised by
moving the basepoint of the generalized cubes `I^{n+1} → X` along `γ` (for `n = 0` this is the
classical conjugation of loops, and for `n ≥ 1` it is the trivial isomorphism between the abelian
groups `π_{n+1}`).

This is the specialisation to `N = Fin (n + 1)` of the general basepoint-change theorem
`Work.Stems.basepoint_iso` proved in the STEMS area: for `N` decidable and nonempty, a path
`p : Path x y` yields `Nonempty (HomotopyGroup N X x ≃* HomotopyGroup N X y)`.  That theorem is
built from the collar construction (`Work.Stems.Collar.collar`, filling the collar of the cube
with `γ` and shrinking the interior), so we simply quote it here.
-/

namespace Work.StemsB

theorem basepoint_transport {X : Type*} [TopologicalSpace X] {x y : X} (n : ℕ) (γ : Path x y) :
    Nonempty (HomotopyGroup (Fin (n + 1)) X x ≃* HomotopyGroup (Fin (n + 1)) X y) :=
  Work.Stems.basepoint_iso (N := Fin (n + 1)) γ

end Work.StemsB
