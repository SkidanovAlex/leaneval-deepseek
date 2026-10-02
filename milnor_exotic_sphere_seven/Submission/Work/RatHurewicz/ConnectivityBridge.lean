import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cube-based connectivity versus `PathConnectedSpace`

Area **RATHUREWICZ** (`Submission/Work/RatHurewicz/`).  The connectivity hypotheses of the drive's
contract (`Work.Drive.RationalHurewiczStable`) are *cube-based*: `Subsingleton (HomotopyGroup (Fin i) X x₀)`
for `i < k`.  Most of the rest of the workspace states its results with Mathlib's
`PathConnectedSpace` / `SimplyConnectedSpace` (which are about `ZerothHomotopy` and the fundamental
groupoid).  This module provides the bridge in the easy direction:

* `Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero` — cube-based `π₀` triviality at a
  point implies `PathConnectedSpace X` (via `HomotopyGroup.pi0EquivZerothHomotopy` and
  `pathConnectedSpace_iff_zerothHomotopy`).

The corresponding statement for `π₁` (`simplyConnectedSpace_of_subsingleton`, needing the
conjugation step for the fundamental group) is reviewed and recorded in the README (§8.1); it is not
proved here.
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- **Cube-based `π₀`-triviality implies path connectedness.**  If every two elements of the
`0`-cube model of the homotopy group of `X` at `x₀` are equal, then `X` is path connected: the
quotient `HomotopyGroup (Fin 0) X x₀` is `ZerothHomotopy X = X / Joined` and the boundary condition
for the `0`-cube is vacuous. -/
theorem pathConnectedSpace_of_subsingleton_pi_zero {X : Type} [TopologicalSpace X] (x₀ : X)
    (h0 : Subsingleton (HomotopyGroup (Fin 0) X x₀)) : PathConnectedSpace X := by
  haveI := h0
  have hsub : Subsingleton (ZerothHomotopy X) :=
    (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x₀)).surjective.subsingleton
  exact pathConnectedSpace_iff_zerothHomotopy.mpr
    ⟨⟨ZerothHomotopy.mk x₀⟩, hsub⟩

end

end Work.RatHurewicz
