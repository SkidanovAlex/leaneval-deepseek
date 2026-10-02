import Mathlib
import Submission.Work.Stems.Cubical.Kop

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `K`-operator on `1`-cubes, prescribed by its faces

The square `K₁(s)` associated with a `1`-cube `s : I → X` is a `2`-cube whose four faces are, in the
sign conventions of the cubical differential,
* the right edge `s`,
* the left edge the constant cube at the basepoint,
* the two horizontal edges the `K₀`-paths of the endpoints of `s`.
Its existence uses the simple connectivity of `X`.

Rather than constructing it by an explicit formula we describe it by its prescribed faces on the
boundary `∂I²` and use that this boundary loop is null-homotopic (simple connectivity), hence
extends to a `2`-cube.
-/

open scoped unitInterval Topology

namespace Work.Stems.Cubical

/-- A point of `I^1` (one coordinate). -/
abbrev I1 := unitInterval

/-- The constant `1`-cube at a point. -/
def constCube1 {X : Type} [TopologicalSpace X] (x : X) : CubeCM 1 X := ContinuousMap.const (IC 1) x

variable {X : Type} [TopologicalSpace X] [PathConnectedSpace X]

/-- The prescribed faces of the `K₁`-square:
`face 0 0 = const x₀`, `face 0 1 = s`, `face 1 0 = K₀(s(0))`, `face 1 1 = K₀(s(1))`. -/
def K1Faces (x₀ : X) (s : CubeCM 1 X) (F : CubeCM 2 X) : Prop :=
  faceCube (0 : Fin 2) 0 F = constCube1 x₀ ∧
  faceCube (0 : Fin 2) 1 F = s ∧
  faceCube (1 : Fin 2) 0 F = K0cube x₀ (s (icOnePt 0)) ∧
  faceCube (1 : Fin 2) 1 F = K0cube x₀ (s (icOnePt 1))

/-- The four edges of the square, glued into a single path from `x₀` to `x₀`, i.e. the boundary
loop.

Reading the boundary of `I^2` counterclockwise starting at `(0,0)` and splicing the prescribed
faces, the loop is `K₀(s(0)) · s · K₀(s(1))⁻¹` reindexed. -/
noncomputable def K1loop (x₀ : X) (s : CubeCM 1 X) : Path x₀ x₀ :=
  ((K0 x₀ (s (icOnePt 0))).trans (cubeToOnePath s)).trans (K0 x₀ (s (icOnePt 1))).symm

end Work.Stems.Cubical
