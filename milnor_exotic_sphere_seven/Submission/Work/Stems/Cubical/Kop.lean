import Mathlib
import Submission.Work.Stems.Cubical.CubeFace

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `K`-operator of the elementary Hurewicz proof (first steps)

Following Hutchings' cubical proof of the Hurewicz isomorphism theorem, `K` pushes the boundary of
a cube into the basepoint: `K` of a `0`-cube (a point `x`) is a path from the basepoint to `x`, and
`K` of a `1`-cube (a path `s`) is a square filling the loop made of the basepoint, the path and the
two `K`-paths of the endpoints of `s`.  The existence of the latter uses simple connectivity of `X`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Cubical

/-- The `n`-cube of `X`, as a continuous map. -/
abbrev CubeCM (n : ℕ) (X : Type) [TopologicalSpace X] := C(IC n, X)

/-- The standard identification `I^1 ≅ [0,1]`. -/
def icOneToUnit : C(IC 1, unitInterval) where
  toFun := fun t => t 0
  continuous_toFun := continuous_apply 0

/-- The inverse identification `[0,1] ≅ I^1`. -/
def unitToIcOne : C(unitInterval, IC 1) where
  toFun := fun b => fun _ => b
  continuous_toFun := by fun_prop

@[simp]
theorem unitToIcOne_apply (b : unitInterval) : unitToIcOne b = fun _ : Fin 1 => b := rfl

/-- Points of `I^1` with coordinate `0` equal to `b`. -/
def icOnePt (b : unitInterval) : IC 1 := fun _ => b

/-- The `K`-operator on `0`-cubes: a path from the basepoint to the point. -/
noncomputable def K0 {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X) (x : X) :
    Path x₀ x :=
  (PathConnectedSpace.joined x₀ x).some

/-- `K0` reinterpreted as a continuous map `I^1 → X`. -/
noncomputable def K0cube {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X)
    (x : X) : CubeCM 1 X :=
  (K0 x₀ x).toContinuousMap.comp icOneToUnit

theorem K0cube_pt {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (x₀ x : X)
    (b : unitInterval) : K0cube x₀ x (icOnePt b) = K0 x₀ x b := by
  simp [K0cube, icOnePt, icOneToUnit]

/-- The standard identification `I^2 ≅ [0,1] × [0,1]`. -/
def icTwoToProd : C(IC 2, unitInterval × unitInterval) where
  toFun := fun t => (t 0, t 1)
  continuous_toFun := Continuous.prodMk (continuous_apply 0) (continuous_apply 1)

/-- A `1`-cube reindexed as a path. -/
def cubeToOnePath {X : Type} [TopologicalSpace X] (s : CubeCM 1 X) :
    Path (s (icOnePt 0)) (s (icOnePt 1)) :=
  ⟨s.comp unitToIcOne, by rfl, by rfl⟩

/-- The `K`-operator on `1`-cubes: a square filling the loop made of the basepoint, the path `s` and
the two `K`-paths of the endpoints of `s`.

It is built from a homotopy, relative to the endpoints, between the path `K₀(s(1))` and the
concatenation `K₀(s(0)) · s` (both from the basepoint to the endpoint `s(1)`), which exists because
`X` is simply connected. -/
noncomputable def K1 {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x₀ : X)
    (s : CubeCM 1 X) : CubeCM 2 X :=
  let p : Path x₀ (s (icOnePt 1)) := K0 x₀ (s (icOnePt 1))
  let q : Path x₀ (s (icOnePt 1)) := (K0 x₀ (s (icOnePt 0))).trans (cubeToOnePath s)
  let H : Path.Homotopy p q := (SimplyConnectedSpace.paths_homotopic p q).some
  H.toContinuousMap.comp icTwoToProd

end Work.Stems.Cubical
