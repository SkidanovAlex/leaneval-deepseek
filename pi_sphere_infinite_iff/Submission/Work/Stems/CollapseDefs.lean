import Mathlib

set_option synthInstance.maxHeartbeats 400000

/-!
# Definitions: the collapse `Iⁿ / ∂Iⁿ ≅ Sⁿ`

This file collects the definitions used to build an explicit quotient map `φ : Iⁿ → Sⁿ` which
sends the boundary `∂Iⁿ` of the cube to a single point `φ 0` and is injective off the boundary
(the target theorem is `Work.Stems.exists_collapsingMap`).

The construction goes through the one-point compactification of `ℝⁿ`:

* `cubeCoords : Iⁿ → ℝⁿ` is the "coordinate" map `q ↦ (y_i / √(1 - y_i²))_i` with
  `y_i = 2 q_i - 1`; it is the composition of the coordinatewise homeomorphisms
  `(-1,1) ≅ ℝ`, `t ↦ t/√(1-t²)`, hence a homeomorphism from the interior of the cube onto `ℝⁿ`,
  and it blows up at the boundary;
* `cubeToOnePoint` sends `∂Iⁿ` to `∞` and agrees with `cubeCoords` elsewhere, so it is a
  continuous surjection `Iⁿ → OnePoint ℝⁿ` (for `n ≥ 1`) whose fibres are the boundary and the
  singletons of the interior;
* `onePointSphereHomeo` is Mathlib's homeomorphism `OnePoint ℝⁿ ≃ₜ Sⁿ`, used to transport the
  collapse to the sphere.
-/

open scoped Topology unitInterval

namespace Work.Stems

noncomputable section

/-- The `n`-cube `Iⁿ = [0,1]ⁿ`. -/
abbrev CubeI (n : ℕ) : Type := Fin n → Set.Icc (0 : ℝ) 1

/-- The "coordinate" map `q ↦ (y_i / √(1-y_i²))_i`, `y_i = 2 q_i - 1`, from the cube to `ℝⁿ`.
On the interior of the cube it is a homeomorphism onto `ℝⁿ`; at the boundary it blows up. -/
def cubeCoords (n : ℕ) (q : CubeI n) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm
    (fun i => (2 * (q i : ℝ) - 1) / Real.sqrt (1 - (2 * (q i : ℝ) - 1) ^ 2))

/-- The collapse of the boundary `∂Iⁿ` to a point, viewed in the one-point compactification
`OnePoint ℝⁿ` of `ℝⁿ`. -/
def cubeToOnePoint (n : ℕ) (q : CubeI n) : OnePoint (EuclideanSpace ℝ (Fin n)) := by
  classical
  exact if q ∈ Cube.boundary (Fin n) then OnePoint.infty else (cubeCoords n q : OnePoint _)

/-- The standard homeomorphism `OnePoint ℝⁿ ≃ₜ Sⁿ` (one-point compactification = unit
sphere), Mathlib's `onePointEquivSphereOfFinrankEq` in the case `V = ℝⁿ`, `ι = Fin (n+1)`. -/
def onePointSphereHomeo (n : ℕ) :
    OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin n)) (ι := Fin (n + 1)) (by simp)

end

end Work.Stems
