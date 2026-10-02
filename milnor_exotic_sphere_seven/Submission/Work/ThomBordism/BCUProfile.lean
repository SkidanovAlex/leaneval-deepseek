import Mathlib
import Submission.Work.ThomBordism.stdHalfBallModel

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The profile map of the boundary-collapse construction

This file fixes the *explicit* profile family used by the collapse map `Φ : W → ↥(stdHalfBall (n+1))`
of `boundarySign_boundaryChartAt_univ` (see `NOTE_BCU_PLAN3.md` §1).

In the normalised chart `eNorm` at the boundary point `y` (with `eNorm y = 0` and `eNorm ∂W` in the
hyperplane `{v | v 0 = 0}`), the collapse is

  `Φ z := profile e (χ z) (eNorm z)`   (`e` a small vector in the hyperplane, `χ` a bump),

and the profile is the three-phase family

* `t ≤ 1/2` — the constant `N := (1,0,…,0)`;
* `1/2 ≤ t ≤ 3/4` — the spherical phase `clamp (cos φ • (v/‖v‖) + sin φ • N)`, `φ` from `π/2` to `0`:
  for `v ∈ ∂H` the argument has norm exactly `1`, so the value is on the unit sphere;
* `3/4 ≤ t ≤ 1` — the shift phase `clamp (v + σ • e)`, `σ` from `1` to `0`: for `v ∈ ∂H` the argument
  stays in the hyperplane, so the value stays in the flat face; and `σ = 0` at `t = 1` is the
  identity.

The *only* points where the value can be `V := eNorm x₀` (or `0`) are the two small segments
`V − σ•e` and `−σ•e`; the bump `χ` is arranged (elsewhere) to be `1` on their preimages.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open scoped Manifold

namespace Work.ThomBordism.BCU

/-- The radial retraction of `EuclideanSpace ℝ (Fin N)` onto the closed unit ball. -/
noncomputable def clampBall {N : ℕ} (v : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  (min 1 ‖v‖⁻¹) • v

/-- The "north pole" `(1, 0, …, 0)`, on the boundary of the standard half-ball. -/
noncomputable def northPole (m : ℕ) : EuclideanSpace ℝ (Fin (m + 1)) :=
  Work.PTGeometric.consCLM m ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))

/-- The spherical phase: `φ = π/2` gives `N`, `φ = 0` gives the unit vector `v/‖v‖`. -/
noncomputable def sphPhase {m : ℕ} (φ : ℝ) (v : EuclideanSpace ℝ (Fin (m + 1))) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  clampBall (Real.cos φ • (‖v‖⁻¹ • v) + Real.sin φ • northPole m)

/-- The shift phase: `σ = 1` gives `v + e`, `σ = 0` gives `v`. -/
noncomputable def shiftPhase {m : ℕ} (σ : ℝ) (e v : EuclideanSpace ℝ (Fin (m + 1))) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  clampBall (v + σ • e)

/-- The profile family. -/
noncomputable def profile {m : ℕ} (e : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ)
    (v : EuclideanSpace ℝ (Fin (m + 1))) : EuclideanSpace ℝ (Fin (m + 1)) :=
  if t ≤ 1 / 2 then northPole m
  else if t ≤ 3 / 4 then sphPhase ((3 / 4 - t) * 2 * Real.pi) v
  else shiftPhase ((1 - t) * 4) e v

end Work.ThomBordism.BCU

namespace Work.ThomBordism.BCU

open Classical

/-- **The seam-free third phase.**  `p = 1` gives the normalised vector `v/‖v‖` (matching the
spherical phase at `φ = 0`), `p = 0` gives the identity `clampBall v`; the extra term `p(1−p)•e`
(for `p ∈ (0,1)`) moves the value off the ray through `V`, which is what confines the `V`-fibre. -/
noncomputable def shiftPhase2 {m : ℕ} (p : ℝ) (e v : EuclideanSpace ℝ (Fin (m + 1))) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  clampBall ((p / ‖v‖ + (1 - p)) • v + (p * (1 - p)) • e)

/-- **The seam-free profile.**  Same as `profile` but with `shiftPhase2`, so that the spherical and
the shift phases agree at `t = 3/4` and the collapse map is continuous. -/
noncomputable def profile2 {m : ℕ} (e : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ)
    (v : EuclideanSpace ℝ (Fin (m + 1))) : EuclideanSpace ℝ (Fin (m + 1)) :=
  if t ≤ 1 / 2 then northPole m
  else if t ≤ 3 / 4 then sphPhase ((3 / 4 - t) * 2 * Real.pi) v
  else shiftPhase2 ((1 - t) * 4) e v

/-- The ambient form of the collapse map: the profile of the normalised chart value with the bump
`χ`, and the constant `northPole` outside the chart.  (Membership in `↥(stdHalfBall (m+1))` is the
subject of a separate lemma.) -/
noncomputable def PhiE {m : ℕ} {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin (m + 1)))) (χ : X → ℝ)
    (evec : EuclideanSpace ℝ (Fin (m + 1))) (z : X) : EuclideanSpace ℝ (Fin (m + 1)) :=
  if z ∈ e.source then BCU.profile evec (χ z) (e z) else BCU.northPole m

/-- **The seam-free collapse map**: the profile `profile2` of the normalised chart value, with the
bump `χ`, and the constant `northPole` outside the chart. -/
noncomputable def PhiE2 {m : ℕ} {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin (m + 1)))) (χ : X → ℝ)
    (evec : EuclideanSpace ℝ (Fin (m + 1))) (z : X) : EuclideanSpace ℝ (Fin (m + 1)) :=
  if z ∈ e.source then BCU.profile2 evec (χ z) (e z) else BCU.northPole m

end Work.ThomBordism.BCU
