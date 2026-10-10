import Mathlib
import Submission.Work.MotAS.ASLink
import Submission.Work.MotAS.ChartDefs
import Submission.Work.MotK.KleinData
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The stereographic layer of the AS Crauder–Katz chart

`Submission/Work/MotV5` (route V, characteristic `5`).  This file proves the two *stereographic
identities* of the AS link,

* `kleinQAS_stereoAS` : `q^AS(y(v)) = q^AS(v)² · q^AS(p)`, and
* `kleinBilinAS_stereoAS` : `b^AS(p, y(v)) = 2 q^AS(v) q^AS(p) − b^AS(p,v)²`,

where `y(v) = q^AS(v)·p − b^AS(p,v)·v` is the inverse stereographic projection (`MotAS`).  Both are
*characteristic-free* polynomial identities in the coordinates of `p` and `v` (no `w`, no
transport), so they need no hypothesis and are independent of the two big secant transports.

Proof note: unfolding `kleinQAS`/`kleinBilinAS` at a *function* argument needs very generous
`maxRecDepth`/`maxHeartbeats` (the `Pi`-instances make the elaborator's `isDefEq` deep); the values
below were found by experiment.  Together with the values of the twisted Pfaffians and of the
twisted secant at the stereographic point `288 · e₀` (dispatched separately) this closes the
stereographic layer of `MotAS/ASLink.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

namespace Work.MotV5.ASChart

open Work.MotAS

variable {R : Type*} [CommRing R]

/-- The constant vector `288 · e₀` (the stereographic point, in coordinates). -/
def pt288 : Fin 5 → R := ![288, 0, 0, 0, 0]

/-- `pt288` in the form in which `MotAS.stereoPt` is known. -/
theorem pt288_eq_if : pt288 (R := R) = fun i => if i = 0 then (288 : R) else 0 := by
  funext i
  fin_cases i <;> rfl

/-- `pt288` is `MotAS.stereoPt` (`MotAS.stereoPt_eq`). -/
theorem pt288_eq_stereoPt (w : R) : pt288 (R := R) = Work.MotAS.stereoPt w := by
  rw [Work.MotAS.stereoPt_eq (R := R) w]
  exact (pt288_eq_if (R := R)).trans rfl

/-- **The quadric on the stereographic image:** `q^AS(y(v)) = q^AS(v)² · q^AS(p)`. -/
theorem kleinQAS_stereoAS (a b : R) (p v : Fin 5 → R) :
    kleinQAS a b (kleinStereoAS a b p v) = kleinQAS a b v ^ 2 * kleinQAS a b p := by
  have h : kleinStereoAS a b p v
      = fun i => kleinQAS a b v * p i - kleinBilinAS a b p v * v i := rfl
  rw [h]
  simp only [kleinBilinAS, kleinQAS, Pi.add_apply]
  refl_ring1

/-- **The polar identity on the stereographic image:**
`b^AS(p, y(v)) = 2 q^AS(v) q^AS(p) − b^AS(p,v)²`. -/
theorem kleinBilinAS_stereoAS (a b : R) (p v : Fin 5 → R) :
    kleinBilinAS a b p (kleinStereoAS a b p v)
      = 2 * kleinQAS a b v * kleinQAS a b p - kleinBilinAS a b p v ^ 2 := by
  have h : kleinStereoAS a b p v
      = fun i => kleinQAS a b v * p i - kleinBilinAS a b p v * v i := rfl
  rw [h]
  simp only [kleinBilinAS, kleinQAS, Pi.add_apply]
  ring_nf

end Work.MotV5.ASChart
