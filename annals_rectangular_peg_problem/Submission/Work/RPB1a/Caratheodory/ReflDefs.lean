import Mathlib

/-!
# Reflection of a holomorphic function in the unit circle

This file sets up the single vocabulary used by `not_eqOn_const_sphere_of_injOn`: the
*reflection* of the function `f - a` in the unit circle.  Inside the closed unit disc it agrees
with `f - a`; outside it is `conj (f (1 / conj z)) - conj a`, which is holomorphic on the exterior
whenever `f` is holomorphic on the unit disc.  If `f = a` on an arc of the unit circle, the two
pieces glue continuously across that arc and (by Painlevé removability across the circle,
`Submission.Work.RPB1a.differentiableOn_of_compl_sphere`) the reflection is holomorphic there as
well; the identity theorem then forces `f ≡ a` on the whole disc.
-/

namespace Work.RPB1a.Caratheodory

open Complex Set Metric
open scoped ContDiff Real Topology ComplexConjugate

/-- The reflection of `f - a` in the unit circle: `f z - a` inside the closed unit disc and
`conj (f (1 / conj z)) - conj a` outside it. -/
noncomputable def diskReflect (f : ℂ → ℂ) (a : ℂ) (z : ℂ) : ℂ :=
  if ‖z‖ ≤ 1 then f z - a else conj (f (1 / conj z)) - conj a

@[simp]
lemma diskReflect_of_le_one {f : ℂ → ℂ} {a z : ℂ} (hz : ‖z‖ ≤ 1) :
    diskReflect f a z = f z - a :=
  if_pos hz

lemma diskReflect_of_one_lt {f : ℂ → ℂ} {a z : ℂ} (hz : 1 < ‖z‖) :
    diskReflect f a z = conj (f (1 / conj z)) - conj a :=
  if_neg (not_le.mpr hz)

/-- The formula defining the reflection outside the unit circle, extended to all of `ℂ`. -/
noncomputable def diskReflectOuter (f : ℂ → ℂ) (a : ℂ) (z : ℂ) : ℂ :=
  conj (f (1 / conj z)) - conj a

lemma diskReflect_eq_outer {f : ℂ → ℂ} {a z : ℂ} (hz : 1 < ‖z‖) :
    diskReflect f a z = diskReflectOuter f a z :=
  diskReflect_of_one_lt hz

end Work.RPB1a.Caratheodory
