import Mathlib
import Submission.Work.Core.torusMap_eq_iff

/-!
# The waypoint design for the embedded disc of `Work.Drive.EpsForm.DatumCore`

Constituent functions of the explicit candidate disc (see the session notes in
`Submission/Work/Drive/EpsForm/work_datumCore.lean`): the chord levels `σ₁ < σ₂`, the core level
`τ`, the tube-angle offset `δ` and the tube-angle lift `phLift` along the chords, together with
their elementary properties (endpoint values, positivity on the open range, ordering, and the
class condition `phLift v0 - phLift u0 = (v0 - u0) - 2π` which makes `κ` inessential).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.EpsForm

/- ## The constituent functions of the waypoint design (Section 6 of the notes) -/

noncomputable section

/-- Left end of the chord range. -/
def u0 : ℝ := -(2 * Real.pi) / 3

/-- Right end of the chord range. -/
def v0 : ℝ := (2 * Real.pi) / 3

/-- The bump `sin (π (t - u0)/(v0 - u0))`: positive on `(u0, v0)`, zero at the ends. -/
def bump (t : ℝ) : ℝ := Real.sin (Real.pi * (t - u0) / (v0 - u0))

/-- The lower chord level `σ₁`. -/
def sig1 (t : ℝ) : ℝ := 1 - (1 / 4) * bump t

/-- The upper chord level `σ₂`. -/
def sig2 (t : ℝ) : ℝ := 1 - (1 / 8) * bump t

/-- The level `τ` at which the profile crosses the core circle (`ρ = 0`). -/
def tauP (t : ℝ) : ℝ := (1 + sig2 t) / 2

/-- The tube-angle offset `δ` between the two chords: zero at the ends of the range. -/
def dlt (t : ℝ) : ℝ := (1 / 2) * bump t

/-- The lift of the tube angle along the chords; it satisfies
`phLift v0 - phLift u0 = (v0 - u0) - 2π`, i.e. the chords have tube-angle class `-1`. -/
def phLift (t : ℝ) : ℝ := t - 2 * Real.pi * (t - u0) / (v0 - u0)

theorem v0_sub_u0 : v0 - u0 = 4 * Real.pi / 3 := by
  unfold u0 v0; ring

theorem bump_u0 : bump u0 = 0 := by
  unfold bump; rw [sub_self, mul_zero, zero_div]; exact Real.sin_zero

theorem bump_v0 : bump v0 = 0 := by
  have hne : v0 - u0 ≠ 0 := by rw [v0_sub_u0]; positivity
  unfold bump
  rw [mul_div_cancel_right₀ Real.pi hne, Real.sin_pi]

theorem bump_pos {t : ℝ} (hu : u0 < t) (hv : t < v0) : 0 < bump t := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlen : (0 : ℝ) < v0 - u0 := by rw [v0_sub_u0]; positivity
  have hx0 : (0 : ℝ) < Real.pi * (t - u0) / (v0 - u0) :=
    div_pos (mul_pos hπ (by linarith)) hlen
  have hx1 : Real.pi * (t - u0) / (v0 - u0) < Real.pi := by
    rw [div_lt_iff₀ hlen]; nlinarith [hπ]
  exact Real.sin_pos_of_pos_of_lt_pi hx0 hx1

theorem sig1_u0 : sig1 u0 = 1 := by unfold sig1; rw [bump_u0]; ring
theorem sig1_v0 : sig1 v0 = 1 := by unfold sig1; rw [bump_v0]; ring
theorem sig2_u0 : sig2 u0 = 1 := by unfold sig2; rw [bump_u0]; ring
theorem sig2_v0 : sig2 v0 = 1 := by unfold sig2; rw [bump_v0]; ring
theorem dlt_u0 : dlt u0 = 0 := by unfold dlt; rw [bump_u0]; ring
theorem dlt_v0 : dlt v0 = 0 := by unfold dlt; rw [bump_v0]; ring

theorem phLift_u0 : phLift u0 = u0 := by
  unfold phLift; rw [sub_self, mul_zero, zero_div, sub_zero]

theorem phLift_v0 : phLift v0 = v0 - 2 * Real.pi := by
  have hne : v0 - u0 ≠ 0 := by rw [v0_sub_u0]; positivity
  unfold phLift
  rw [mul_div_cancel_right₀ (2 * Real.pi) hne]

/-- The class condition for `κ`: the tube angle along the chords drops by a full turn, so the
two chords have the same class `(0,-1)` and their union has winding `(0,0)`. -/
theorem phLift_class : phLift v0 - phLift u0 = (v0 - u0) - 2 * Real.pi := by
  rw [phLift_u0, phLift_v0]; ring

/-- On the open chord range the bump is positive, hence `σ₁ < σ₂`. -/
theorem sig1_lt_sig2 {t : ℝ} (hu : u0 < t) (hv : t < v0) : sig1 t < sig2 t := by
  have hb := bump_pos hu hv
  unfold sig1 sig2; linarith

/-- `σ₂ < τ < 1` on the open chord range. -/
theorem sig2_lt_tauP {t : ℝ} (hu : u0 < t) (hv : t < v0) : sig2 t < tauP t := by
  have hb := bump_pos hu hv
  have h : sig2 t < 1 := by unfold sig2; linarith
  unfold tauP; linarith

theorem tauP_lt_one {t : ℝ} (hu : u0 < t) (hv : t < v0) : tauP t < 1 := by
  have hb := bump_pos hu hv
  have h : sig2 t < 1 := by unfold sig2; linarith
  unfold tauP; linarith

theorem sig1_lt_one {t : ℝ} (hu : u0 < t) (hv : t < v0) : sig1 t < 1 := by
  have hb := bump_pos hu hv
  unfold sig1; linarith

end

end Work.Drive.EpsForm
open Classical

namespace Work.Drive.EpsForm

noncomputable section

/-! ## The waypoint profile and the candidate disc map

The profile of the candidate disc at azimuth `t` is the polyline through the tube-coordinate
waypoints `W₁ = (-2,0)` (the centre, `s = 0`), the two chord points `W₂, W₃` (at `s = σ₁, σ₂`),
the core point `W₄ = (0,0)` (at `s = τ`) and the boundary point `W₅ = (cos t, sin t)` (at
`s = 1`).  Outside the chord range the chord waypoints are replaced by the boundary point and
the levels are clamped to `1`, which makes the profile the straight segment from `(-2,0)` to
`(cos t, sin t)` — the cone's profile, whose only interior intersection with the unit circle is
`3/(5+4cos t)`, which is `≥ 1` exactly outside the chord range.  Because `phLift u0 = u0` and
`phLift v0 = v0 - 2π ≡ v0`, the definition is continuous across `t = u0` and `t = v0`. -/

/-- The chord range predicate. -/
def inRange (t : ℝ) : Prop := u0 ≤ t ∧ t ≤ v0

instance (t : ℝ) : Decidable (inRange t) := Classical.propDecidable _

/-- The (clamped) lower chord level. -/
def sig1c (t : ℝ) : ℝ := if inRange t then sig1 t else 1

/-- The (clamped) upper chord level. -/
def sig2c (t : ℝ) : ℝ := if inRange t then sig2 t else 1

/-- The (clamped) core level. -/
def tauc (t : ℝ) : ℝ := if inRange t then tauP t else 1

/-- The first waypoint (the centre). -/
def W1 : ℝ × ℝ := (-2, 0)

/-- The fourth waypoint (the core circle). -/
def W4 : ℝ × ℝ := (0, 0)

/-- The fifth waypoint (the boundary point). -/
def W5c (t : ℝ) : ℝ × ℝ := (Real.cos t, Real.sin t)

/-- The second waypoint: the lower chord point inside the range, the boundary point outside. -/
def W2c (t : ℝ) : ℝ × ℝ :=
  if inRange t then (Real.cos (phLift t), Real.sin (phLift t)) else W5c t

/-- The third waypoint. -/
def W3c (t : ℝ) : ℝ × ℝ :=
  if inRange t then (Real.cos (phLift t + dlt t), Real.sin (phLift t + dlt t)) else W5c t

/-- Linear interpolation between two waypoints. -/
def seg (P Q : ℝ × ℝ) (a b s : ℝ) : ℝ × ℝ :=
  ((1 - (s - a) / (b - a)) * P.1 + ((s - a) / (b - a)) * Q.1,
   (1 - (s - a) / (b - a)) * P.2 + ((s - a) / (b - a)) * Q.2)

/-- **The waypoint profile** in tube coordinates: the polyline through the five waypoints. -/
def profW (t s : ℝ) : ℝ × ℝ :=
  if s ≤ sig1c t then seg W1 (W2c t) 0 (sig1c t) s
  else if s ≤ sig2c t then seg (W2c t) (W3c t) (sig1c t) (sig2c t) s
  else if s ≤ tauc t then seg (W3c t) W4 (sig2c t) (tauc t) s
  else seg W4 (W5c t) (tauc t) 1 s

/-- **The candidate disc map** in tube coordinates. -/
def eFun (t s : ℝ) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i.val = 0 then (2 + (profW t s).1) * Real.cos t
    else if i.val = 1 then (2 + (profW t s).1) * Real.sin t
    else (profW t s).2)



end

end Work.Drive.EpsForm
