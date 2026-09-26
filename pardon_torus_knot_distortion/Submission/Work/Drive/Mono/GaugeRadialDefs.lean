import Mathlib

/-!
# Radial rescaling of a convex set from an interior point, via the Minkowski gauge

Let `K ⊆ E` be a convex set and `p ∈ interior K`.  Every ray from `p` meets the frontier of `K`
in exactly one point, so the set `K` is in bijection with the closed unit ball through the map
that records the *direction* of `z - p` and the *gauge* of `z - p` with respect to `K - p`.

* `gaugeRadial K p z = gauge (K - p) (z - p) • (z - p)/‖z - p‖`;
* `gaugeRadialInv K p w = p + (gauge (K - p) w/‖w‖)⁻¹ • w`.

Because `0⁻¹ = 0` in `ℝ`, both formulae are meaningful at `z = p` (resp. `w = 0`), where the
first is `0` and the second is `p`.  The two maps are mutually inverse bijections of `E`; the
first maps `K` onto the closed unit ball and the frontier of `K` onto the unit sphere.  The API
is proved in `GaugeRadialSpec`.
-/

namespace Work.Drive.Mono

noncomputable section

open Set
open scoped Pointwise

/-- The radial rescaling of the convex set `K` from the point `p`: the point `z` is sent to the
point of the closed unit ball with the direction of `z - p` and norm `gauge (K - p) (z - p)`. -/
def gaugeRadial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (p : E) (z : E) : E :=
  gauge (K - {p}) (z - p) • (‖z - p‖⁻¹ • (z - p))

/-- The inverse of `gaugeRadial K p`: the point `w` is sent to the point of the ray of `w` whose
gauge equals `‖w‖`, namely `p + (gauge (K - p) w/‖w‖)⁻¹ • w`. -/
def gaugeRadialInv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (p : E) (w : E) : E :=
  p + (gauge (K - {p}) (‖w‖⁻¹ • w))⁻¹ • w

end

end Work.Drive.Mono
