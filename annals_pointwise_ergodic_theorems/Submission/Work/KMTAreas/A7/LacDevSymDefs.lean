/-
# Auxiliary definitions for the uniform symbol bound `Work.KMTAreas.A7.lacDevSymBound`

The uniform bound on the symbol `∑'_j lacDevLin K σ U ω j · e^{2πijθ}` of the linearised
deviation kernel is a lacunary Littlewood–Paley summation.  Two real quantities of the frequency
`θ` govern it:

* `nearDist θ = |θ - nearInt θ|` — the distance from `θ` to the nearest integer.  It is the
  quantity in which the *bump* symbol `bumpSym K m θ = ∑'_k 𝓕K (m (k - θ))` is small for small
  `m · nearDist θ` (the Poisson summation picks out the single nearest integer), and it is the
  quantity in which the *deviation* symbol cancels the triangle symbol `lacConst K · triSym L θ`.

* `zGap θ = ‖1 - e^{2πiθ}‖` — the size of the exponential gap.  It is the quantity that makes the
  *triangle* (Fejér) symbol small away from the integers: `triSym L θ` is the symbol of a
  probability kernel of width `2^L`, and it is small as soon as `2^L · zGap θ` is large.

The two quantities are comparable — `4 * nearDist θ ≤ zGap θ ≤ 2 π * nearDist θ`
(`Work.KMTAreas.A7.lacDevNearInt_facts`) — which is what allows a single lacunary summation
(`Work.KMTAreas.A7.lacDevLacSum`) to absorb the two families of terms in the two regimes
`σ n · zGap θ ≤ 1` and `σ n · zGap θ ≥ 1`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LacDevDefs

set_option autoImplicit false

namespace Work.KMTAreas.A7

open scoped BigOperators

noncomputable section

/-- The nearest integer to `θ`, realised as `⌊θ + 1/2⌋`. -/
def nearInt (θ : ℝ) : ℤ := ⌊θ + 1 / 2⌋

/-- The distance from `θ` to the nearest integer. -/
def nearDist (θ : ℝ) : ℝ := |θ - (nearInt θ : ℝ)|

/-- The size of the exponential gap `|1 - e^{2πiθ}|`, in the character convention of
`Work.KMTAreas.ADev` (`chr 1 θ = e^{2πiθ}`). -/
def zGap (θ : ℝ) : ℝ := ‖(1 : ℂ) - Work.KMTAreas.ADev.chr 1 θ‖

end

end Work.KMTAreas.A7
