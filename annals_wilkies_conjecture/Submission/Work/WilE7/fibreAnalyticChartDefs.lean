import Mathlib

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped Topology

namespace Work.WilE7

/-- **The coordinate-wise shrinking self-map of `ℝ^m`.**  Each coordinate `v l` is replaced by
`c * v l / (1 + (v l)^2)`.  This map is analytic everywhere, its image is contained in the closed
ball of radius `c / 2`, it fixes `0`, and its derivative at `0` is `c` times the identity.
It is the device used to turn a germ of an analytic parametrisation into a global one: composing
with it keeps the derivative at `0` injective while forcing the image into an arbitrarily small
ball. -/
def coordShrink (m : ℕ) (c : ℝ) : (Fin m → ℝ) → (Fin m → ℝ) :=
  fun v l => c * v l / (1 + (v l) ^ 2)

end Work.WilE7
