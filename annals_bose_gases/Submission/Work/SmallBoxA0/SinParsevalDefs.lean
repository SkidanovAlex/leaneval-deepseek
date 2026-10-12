import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The odd extension used for the sine (Dirichlet) Parseval identity

`Work.SmallBoxA0.oddExt F v` is the odd extension of (the shifted version of)
`F` about `v = 0`:

  * for `v ∈ (0,1)` it equals `F (v - 1/2)`;
  * for `v ∈ (-1,0)` it equals `-F (-v - 1/2)` (i.e. `-(F ∘ shift)(-v)`).

It is designed so that the `n`-th Fourier coefficient of `oddExt F` on the
period-`2` circle (interval `[-1,1]`) equals `-I` times the `n`-th sine
coefficient `∫_{-1/2}^{1/2} F x · sin (nπ (x + 1/2)) dx` of `F`.  Applying the
Parseval identity `tsum_sq_fourierCoeffOn` to `oddExt F` then yields the
Dirichlet/sine Parseval identity on `[-1/2,1/2]`.
-/

set_option autoImplicit false

namespace Work.SmallBoxA0

noncomputable section

open MeasureTheory

/-- Odd extension of `F` about `0` after the shift `x ↦ x - 1/2`. -/
def oddExt (F : ℝ → ℝ) (v : ℝ) : ℝ :=
  if v ≤ 0 then -(F (-v - 1 / 2)) else F (v - 1 / 2)

end

end Work.SmallBoxA0
