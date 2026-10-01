import Mathlib

/-!
# Shared definitions for the `p = 2` "two-digit" (Postnikov) decomposition of the cubic
character correlation (`Work.LinnikBurgess.corr6_twoPow_gaussTwo_le`, route unit U3).

The truncated exponential `thetaTwo e m u = 1 + 2^m u + 2^(2m-1) u^2` in `ZMod (2^e)` plays the
role of `u ↦ 1 + 2^m u` when `3m ≥ e+1`: it is (i) multiplicative, `θ(u)θ(v) = θ(u+v)`,
(ii) periodic modulo `2^(e-m)`, (iii) a unit for every `u`, and (iv) satisfies the "two-digit"
identity `1 + 2^m u = θ (u - 2^(m-1) u^2)`.  This is what turns the summand at `x = y + 2^m w`
into a *quadratic* character sum in `w`.
-/

namespace Work.LinnikBurgess

/-- The truncated exponential `E(u) = 1 + 2^m u + 2^{2m-1} u^2`, an element of `ZMod (2^e)`. -/
noncomputable def thetaTwo (e m : ℕ) (u : ZMod (2 ^ e)) : ZMod (2 ^ e) :=
  1 + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * u + ((2 ^ (2 * m - 1) : ℕ) : ZMod (2 ^ e)) * u ^ 2

end Work.LinnikBurgess
