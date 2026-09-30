import Mathlib
import Submission.Work.BMF.halasz_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for `Work.BMF.LSeries_norm_le_exp_Wsup`

The local Euler factor of a function `f : ℕ → ℂ` at the prime `p` and the point `s`:

`eulerFac f p s = Σ_{e ≥ 0} f (p^e) * (p^{-s})^e = Σ_{e ≥ 0} f (p^e) * p^{-e s}`.

For `f` multiplicative (on coprime arguments) and `Re s > 1`, `LSeries f s = ∏_p eulerFac f p s`.
-/

namespace Work.BMF

open Finset Real Complex

/-- The local Euler factor `Σ_{e ≥ 0} f (p^e) (p^{-s})^e` at the prime `p`. -/
noncomputable def eulerFac (f : ℕ → ℂ) (p : ℕ) (s : ℂ) : ℂ :=
  ∑' e : ℕ, f (p ^ e) * ((p : ℂ) ^ (-s)) ^ e

end Work.BMF
