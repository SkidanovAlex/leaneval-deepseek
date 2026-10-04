import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for `Work.Diff.Alg.Pinch.chat_shift_strict`

The uniform-in-`s` shifted strictness `Work.Diff.Alg.Pinch.ShiftStrict` is proved from four
*quantitative* versions of the pointwise Böhm–Wilking strictness statements: at a tight direction
(resp. a degenerate direction) of the preimage `S = chatLinv n s X`, the pulled-back reaction
`linv a b (Q (ell a b S))` improves the relevant form by an *explicit* positive amount.

For the branch `b ≤ 1/2` (`a = ccA n b`) the two amounts are

* `RFAux.bwCρ n b · |Ric₀ S|² · |v|²`  for the Ricci form (`Work.Diff.Alg.Pinch.ric_margin_b`),
* `4 · ccA n b · ccP n b · (scal S / n)² · EFun (Iso n)`  for the isotropic curvature form
  (`Work.Diff.Alg.Pinch.efun_margin_b`);

for the branch `1/2 < a` (`b = 1/2`, `p = 1 - 4/((n-2) + 8a)`) they are

* `2 (1-p) (scal S / n)² ((2a-1) + n (1-p)²/(4 (1+2(n-1)a))) |v|²`
  (`Work.Diff.Alg.Pinch.ric_margin_a`),
* `2 · efaPsi n a · (scal S / n)² · EFun (Iso n)`  (`Work.Diff.Alg.Pinch.efun_margin_a`).

`efaPsi` is the explicit (positive) lower bound for the Böhm–Wilking coefficient `bwGamma n a S`
coming out of the proof of `Work.Diff.Alg.Pinch.bwGamma_pos`: with `s = 2a - 1` and
`D = n + 2 + 4s`,

`bwGamma n a S ≥ (scal S / n)² · [(n-2)/(n+2) + s (n-6+4s)/D - 4 s (n-1)/D²]`

(following from `ric0Frob2 S ≤ n(n-1)(4 (scal S/n)/D)²`, which is `ric0Frob2_le`).
-/

namespace Work.Diff.Alg.Pinch

/-- The explicit lower bound `Ψ(a)` for the Böhm–Wilking coefficient `bwGamma n a S` (divided by
`(scal S / n)²`), for the branch `1/2 < a`, `b = 1/2`.  See the module docstring. -/
noncomputable def efaPsi (n : ℕ) (a : ℝ) : ℝ :=
  ((n : ℝ) - 2) / ((n : ℝ) + 2)
    + (2 * a - 1) * (((n : ℝ) - 6 + 4 * (2 * a - 1)) / ((n : ℝ) + 2 + 4 * (2 * a - 1)))
    - 4 * (2 * a - 1) * ((n : ℝ) - 1) / ((n : ℝ) + 2 + 4 * (2 * a - 1)) ^ 2

end Work.Diff.Alg.Pinch
