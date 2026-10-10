import Mathlib
import Submission.Work.MotAS.AsRuleRankDefs
import Submission.Work.MotAS.asRuleMinP_isHomogeneous

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.WitPt` --- the witness point for `Work.MotAS.asRuleMinP_notMem2`

`witPt a b` is the point of the AS Klein curve `kleinPAS a b g = 0` obtained as
`asM(w)^{-1} · (a,0,-a,-b,b)` where `w^5 = w + g`, reduced modulo `(w^5-w-g)` and modulo `5`
and read as a point with coordinates in `K[X]` (`X` in place of `w`).  It satisfies
`kleinPAS a b g (witPt a b) ≡ 0 (mod X^5 - X - g)`, and
`asRuleMinP a b g (witPt a b) ≡ witPhi a b g (mod X^5 - X - g)` with `witPhi a b g ≠ 0`
for `a b ≠ 0` and `a^2 - ab - b^2 ≠ 0` (the `X^2`-coefficient of `witPhi` is
`3ab(a^5-3b^5)^2 ≠ 0` because `a = 3b` would force `a^2-ab-b^2 = 0`).

## Proof route for the value identities

Both `Work.MotAS.witValue` and `Work.MotAS.witPfaff` are *explicit polynomial identities*.
Unfold `asRuleMinP` (`AsRuleRankDefs.lean`), `asRuleQA`/`asRuleQB`/`asTanQ`
(`SdualAS2Defs.lean`), `asPolarP` (`ASRulDefs.lean`), `kleinBilinAS` (`ASLink.lean`),
`kleinQAS`, `kleinPAS`, `kleinPAS0..4` (`ASData.lean`) and `Work.MotK.kleinE`
(`RuleData.lean`), and use `Work.MotAS.aeval_asRuleQX`/`aeval_asRuleQBX`
(`asRuleMinP_isHomogeneous.lean`) together with `Work.MotAS.map_kleinPAS0..4`
(`KleinTwProjAS.lean`) to push `MvPolynomial.aeval (witPt a b)` into the formulas; close
with `ring`.  (One may also first prove `asRuleMinP a b g = witLp a b * witQp a b` by the
same unfolding, where `witLp = (a^2-ab-b^2)·X0 + (a^2+b^2)·X2 + (2a^2-ab-2b^2)·X4` and
`witQp` is the cubic of `POLY_Q` below; the values `witLF = witLp(witPt a b)` and
`witQF = witQp(witPt a b)` are the explicit polynomials below and
`witLF * witQF = (X^5-X-g) * witH + witPhi` by `ring`.)

## ⚠ How to close the `ring` step in characteristic 5

`ring` / `ring_nf` do **not** reduce integer coefficients modulo 5 (they leave
`... * 2 = ... * 27 - ... * 18`).  The workable pattern (used throughout this workspace,
e.g. `Submission/Work/MotAS/ASTransport.lean`) is: introduce

```lean
have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
```

and either

* prove the identity with the 5-multiple made explicit and cancel it, e.g.
```lean
have key : LHS - RHS = 5 * (explicit C) := by ring
rw [key, h5, mul_zero, sub_eq_zero]
```
  (`key` is a genuine ring identity, so plain `ring` proves it), or
* run `linear_combination (explicit C) * h5` after `ring_nf` has produced the residual.

Equivalently: state and prove the identity for a general `[CommRing R]` with `h5 : (5 : R) = 0`
(that is exactly the workspace idiom), and specialise.

-/

set_option maxHeartbeats 16000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace Work.MotAS
open MvPolynomial Polynomial

variable {K : Type} [Field K] [CharP K 5]

noncomputable def witPt (a b : K) : Fin 5 → Polynomial K :=
  ![Polynomial.C ((a)) + Polynomial.C ((2*a) + (2*b)) * Polynomial.X^(1:ℕ) + Polynomial.C ((4*a) + (3*b)) * Polynomial.X^(2:ℕ) + Polynomial.C ((3*a) + (b)) * Polynomial.X^(3:ℕ), Polynomial.C ((3*a) + (3*b)) + Polynomial.C ((2*a) + (4*b)) * Polynomial.X^(1:ℕ) + Polynomial.C ((a) + (2*b)) * Polynomial.X^(2:ℕ), Polynomial.C ((4*a) + (3*b)) + Polynomial.C ((4*a) + (3*b)) * Polynomial.X^(1:ℕ), Polynomial.C ((2*a) + (4*b)), 0]

noncomputable def witH (a b g : K) : Polynomial K := Polynomial.C ((a^(12:ℕ)*g) + (a^(12:ℕ)) + (a^(11:ℕ)*b*g) + (2*a^(11:ℕ)*b) + (3*a^(10:ℕ)*b^(2:ℕ)*g) + (a^(10:ℕ)*b^(2:ℕ)) + (3*a^(9:ℕ)*b^(3:ℕ)) + (4*a^(8:ℕ)*b^(4:ℕ)) + (4*a^(7:ℕ)*b^(5:ℕ)*g) + (a^(7:ℕ)*b^(5:ℕ)) + (4*a^(6:ℕ)*b^(6:ℕ)*g) + (4*a^(6:ℕ)*b^(6:ℕ)) + (2*a^(5:ℕ)*b^(7:ℕ)*g) + (2*a^(5:ℕ)*b^(7:ℕ)) + (a^(4:ℕ)*b^(8:ℕ)) + (3*a^(3:ℕ)*b^(9:ℕ)) + (4*a^(2:ℕ)*b^(10:ℕ)*g) + (3*a^(2:ℕ)*b^(10:ℕ)) + (4*a*b^(11:ℕ)*g) + (2*b^(12:ℕ)*g)) + Polynomial.C ((a^(12:ℕ)*g) + (3*a^(11:ℕ)*b*g) + (a^(11:ℕ)*b) + (2*a^(10:ℕ)*b^(2:ℕ)*g) + (3*a^(10:ℕ)*b^(2:ℕ)) + (4*a^(9:ℕ)*b^(3:ℕ)) + (2*a^(8:ℕ)*b^(4:ℕ)) + (4*a^(7:ℕ)*b^(5:ℕ)*g) + (a^(7:ℕ)*b^(5:ℕ)) + (2*a^(6:ℕ)*b^(6:ℕ)*g) + (2*a^(6:ℕ)*b^(6:ℕ)) + (3*a^(5:ℕ)*b^(7:ℕ)*g) + (a^(5:ℕ)*b^(7:ℕ)) + (3*a^(4:ℕ)*b^(8:ℕ)) + (4*a^(3:ℕ)*b^(9:ℕ)) + (4*a^(2:ℕ)*b^(10:ℕ)*g) + (2*a^(2:ℕ)*b^(10:ℕ)) + (2*a*b^(11:ℕ)*g) + (3*b^(12:ℕ)*g)) * Polynomial.X^(1:ℕ) + Polynomial.C ((a^(12:ℕ)) + (2*a^(11:ℕ)*b*g) + (3*a^(11:ℕ)*b) + (4*a^(10:ℕ)*b^(2:ℕ)*g) + (4*a^(10:ℕ)*b^(2:ℕ)) + (4*a^(9:ℕ)*b^(3:ℕ)) + (2*a^(8:ℕ)*b^(4:ℕ)) + (3*a^(6:ℕ)*b^(6:ℕ)*g) + (a^(5:ℕ)*b^(7:ℕ)*g) + (3*a^(4:ℕ)*b^(8:ℕ)) + (4*a^(3:ℕ)*b^(9:ℕ)) + (a^(2:ℕ)*b^(10:ℕ)) + (3*a*b^(11:ℕ)*g) + (3*a*b^(11:ℕ)) + (b^(12:ℕ)*g) + (4*b^(12:ℕ))) * Polynomial.X^(2:ℕ) + Polynomial.C ((2*a^(12:ℕ)*g) + (4*a^(12:ℕ)) + (3*a^(11:ℕ)*b*g) + (a^(11:ℕ)*b) + (3*a^(10:ℕ)*b^(2:ℕ)*g) + (3*a^(9:ℕ)*b^(3:ℕ)) + (4*a^(8:ℕ)*b^(4:ℕ)) + (3*a^(7:ℕ)*b^(5:ℕ)*g) + (3*a^(7:ℕ)*b^(5:ℕ)) + (2*a^(6:ℕ)*b^(6:ℕ)*g) + (2*a^(5:ℕ)*b^(7:ℕ)*g) + (3*a^(5:ℕ)*b^(7:ℕ)) + (a^(4:ℕ)*b^(8:ℕ)) + (3*a^(3:ℕ)*b^(9:ℕ)) + (3*a^(2:ℕ)*b^(10:ℕ)*g) + (2*a*b^(11:ℕ)*g) + (a*b^(11:ℕ)) + (2*b^(12:ℕ)*g) + (b^(12:ℕ))) * Polynomial.X^(3:ℕ) + Polynomial.C ((3*a^(12:ℕ)*g) + (2*a^(11:ℕ)*b*g) + (2*a^(10:ℕ)*b^(2:ℕ)*g) + (2*a^(7:ℕ)*b^(5:ℕ)*g) + (3*a^(6:ℕ)*b^(6:ℕ)*g) + (3*a^(5:ℕ)*b^(7:ℕ)*g) + (2*a^(2:ℕ)*b^(10:ℕ)*g) + (3*a*b^(11:ℕ)*g) + (3*b^(12:ℕ)*g)) * Polynomial.X^(4:ℕ) + Polynomial.C ((2*a^(12:ℕ)) + (3*a^(11:ℕ)*b) + (a^(10:ℕ)*b^(2:ℕ)) + (3*a^(7:ℕ)*b^(5:ℕ)) + (2*a^(6:ℕ)*b^(6:ℕ)) + (4*a^(5:ℕ)*b^(7:ℕ)) + (3*a^(2:ℕ)*b^(10:ℕ)) + (2*a*b^(11:ℕ)) + (4*b^(12:ℕ))) * Polynomial.X^(5:ℕ) + Polynomial.C ((3*a^(12:ℕ)) + (3*a^(10:ℕ)*b^(2:ℕ)) + (2*a^(7:ℕ)*b^(5:ℕ)) + (2*a^(5:ℕ)*b^(7:ℕ)) + (2*a^(2:ℕ)*b^(10:ℕ)) + (2*b^(12:ℕ))) * Polynomial.X^(6:ℕ) + Polynomial.C ((4*a^(12:ℕ)) + (4*a^(10:ℕ)*b^(2:ℕ)) + (a^(7:ℕ)*b^(5:ℕ)) + (a^(5:ℕ)*b^(7:ℕ)) + (a^(2:ℕ)*b^(10:ℕ)) + (b^(12:ℕ))) * Polynomial.X^(7:ℕ)

noncomputable def witPhi (a b g : K) : Polynomial K := Polynomial.C ((a^(12:ℕ)*g^(2:ℕ)) + (a^(12:ℕ)*g) + (4*a^(11:ℕ)*b*g^(2:ℕ)) + (2*a^(11:ℕ)*b*g) + (3*a^(11:ℕ)*b) + (4*a^(10:ℕ)*b^(2:ℕ)*g^(2:ℕ)) + (4*a^(10:ℕ)*b^(2:ℕ)*g) + (4*a^(7:ℕ)*b^(5:ℕ)*g^(2:ℕ)) + (4*a^(7:ℕ)*b^(5:ℕ)*g) + (a^(6:ℕ)*b^(6:ℕ)*g^(2:ℕ)) + (3*a^(6:ℕ)*b^(6:ℕ)*g) + (2*a^(6:ℕ)*b^(6:ℕ)) + (a^(5:ℕ)*b^(7:ℕ)*g^(2:ℕ)) + (a^(5:ℕ)*b^(7:ℕ)*g) + (4*a^(2:ℕ)*b^(10:ℕ)*g^(2:ℕ)) + (4*a^(2:ℕ)*b^(10:ℕ)*g) + (a*b^(11:ℕ)*g^(2:ℕ)) + (3*a*b^(11:ℕ)*g) + (2*a*b^(11:ℕ)) + (b^(12:ℕ)*g^(2:ℕ)) + (b^(12:ℕ)*g)) + Polynomial.C ((a^(12:ℕ)*g) + (2*a^(11:ℕ)*b*g) + (a^(11:ℕ)*b) + (4*a^(10:ℕ)*b^(2:ℕ)*g) + (4*a^(7:ℕ)*b^(5:ℕ)*g) + (3*a^(6:ℕ)*b^(6:ℕ)*g) + (4*a^(6:ℕ)*b^(6:ℕ)) + (a^(5:ℕ)*b^(7:ℕ)*g) + (4*a^(2:ℕ)*b^(10:ℕ)*g) + (3*a*b^(11:ℕ)*g) + (4*a*b^(11:ℕ)) + (b^(12:ℕ)*g)) * Polynomial.X^(1:ℕ) + Polynomial.C ((3*a^(11:ℕ)*b) + (2*a^(6:ℕ)*b^(6:ℕ)) + (2*a*b^(11:ℕ))) * Polynomial.X^(2:ℕ)

noncomputable def witHk : Fin 5 → K → K → K → Polynomial K
  | 0, a, b, g => Polynomial.C ((4*a^(4:ℕ)) + (2*a^(3:ℕ)*b) + (a^(2:ℕ)*b^(2:ℕ)) + (3*a*b^(3:ℕ)) + (4*b^(4:ℕ))) + Polynomial.C ((4*a^(4:ℕ)) + (2*a^(3:ℕ)*b) + (a^(2:ℕ)*b^(2:ℕ)) + (3*a*b^(3:ℕ)) + (4*b^(4:ℕ))) * Polynomial.X^(1:ℕ)
  | 1, a, b, g => Polynomial.C ((a^(4:ℕ)) + (3*a^(3:ℕ)*b) + (4*a^(2:ℕ)*b^(2:ℕ)) + (2*a*b^(3:ℕ)) + (b^(4:ℕ)))
  | _, _, _, _ => 0

noncomputable def witLF (a b g : K) : Polynomial K := Polynomial.C ((2*a^(2:ℕ)*b) + (3*a*b^(2:ℕ)) + (3*b^(3:ℕ))) + Polynomial.C ((a^(3:ℕ)) + (3*a^(2:ℕ)*b) + (b^(3:ℕ))) * Polynomial.X^(1:ℕ) + Polynomial.C ((4*a^(3:ℕ)) + (4*a^(2:ℕ)*b) + (3*a*b^(2:ℕ)) + (2*b^(3:ℕ))) * Polynomial.X^(2:ℕ) + Polynomial.C ((3*a^(3:ℕ)) + (3*a^(2:ℕ)*b) + (a*b^(2:ℕ)) + (4*b^(3:ℕ))) * Polynomial.X^(3:ℕ)

noncomputable def witQF (a b g : K) : Polynomial K := Polynomial.C ((4*a^(9:ℕ)*g^(2:ℕ)) + (4*a^(9:ℕ)) + (2*a^(8:ℕ)*b*g^(2:ℕ)) + (4*a^(8:ℕ)*b*g) + (4*a^(8:ℕ)*b) + (a^(7:ℕ)*b^(2:ℕ)*g^(2:ℕ)) + (3*a^(7:ℕ)*b^(2:ℕ)) + (3*a^(6:ℕ)*b^(3:ℕ)*g^(2:ℕ)) + (2*a^(6:ℕ)*b^(3:ℕ)*g) + (2*a^(6:ℕ)*b^(3:ℕ)) + (4*a^(5:ℕ)*b^(4:ℕ)*g^(2:ℕ)) + (a^(5:ℕ)*b^(4:ℕ)*g) + (3*a^(4:ℕ)*b^(5:ℕ)*g^(2:ℕ)) + (3*a^(4:ℕ)*b^(5:ℕ)) + (4*a^(3:ℕ)*b^(6:ℕ)*g^(2:ℕ)) + (3*a^(3:ℕ)*b^(6:ℕ)*g) + (3*a^(3:ℕ)*b^(6:ℕ)) + (2*a^(2:ℕ)*b^(7:ℕ)*g^(2:ℕ)) + (a^(2:ℕ)*b^(7:ℕ)) + (a*b^(8:ℕ)*g^(2:ℕ)) + (4*a*b^(8:ℕ)*g) + (4*a*b^(8:ℕ)) + (3*b^(9:ℕ)*g^(2:ℕ)) + (2*b^(9:ℕ)*g)) + Polynomial.C ((4*a^(9:ℕ)*g^(2:ℕ)) + (3*a^(9:ℕ)*g) + (4*a^(9:ℕ)) + (2*a^(8:ℕ)*b*g^(2:ℕ)) + (a^(8:ℕ)*b*g) + (a^(8:ℕ)*b) + (a^(7:ℕ)*b^(2:ℕ)*g^(2:ℕ)) + (a^(7:ℕ)*b^(2:ℕ)*g) + (a^(7:ℕ)*b^(2:ℕ)) + (3*a^(6:ℕ)*b^(3:ℕ)*g^(2:ℕ)) + (3*a^(6:ℕ)*b^(3:ℕ)*g) + (4*a^(5:ℕ)*b^(4:ℕ)*g^(2:ℕ)) + (2*a^(5:ℕ)*b^(4:ℕ)*g) + (3*a^(4:ℕ)*b^(5:ℕ)*g^(2:ℕ)) + (a^(4:ℕ)*b^(5:ℕ)*g) + (3*a^(4:ℕ)*b^(5:ℕ)) + (4*a^(3:ℕ)*b^(6:ℕ)*g^(2:ℕ)) + (2*a^(3:ℕ)*b^(6:ℕ)*g) + (2*a^(3:ℕ)*b^(6:ℕ)) + (2*a^(2:ℕ)*b^(7:ℕ)*g^(2:ℕ)) + (2*a^(2:ℕ)*b^(7:ℕ)*g) + (2*a^(2:ℕ)*b^(7:ℕ)) + (a*b^(8:ℕ)*g^(2:ℕ)) + (a*b^(8:ℕ)*g) + (3*b^(9:ℕ)*g^(2:ℕ)) + (4*b^(9:ℕ)*g)) * Polynomial.X^(1:ℕ) + Polynomial.C ((4*a^(9:ℕ)*g) + (a^(9:ℕ)) + (a^(8:ℕ)*b*g) + (a^(7:ℕ)*b^(2:ℕ)*g) + (3*a^(7:ℕ)*b^(2:ℕ)) + (4*a^(6:ℕ)*b^(3:ℕ)) + (3*a^(4:ℕ)*b^(5:ℕ)*g) + (2*a^(4:ℕ)*b^(5:ℕ)) + (2*a^(3:ℕ)*b^(6:ℕ)*g) + (2*a^(2:ℕ)*b^(7:ℕ)*g) + (a^(2:ℕ)*b^(7:ℕ)) + (3*a*b^(8:ℕ))) * Polynomial.X^(2:ℕ) + Polynomial.C ((3*a^(9:ℕ)*g) + (2*a^(8:ℕ)*b*g) + (4*a^(8:ℕ)*b) + (2*a^(6:ℕ)*b^(3:ℕ)*g) + (2*a^(6:ℕ)*b^(3:ℕ)) + (2*a^(5:ℕ)*b^(4:ℕ)*g) + (a^(5:ℕ)*b^(4:ℕ)) + (a^(4:ℕ)*b^(5:ℕ)*g) + (4*a^(3:ℕ)*b^(6:ℕ)*g) + (3*a^(3:ℕ)*b^(6:ℕ)) + (4*a*b^(8:ℕ)*g) + (4*a*b^(8:ℕ)) + (4*b^(9:ℕ)*g) + (2*b^(9:ℕ))) * Polynomial.X^(3:ℕ) + Polynomial.C ((2*a^(9:ℕ)*g) + (3*a^(9:ℕ)) + (3*a^(8:ℕ)*b*g) + (2*a^(8:ℕ)*b) + (3*a^(6:ℕ)*b^(3:ℕ)*g) + (2*a^(6:ℕ)*b^(3:ℕ)) + (3*a^(5:ℕ)*b^(4:ℕ)*g) + (2*a^(5:ℕ)*b^(4:ℕ)) + (4*a^(4:ℕ)*b^(5:ℕ)*g) + (a^(4:ℕ)*b^(5:ℕ)) + (a^(3:ℕ)*b^(6:ℕ)*g) + (4*a^(3:ℕ)*b^(6:ℕ)) + (a*b^(8:ℕ)*g) + (4*a*b^(8:ℕ)) + (b^(9:ℕ)*g) + (4*b^(9:ℕ))) * Polynomial.X^(4:ℕ) + Polynomial.C ((a^(9:ℕ)*g) + (a^(9:ℕ)) + (3*a^(8:ℕ)*b*g) + (3*a^(8:ℕ)*b) + (4*a^(7:ℕ)*b^(2:ℕ)*g) + (3*a^(7:ℕ)*b^(2:ℕ)) + (2*a^(6:ℕ)*b^(3:ℕ)*g) + (3*a^(6:ℕ)*b^(3:ℕ)) + (a^(5:ℕ)*b^(4:ℕ)*g) + (2*a^(5:ℕ)*b^(4:ℕ)) + (2*a^(4:ℕ)*b^(5:ℕ)*g) + (2*a^(4:ℕ)*b^(5:ℕ)) + (a^(3:ℕ)*b^(6:ℕ)*g) + (a^(3:ℕ)*b^(6:ℕ)) + (3*a^(2:ℕ)*b^(7:ℕ)*g) + (a^(2:ℕ)*b^(7:ℕ)) + (4*a*b^(8:ℕ)*g) + (a*b^(8:ℕ)) + (2*b^(9:ℕ)*g) + (4*b^(9:ℕ))) * Polynomial.X^(5:ℕ) + Polynomial.C ((a^(9:ℕ)*g) + (3*a^(8:ℕ)*b*g) + (3*a^(8:ℕ)*b) + (4*a^(7:ℕ)*b^(2:ℕ)*g) + (a^(7:ℕ)*b^(2:ℕ)) + (2*a^(6:ℕ)*b^(3:ℕ)*g) + (3*a^(6:ℕ)*b^(3:ℕ)) + (a^(5:ℕ)*b^(4:ℕ)*g) + (a^(5:ℕ)*b^(4:ℕ)) + (2*a^(4:ℕ)*b^(5:ℕ)*g) + (a^(3:ℕ)*b^(6:ℕ)*g) + (a^(3:ℕ)*b^(6:ℕ)) + (3*a^(2:ℕ)*b^(7:ℕ)*g) + (2*a^(2:ℕ)*b^(7:ℕ)) + (4*a*b^(8:ℕ)*g) + (a*b^(8:ℕ)) + (2*b^(9:ℕ)*g) + (2*b^(9:ℕ))) * Polynomial.X^(6:ℕ) + Polynomial.C ((2*a^(9:ℕ)) + (2*a^(8:ℕ)*b) + (3*a^(7:ℕ)*b^(2:ℕ)) + (2*a^(6:ℕ)*b^(3:ℕ)) + (a^(5:ℕ)*b^(4:ℕ)) + (4*a^(4:ℕ)*b^(5:ℕ)) + (4*a^(3:ℕ)*b^(6:ℕ)) + (a^(2:ℕ)*b^(7:ℕ)) + (4*a*b^(8:ℕ)) + (2*b^(9:ℕ))) * Polynomial.X^(7:ℕ) + Polynomial.C ((2*a^(9:ℕ)) + (3*a^(8:ℕ)*b) + (3*a^(6:ℕ)*b^(3:ℕ)) + (3*a^(5:ℕ)*b^(4:ℕ)) + (4*a^(4:ℕ)*b^(5:ℕ)) + (a^(3:ℕ)*b^(6:ℕ)) + (a*b^(8:ℕ)) + (b^(9:ℕ))) * Polynomial.X^(8:ℕ) + Polynomial.C ((3*a^(9:ℕ)) + (2*a^(8:ℕ)*b) + (2*a^(6:ℕ)*b^(3:ℕ)) + (2*a^(5:ℕ)*b^(4:ℕ)) + (a^(4:ℕ)*b^(5:ℕ)) + (4*a^(3:ℕ)*b^(6:ℕ)) + (4*a*b^(8:ℕ)) + (4*b^(9:ℕ))) * Polynomial.X^(9:ℕ)

end Work.MotAS