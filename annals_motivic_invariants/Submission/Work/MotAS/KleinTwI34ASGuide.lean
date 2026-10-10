import Mathlib
import Submission.Work.MotAS.ASData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Deriving the "ruling transport" identities I3^AS and I4^AS

The AS link identities, in characteristic `5` (`h5 : (5 : R) = 0`), for a general `CommRing R`:

* **I1^AS** `kleinRAS a b g (kleinPAS a b g y) = fun i => kleinSecAS a b g y * y i`
  (component `0` is `Work.MotAS.KleinTwScalarAS`, PROVED; the ratio form is
  `Work.MotAS.KleinTwProjAS`, PROVED);
* **I2^AS** `kleinPAS a b g (kleinRAS a b g z) = fun i => kleinSecDualAS a b g z * z i`
  (`Work.MotAS.KleinTwI2AS`, in flight);
* **I3^AS** `kleinSecDualAS a b g (kleinPAS a b g y) = kleinSecAS a b g y ^ 2`;
* **I4^AS** `kleinSecAS a b g (kleinRAS a b g z) = kleinSecDualAS a b g z ^ 3`.

## Why I3/I4 are *cheap* once I1 and I2 are available

They are the AS analogues of the split derivation of `Work.MotK.KleinIdents.kleinI4_mul` /
`KleinI4` (see `Submission/Work/MotK/KleinI4.lean`), which is *pure algebra*, no expansion:

* `P^AS` and `R^AS` are homogeneous of degree `2`, resp. `3`
  (`kleinPAS (c • y) = c^2 • kleinPAS y`, `kleinRAS (c • z) = c^3 • kleinRAS z`, all `ring`);
* for I3: `P^AS(R^AS(P^AS y))` is `kleinSecDualAS (…y) • kleinPAS y` by I2 at `z := kleinPAS y`,
  and `kleinSecAS y^2 • kleinPAS y` by I1 at `y` plus homogeneity of `P^AS`; compare component `4`,
  i.e. `kleinPAS4 = -kleinQAS` (`Work.MotAS.kleinPAS_four_eq_neg`), a nonzero polynomial (e.g.
  `kleinQAS` does not vanish at `![1,0,0,0,0]`);
* for I4: `R^AS(P^AS(R^AS z))` is `kleinSecAS (kleinRAS z) • kleinRAS z` by I1 at `kleinRAS z`,
  and `kleinSecDualAS z ^ 3 • kleinRAS z` by I2 at `z` plus homogeneity of `R^AS`; compare
  component `0` (`kleinRAS (charting0) ≠ 0`, e.g. evaluate at a suitable point).

The step "compare components" needs a *domain* and a *nonzero* component; the clean way is the
universal-ring trick of `KleinI4.lean`: prove the identity in `Univ = (ZMod 5)[X_0..X_7]`
(or in `AdjoinRoot`/`MvPolynomial` over `ZMod 5`) where the component is a nonzero polynomial
(check it by evaluation at a point), cancel it there, and push the result back along the
evaluation homomorphism (`map`-lemmas for `kleinRAS`, `kleinPAS`, `kleinSecAS`, `kleinSecDualAS`,
as in `KleinI4.lean`).  Both identities then hold in every `CommRing R` with `(5 : R) = 0`.
-/

namespace Work.MotAS

end Work.MotAS
