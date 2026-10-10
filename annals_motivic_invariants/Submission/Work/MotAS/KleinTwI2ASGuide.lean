import Mathlib
import Submission.Work.MotAS.ASData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The AS link identity I2^AS

`kleinPAS k (kleinRAS z) = s'^AS(z) · z`, the Artin-Schreier (characteristic `5`) form of the split
identity `KleinIdents.kleinP_kleinR` of `Work.MotK`.

## Suggested route (cheap: transports + cancellation, no big `ring`)

Let `S := AdjoinRoot (Polynomial.X^5 - Polynomial.X - Polynomial.C g)` over `R` and
`w := AdjoinRoot.root _`, so `w^5 = w + g` and `5 = 0` in `S` (`h5` transports to `S`).

* with `ξ := fun i => ∑ j, asM w i j * z j`, `asTransportR`
  (`Submission/Work/MotAS/ASTransportR`) gives
  `kleinR a b (fun i => ∑ j, asN w i j * z j) = (asM w).mulVec (kleinRAS a b g z)`;
* the split identity `Work.MotK.KleinIdents.kleinP_kleinR`
  (`kleinP a b (kleinR a b x) = fun i => kleinSecDual a b x * x i`, valid over any `CommRing`)
  applied to `x := asN w · z` gives
  `kleinP a b (kleinR a b (fun i => ∑ j, asN w i j * z j)) = fun i => kleinSecDual a b ξ * ξ i`
  (where `ξ` is that vector); combine with `asTransportP`
  (`Submission.Work.MotAS/ASTransport`) on the left and `asTransportSD`
  (`Submission.Work.MotAS/asTransportSD`) on the right to get
  `(asN w).mulVec (kleinPAS a b g (kleinRAS a b g z)) = (asN w).mulVec (fun i => kleinSecDualAS a b g z * z i)`;
* `asN_mulVec_injective` (`Submission.Work.MotAS.ASMatrix`, needs `isUnit_288`, i.e. `5 = 0`)
  cancels `asN w`;
* descend from `S` to `R` with `AdjoinRoot.of.injective_of_monic_of_degree_pos`
  (`X^5 - X - C g` is monic of positive degree), since the statement is `w`-free.

Note `asTransportP`/`asTransportR`/`asTransportSD` are already proved in the workspace.
-/

-- (guidance only; the theorem statement lives at `Work/MotAS/KleinTwI2AS`)
