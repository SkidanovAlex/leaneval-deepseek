import Mathlib
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.MotK.TwCensus.SdualTShape
import Submission.Work.MotK.TwCensus.SdualTScale
import Submission.Work.MotK.TwCensus.SdualTOneIrreducible
import Submission.Work.MotK.TGen.SdG5hDefs
import Submission.Work.MotK.TGen.SdG5hCrux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.SdualTIrreducibleOfDisc`

The target ruling divisor of the T-twisted Crauder–Katz link is
`Work.MotK.TGen.sdualT a b h = kleinTwSDualV a b h (chart3 K)`, the chart restriction
`z = (0, X₀, X₁, X₂, 1)` of the target-side dual secant quintic.  This file proves

```
theorem SdualTIrreducibleOfDisc (K : Type) [Field K] [Infinite K] (hk : ringChar K ≠ 5)
    (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (hdisc : a ^ 10 - 11 * a ^ 5 * b ^ 5 - b ^ 10 ≠ 0) :
    Irreducible (Work.MotK.TGen.sdualT a b h)
```

i.e. `sdualT a b h` is irreducible away from the degenerate locus `a^10 - 11a^5b^5 - b^10 = 0`.

## Proof

`Submission/Work/MotK/TGen/SdG5hDefs.lean` records that `sdualT a b h` splits as
`sdG5h a b h + sdG5hLower a b h`, where `sdG5h` is homogeneous of degree `5` and `sdG5hLower`
has total degree `< 5`.  The classical top-degree argument
(`Work.MotK.TwCensus.irreducible_of_isHomogeneous_add`) then shows that
`Irreducible (sdG5h a b h)` implies `Irreducible (sdualT a b h)`, and the irreducibility of the
degree-five part is the isolated crux `Work.MotK.TGen.SdG5hCrux`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Work.MotK.TGen

open MvPolynomial

/-- **`sdualT a b h` is irreducible away from the degenerate locus.** -/
theorem SdualTIrreducibleOfDisc (K : Type) [Field K] [Infinite K] (hk : ringChar K ≠ 5)
    (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (hdisc : a ^ 10 - 11 * a ^ 5 * b ^ 5 - b ^ 10 ≠ 0) :
    Irreducible (Work.MotK.TGen.sdualT a b h) := by
  have hG : Irreducible (Work.MotK.TGen.sdG5h a b h) :=
    Work.MotK.TGen.SdG5hCrux hk a b h ha hb hh hdisc
  have hmain : Irreducible (Work.MotK.TGen.sdG5h a b h + Work.MotK.TGen.sdG5hLower a b h) :=
    Work.MotK.TwCensus.irreducible_of_isHomogeneous_add (Work.MotK.TGen.sdG5h_isHomogeneous a b h)
      (Work.MotK.TGen.sdG5hLower_totalDegree a b h) hG
  rwa [← Work.MotK.TGen.sdualT_eq_sdG5h_add] at hmain

end Work.MotK.TGen
