import Mathlib
import Submission.Work.MotK.TwCensus.SdualTPrimeGood

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The target ruling divisor `sdualT` is a prime element (re-export)

The theorem `Work.MotK.TwCensus.SdualTPrimeGood` — for an infinite field `K` of characteristic
`≠ 5`, a good Klein datum `D` and `h ≠ 0`, the chart restriction of the target-side dual secant
quintic

  `sdualT D.a D.b h = kleinTwSDualV D.a D.b h (chart3 K)`

is a *prime element* of `K[x₀,x₁,x₂]` (equivalently irreducible, `K[x₀,x₁,x₂]` being a unique
factorization monoid, so that its principal ideal `(sdualT)` is a height-one prime — the point
`zP` of the certificate `Work.MotV.LinkCert` of the T-twisted Crauder–Katz link, needed by
`Work.MotK.TGen.SdualTClass`) — is proved in

* `Submission/Work/MotK/TwCensus/SdualTPrimeGood.lean` (the theorem itself, from the two pillars
  `Work.MotK.TwCensus.GoodDiscNe` and `Work.MotK.TGen.SdualTIrreducibleOfDisc`),
* with the explicit-shape input `Work.MotK.TwCensus.sdualT_explicit` and its companions in the
  neutral module `Submission.Work.MotK.TwCensus.SdualTShape`.

This module is kept as the stable import point for consumers of the census clause; it re-exports
the theorem rather than restating it (restating it would duplicate the declaration).
-/
