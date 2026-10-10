import Mathlib
import Submission.Work.MotK.TwCensus.SdualTShape
import Submission.Work.MotK.TwCensus.GoodDiscNe
import Submission.Work.MotK.TGen.SdualTIrreducibleOfDisc

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TwCensus.SdualTPrimeGood` — the census clause for the target ruling divisor

Target (this file):

`Prime (Work.MotK.TGen.sdualT D.a D.b h)` for `D : KleinData K` with `D.Good`, `h ≠ 0`,
`K` infinite and `ringChar K ≠ 5`.

Here `Work.MotK.TGen.sdualT a b h = kleinTwSDualV a b h (chart3 K)` is the chart restriction
`z = (0, X₀, X₁, X₂, 1)` of the target-side dual secant quintic `s'` of the T-twisted
Crauder--Katz link.  Since `K[x₀,x₁,x₂]` is a unique factorization monoid, primality is
irreducibility (of the non-zero element `sdualT D.a D.b h`), so the theorem says that the
principal ideal `(sdualT)` cut out by the target ruling divisor is a height-one prime — the point
`zP` of the certificate `Work.MotV.LinkCert` of the T-twisted link.

## Proof

Two ingredients:

* **non-degeneracy from `Good`** — `Work.MotK.TwCensus.GoodDiscNe K hk D hD`:
  `D.a^10 - 11 D.a^5 D.b^5 - D.b^10 ≠ 0`.  (`klein_eq` + `spans` + `coord0_ne` place the five
  Klein coordinates on the Klein curve `C_{a,b}` with `[κ]` not contained in a line; for
  `Δ = a^10 - 11a^5b^5 - b^10 = 0` the curve `C_{a,b}` is a pentagon of five lines, in one of
  which `[κ]` would have to lie.)
* **irreducibility off the degenerate locus** —
  `Work.MotK.TGen.SdualTIrreducibleOfDisc K hk a b h ha hb hh hdisc`: the degree-five part
  `sdG5h a b h` of `sdualT a b h` is irreducible (its two surviving degree splits are excluded by
  the weight filtration), and the top-degree argument
  `Work.MotK.TwCensus.irreducible_of_isHomogeneous_add` transfers this to `sdualT a b h`.

## Layout of the files

The elementary explicit-shape facts about `sdualT` (`sdualT_explicit`, `sdualT_scale_ab`, `sdG5`,
`sdualT_one_eq_structural`) live in the *neutral* module
`Submission.Work.MotK.TwCensus.SdualTShape`, which the irreducibility cluster
(`TGen/SdG5hDefs.lean`, `TwCensus/SdualTOneIrreducible.lean`, `TwCensus/SdG5*.lean`, ...) imports.
This file imports the cluster, so hosting those facts here (as was the case before) would make the
developments mutually recursive; the cycle is broken by the neutral module.
-/

set_option autoImplicit false

namespace Work.MotK.TwCensus

/-- **The target ruling divisor of the T-twisted link is a prime element.**  For `K` infinite of
characteristic `≠ 5`, `D : KleinData K` good and `h ≠ 0`, `sdualT D.a D.b h` is prime in
`K[x₀,x₁,x₂]`. -/
theorem SdualTPrimeGood (K : Type) [Field K] [Infinite K] (hk : ringChar K ≠ 5)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) :
    Prime (Work.MotK.TGen.sdualT D.a D.b h) := by
  have hab : D.a * D.b ≠ 0 := hD.ab_ne
  have ha : D.a ≠ 0 := fun h0 => hab (by rw [h0, zero_mul])
  have hb : D.b ≠ 0 := fun h0 => hab (by rw [h0, mul_zero])
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (Work.MotK.TGen.SdualTIrreducibleOfDisc K hk D.a D.b h ha hb hh
      (Work.MotK.TwCensus.GoodDiscNe K hk D hD))

end Work.MotK.TwCensus
