import Mathlib
import Submission.Work.MotK.LinkCertTGenInf
import Submission.Work.MotK.TGen.SdualTClass
import Submission.Work.MotK.TGen.STClass
import Submission.Work.MotK.GenBridge

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The census of the T-twisted Crauder--Katz link, and the generic certificate

This file proves the *census* `Work.MotK.TGenCensus` of the T-twisted Crauder--Katz link and
deduces from it the generic certificate `Work.MotK.LinkCertTGenInf`.

## Why the census is three lines

`Work.MotK.TGenCensus K D h` (`Submission/Work/MotK/LinkCertTGenInf.lean`) is deliberately stated in
the form in which its four clauses are *literally* the four statements available in the workspace:

| clause | factor | supplied by |
|---|---|---|
| the distinguished height-one point `zP` and its residue field | `sdualT` (quintic, target ruling) | `Work.MotK.TGen.SdualTClass` |
| every codimension-one point of the source ruling divisor is of class `RatFunc (twistFieldTG K D (h²))` or junk | `sT` (degree 10) | `Work.MotK.TGen.STClass` |
| every codimension-one point above `f̂₄` is junk | `fwVec a b h 4` (quartic) | `Work.MotK.fwVec4JunkAll` |
| every codimension-one point above the target cone is junk | `cubT` (cubic) | `Work.MotK.cubTJunkAll` |

The remaining step — that the census implies the certificate — is the proved
`Work.MotK.linkCertTGenInf_of_census`, which is pure height-one bookkeeping in the UFD
`K[x₀,x₁,x₂]`: a height-one prime above a product contains one of the factors
(`Ideal.IsPrime.mem_or_mem`), and a height-one prime above a principal prime *is* that prime
(`Work.MotK.CensusPrime.eq_span_of_height_one`); the necessary non-vanishing
(`Fdiv ≠ 0`, `Gdiv ≠ 0`) and the chart isomorphism `Φ` (`TGen.chartIsoT`) are proved in sibling
files.

## Where this file sits in the import graph

`Work.MotK.TGen.STClass` needs `Work.MotK.TGen.STRulingDiv`, which in turn imports
`Submission/Work/MotK/LinkCertTGenInf.lean` for its junk helpers (`fwVec4JunkAll`, `cubTJunkAll`,
...).  Hence `TGenCensus`'s producer cannot live in `LinkCertTGenInf.lean` without creating an
import cycle, which is why it — and the certificate `Work.MotK.LinkCertTGenInf` itself — are stated
here instead.

## Consumers

* `Work.MotK.LinkCertT` (`Submission/Work/MotK/LinkCertT.lean`), the certificate at route V's
  vocabulary, applies `LinkCertTGenInf` at `K := RatFunc 𝕜`, the base-changed Klein datum, and
  `h := Work.MotV.hT 𝕜`;
* `Work.MotT.LinkCertTInput K` (audit node T8) is the `∀ D hD h hh`-form of `LinkCertTGenInf`, and
  is obtained from it by `Work.MotK.linkCertTInput_transfer`
  (`Submission/Work/MotK/GenBridge.lean`).
-/

set_option autoImplicit false

namespace Work.MotK

/-- **The census of the T-twisted link.**  For an infinite field `K` of characteristic `≠ 5`, a good
Klein datum `D` and `h ≠ 0`, the four clauses of `Work.MotK.TGenCensus K D h` hold.

The two "class" clauses are `Work.MotK.TGen.SdualTClass` and `Work.MotK.TGen.STClass`; the two
"junk" clauses are `Work.MotK.fwVec4JunkAll` and `Work.MotK.cubTJunkAll`, which convert the proved
prime forms (`Work.MotK.TGen.FwVec4Rational`, `Work.MotK.TGen.CubTRational`) into the divisor form
by `Work.MotK.junkAll_of_prime`.  The hypotheses `D.a ≠ 0`, `D.b ≠ 0` come from `D.Good`. -/
theorem TGenCensus_wired (K : Type) [Field K] [Infinite K] (hk : ringChar K ≠ 5)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) :
    TGenCensus K D h := by
  have hab := hD.ab_ne
  have ha : D.a ≠ 0 := fun h0 => hab (by rw [h0, zero_mul])
  have hb : D.b ≠ 0 := fun h0 => hab (by rw [h0, mul_zero])
  exact ⟨TGen.SdualTClass K hk D hD h hh, TGen.STClass K hk D hD h hh,
    fwVec4JunkAll D.a D.b h ha hb hh, cubTJunkAll D.a D.b h ha hb hh⟩

/- **Note.**  The certificate itself now lives in `Submission/Work/MotK/LinkCertTGenInf.lean` (module
`Submission.Work.MotK.LinkCertTGenInf`), where it is stated as `Work.MotK.LinkCertTGenInf` and proved
from the same assembly as `TGenCensus_wired` above.  It is stated there because the import cycle
that had forced it out of that file is broken by `Submission/Work/MotK/TGen/JunkConversions.lean`. -/

end Work.MotK
