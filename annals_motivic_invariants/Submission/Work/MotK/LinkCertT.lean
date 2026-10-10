import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV.CTAux
import Submission.Work.MotK.TGenCensusWired
import Submission.Work.MotT.RouteVBridge
import Submission.Work.MotT.kleinDataBaseChange_good

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.LinkCertT` — the T-twist link certificate of the Crauder–Katz transformation

Target of this file: `Work.MotK.LinkCertT`, the K-route deliverable `LK_T` of
`MOTIVIC_S45_LEAD.md` §6 / `Submission/Work/MotK/GUIDE_LINK.md` §B: an affine certificate
`Work.MotV.LinkCert (RatFunc 𝕜) (twistFieldT D hT) (twistFieldT D (hT^2))` for the T-twist of the
Klein curve at the fixed Kummer class `hT 𝕜 = X(X-1)`.

## The route used here

The generic certificate `Work.MotK.LinkCertTGenInf` (sibling file `TGenCensusWired.lean`) proves the certificate for an
*arbitrary* infinite base field `K` of characteristic `≠ 5`, an arbitrary good Klein datum over `K`
and an arbitrary nonzero Kummer parameter `h ∈ K`:

```
LinkCertTGenInf (K) [Field K] [Infinite K] (hk : ringChar K ≠ 5)
    (D : KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) :
    Nonempty (LinkCert K (twistFieldTG K D h) (twistFieldTG K D (h ^ 2)))
```

and it is reduced there to its *census* `Work.MotK.TGenCensus`, whose four clauses are supplied by
`Work.MotK.TGen.SdualTClass`, `Work.MotK.TGen.STClass`, `Work.MotK.fwVec4JunkAll` and
`Work.MotK.cubTJunkAll` (see `TGenCensus_wired` in that file); the module docstring there records
the whole reduction.

The present file is the instantiation of that generic statement at route V's vocabulary:
`K := RatFunc 𝕜`, `D := Work.MotT.kleinDataBaseChange D (RatFunc 𝕜)`, `h := Work.MotV.hT 𝕜`,
using the definitional identifications of `Work.MotT.RouteVBridge`
(`twistFieldT D h = twistFieldTK (kleinDataBaseChange D (RatFunc 𝕜)) h`) and of
`Work.MotK.GenBridge` (`twistFieldTG = twistFieldTK`).  Note that `𝕜` is *not* assumed infinite: the
codimension-one count of the census is carried out over `RatFunc 𝕜`, which is infinite for every
field `𝕜`.
-/

namespace Work.MotK

open Work.MotV

theorem LinkCertT (𝕜 : Type) [Field 𝕜] (hk : ringChar 𝕜 ≠ 5) (D : Work.MotV.KleinData 𝕜)
    (hD : D.Good) :
    Nonempty (Work.MotV.LinkCert (RatFunc 𝕜) (Work.MotV.twistFieldT D (Work.MotV.hT 𝕜))
      (Work.MotV.twistFieldT D (Work.MotV.hT 𝕜 ^ 2))) := by
  haveI : Infinite (RatFunc 𝕜) :=
    Infinite.of_injective (algebraMap (Polynomial 𝕜) (RatFunc 𝕜))
      (RatFunc.algebraMap_injective 𝕜)
  have hkK : ringChar (RatFunc 𝕜) ≠ 5 := fun h5 =>
    hk (by rw [Algebra.ringChar_eq 𝕜 (RatFunc 𝕜)]; exact h5)
  exact LinkCertTGenInf (RatFunc 𝕜) hkK (Work.MotT.kleinDataBaseChange D (RatFunc 𝕜))
    (Work.MotT.kleinDataBaseChange_good D hD) (Work.MotV.hT 𝕜) (Work.MotV.hT_ne_zero 𝕜)

end Work.MotK
