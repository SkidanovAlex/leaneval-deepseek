import Mathlib
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.Nodes.linkCert_AS
import Submission.Work.MotAS.twistFieldAS_eq

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `LK_AS` from the explicit Galois-coordinate model of `MotAS`

Node **LK_AS** — a link certificate between the two Artin–Schreier twist fields of the Klein curve —
is the only missing input of the characteristic-`5` branch (`STATUS.md` §12.3).  The subproject
`Submission/Work/MotAS` produces the certificate for its *explicit* model
`Work.MotAS.twistFieldAS D g = K(y_j/y_0)` (node `LK_AS′`, `Work.MotAS.linkCertAS`); the bridge
from that model to `MotV5`'s fixed-field twist `Work.MotV5.asTwistFieldTrue D g τ σS` is node
**AS-EQ** (`Work.MotAS.twistFieldAS_eq`, proved and axiom-clean).

This module performs that last step: it turns *any* certificate for the two explicit model fields
into the `LK_AS` certificate consumed by `Work.MotV5.not_gen_charFive_of` (and hence by
`Work.MotV5.not_gen_charFive_all_of_linkCert`).  Concretely, once
`Work.MotAS.linkCertAS D hD` is available, `LK_AS` is the single application
`Work.MotV5.Nodes.linkCert_AS_of_twistFieldAS 𝕜 D hD τ τ₂ σS σ σ₂ h1 h2 L` with
`L := Work.MotAS.linkCertAS 𝕜 D hD`.
-/

set_option autoImplicit false

namespace Work.MotV5.Nodes

open Work.MotV

/-- **`LK_AS` from the `MotAS` model.**  A link certificate between the explicit Galois-coordinate
twist fields `Work.MotAS.twistFieldAS D (fAS 𝕜)` and `Work.MotAS.twistFieldAS D (2 • fAS 𝕜)`
transports, along node **AS-EQ**, to the certificate between the two `asTwistFieldTrue`s required
by the `MotV5` assembly. -/
theorem linkCert_AS_of_twistFieldAS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (τ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ σ₂ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h1 : Work.MotV5.ASTwistData 𝕜 D (Work.MotV.fAS 𝕜) τ σS σ)
    (h2 : Work.MotV5.ASTwistData 𝕜 D (2 • Work.MotV.fAS 𝕜) τ₂ σS σ₂)
    (L : Work.MotV.LinkCert (RatFunc 𝕜)
      ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
      ↥(Work.MotAS.twistFieldAS D (2 • Work.MotV.fAS 𝕜))) :
    Nonempty (Work.MotV.LinkCert (RatFunc 𝕜)
      ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS)
      ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS)) :=
  linkCert_AS_of_CK 𝕜 D hD τ τ₂ σS σ σ₂ h1 h2
    (F₁' := ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
    (F₂' := ↥(Work.MotAS.twistFieldAS D (2 • Work.MotV.fAS 𝕜))) L
    (IntermediateField.equivOfEq
      (Work.MotAS.twistFieldAS_eq D hD (Work.MotV.fAS 𝕜) τ σS σ h1))
    (IntermediateField.equivOfEq
      (Work.MotAS.twistFieldAS_eq D hD (2 • Work.MotV.fAS 𝕜) τ₂ σS σ₂ h2))

end Work.MotV5.Nodes
