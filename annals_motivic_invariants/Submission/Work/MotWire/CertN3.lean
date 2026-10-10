/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotWire
-/
import Mathlib
import ChallengeDeps
import Submission.Work.MotT.certN3_of_linkCert
import Submission.Work.MotV.not_gen_of_certN

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

/-!
# The `n = 3` certificate level: the precise target of the characteristic-`5` input

For `K` any field, a *link certificate* `Work.MotV.LinkCert K F₁ F₂` at the base field `K` together
with

* `Work.MotV.ConstantsOnly K F₁` (the constants-only node), and
* `IsEmpty (F₁ ≃ₐ[K] F₂)` (the rigidity node),

gives `¬ GenByPseudoRegularizable K 3` — no spreading is needed (`n = 3` is the certificate level of
`Work.MotV.CertN`, node **T9** of the T-route) and no hypothesis on the characteristic is needed.

This is the shape in which the residual characteristic-`5` case of `theorem_1_2_1 (c)`, `(d)` —
i.e. the `n = 3` half `Work.MotWire.CharFiveInputThree` of the single input
`Work.MotWire.CharFiveInput` — becomes concrete: it is enough to produce, for every infinite field
`K` of characteristic `5`, two `K`-fields `F₁`, `F₂` with such a certificate.  Compare
`Submission/Work/MotWire/README.md` §2.3: in characteristic `≠ 5` the certificate is
`Work.MotK.LinkCertTGenInf` with `F₁`, `F₂` the two T-twist fields, and the constants-only and
rigidity nodes are `Work.MotT.constantsOnly_twistK` and `Work.MotT.rigidityK`; in characteristic `5`
the corresponding Artin–Schreier objects exist in `Submission/Work/MotV5` only over `RatFunc 𝕜`.

The statement belongs to the interface of this area, not to its wire: it is not an input, it is the
reduction that a future characteristic-`5` subproject should aim at.
-/

namespace Work.MotWire

open MotivicInvariants (GenByPseudoRegularizable)

/-- **The `n = 3` certificate level.**  A `K`-level link certificate whose `G`-side class field is
constants-only and whose two class fields are not `K`-isomorphic forces
`¬ GenByPseudoRegularizable K 3`. -/
theorem not_gen_three_of_linkCert (K : Type) [Field K] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Algebra K F₁] [Algebra K F₂] (L : Work.MotV.LinkCert K F₁ F₂)
    (hCO : Work.MotV.ConstantsOnly K F₁) (hR : IsEmpty (F₁ ≃ₐ[K] F₂)) :
    ¬ GenByPseudoRegularizable K 3 :=
  Work.MotV.not_gen_of_certN (Classical.choice (Work.MotT.certN3_of_linkCert K L hCO hR))

end Work.MotWire
