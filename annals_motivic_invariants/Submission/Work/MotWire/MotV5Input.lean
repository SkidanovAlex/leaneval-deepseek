/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotWire
-/
import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.NotGenCharFive
import Submission.Work.MotWire.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The characteristic-`5`, `n ≥ 4` half of the input, in `MotV5`'s vocabulary

`Work.MotV5.not_gen_charFive_all_of_linkCert` (`Submission/Work/MotV5/NotGenCharFive.lean`,
axiom-clean) produces

  `∀ 𝕜 [Field 𝕜] [Infinite 𝕜], ringChar 𝕜 = 5 → ∀ n ≥ 4, ¬ GenByPseudoRegularizable 𝕜 n`

from a single hypothesis, namely the existence — for every infinite field `𝕜` of characteristic `5`
— of admissible Klein data `D` with `ASGood D`, of the twisting data `τ`, `τ₂`, `σS`, `σ`, `σ₂`
satisfying the two `ASTwistData` bundles, and of a Crauder–Katz link certificate between the two
Artin–Schreier twist fields (audit node **LK_AS**).

This module names that hypothesis (`MotV5LinkCertInput`) and records the consequence: the `n ≥ 4`
half of `Work.MotWire.CharFiveInput` is *exactly* the `MotV5` certificate hypothesis, so it is not
new content of the input.  Consequently

  `CharFiveInput` ⟺ `CharFiveInputThree` + `MotV5LinkCertInput`,

and the genuinely open piece of the characteristic-`5` branch of Lin–Shinder in this workspace is
the `n = 3` statement `CharFiveInputThree`.

(The sharper form of the hypothesis — with the Crauder–Katz *census* `Work.MotAS.CensusAS D hD`
instead of the certificate itself — is `Work.MotV5.not_gen_charFive_all_of_censusAS`, which is not
importable here because its module `Submission/Work/MotV5/Nodes/linkCert_AS_of_censusAS.lean`
depends on the still-unbuilt `Submission.Work.MotAS` tree.  As soon as it builds, the statement
below can be replaced by the census form without any other change.)
-/

namespace Work.MotWire

/-- **The certificate hypothesis of the characteristic-`5`, `n ≥ 4` branch**, verbatim the hypothesis
of `Work.MotV5.not_gen_charFive_all_of_linkCert`: for every infinite field `𝕜` of characteristic `5`
there are admissible Klein data, the two Artin–Schreier twisting bundles, and the Crauder–Katz link
certificate between the two twist fields. -/
def MotV5LinkCertInput : Prop :=
  ∀ (𝕜 : Type) [Field 𝕜] [Infinite 𝕜], ringChar 𝕜 = 5 →
    ∃ (D : Work.MotV.KleinData 𝕜)
      (τ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
      (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
      (σ σ₂ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜),
      Work.MotV5.KleinData.ASGood D ∧
      Work.MotV5.ASTwistData 𝕜 D (Work.MotV.fAS 𝕜) τ σS σ ∧
      Work.MotV5.ASTwistData 𝕜 D (2 • Work.MotV.fAS 𝕜) τ₂ σS σ₂ ∧
      Nonempty (Work.MotV.LinkCert (RatFunc 𝕜)
        ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS)
        ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS))

/-- **The `n ≥ 4` half of the input, from the `MotV5` certificate hypothesis.**  This is the
delivered characteristic-`5` branch `Work.MotV5.not_gen_charFive_all_of_linkCert`; the node
**CO_AS** (`Work.MotV5.Nodes.constantsOnly_AS`) and the node **RIG_AS**
(`Work.MotV5.Nodes.rigidity_AS`) are discharged inside it. -/
theorem charFiveInputN4_of_motV5 (h : MotV5LinkCertInput) : CharFiveInputN4 :=
  fun 𝕜 _ _ hk {n} hn => Work.MotV5.not_gen_charFive_all_of_linkCert h 𝕜 hk hn

/-- **The single input from its `n = 3` half and the `MotV5` certificate hypothesis.**  In other
words: apart from the `n = 3` case, the characteristic-`5` input is exactly the already-formulated
`MotV5` certificate hypothesis, and nothing else. -/
theorem charFiveInput_of_three_and_motV5 (h3 : CharFiveInputThree) (h : MotV5LinkCertInput) :
    CharFiveInput :=
  charFiveInput_of_parts h3 (charFiveInputN4_of_motV5 h)

end Work.MotWire
