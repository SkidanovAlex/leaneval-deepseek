import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.AK
import Submission.Work.MotAS.Nodes.fwVecAS2ThreeNotMemXProof

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASRulV2M.fwVecAS2_three_notMem_x` — the forward chart denominator is not in `x`

Let `𝕜` be a field of characteristic `5`, `D : Work.MotV.KleinData 𝕜` with `ASGood D`, and let `x` be
a height-one prime of `(RatFunc 𝕜)[X₀,X₁,X₂]` containing the source ruling quintic
`sAS2 (aK D) (bK D) (fAS 𝕜)`.  Then the third coordinate `fwVecAS2 ⋯ 3` of the forward chart map
does *not* vanish at `x`.  It is one of the two non-vanishing inputs of the K5 node
`Work.MotAS.ASRulingMain` (`Submission/Work/MotAS/ASRulingMain.lean`): it is exactly `c₃ ≠ 0` for
`c = kleinPAS a b g y`, i.e. the hypothesis `w ≠ 0` of
`Work.MotAS.ASRul.kernel_basis` / `Work.MotAS.ASRulV2M.hparam_kernel`.

## History

An earlier version of this file imported `Submission.Work.MotC5N3.fwVecAS2_three_notMem_x` and proved
a general-field form `fwVecAS2_three_notMem_x_gen` first.  That made the whole characteristic-`5`
chapter depend on a sibling subproject; the proof has since been redone self-containedly in
`Submission/Work/MotAS/Nodes/fwVecAS2ThreeNotMemXProof.lean` (whose header records the certificate:
`fwVecAS2 · 3 = C 4 · C A² · asH` with `A = a² − ab − b²`, `asH` irreducible and coprime to `sAS2`;
top-form comparison via `Work.MotK.TGen.TopFormMul`).  This module is now a one-line wrapper, so the
chapter no longer depends on `MotC5N3`.  The general-field statement `fwVecAS2_three_notMem_x_gen`
of the old version had no consumer and is gone; the general-base-field statement lives where it is
needed (`Work.MotC5N3.fwVecAS2_three_notMem_x_gen`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS.ASRulV2M

theorem fwVecAS2_three_notMem_x (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (x : Work.MotA.polySpec (RatFunc 𝕜) 3)
    (hcoh : Order.coheight x = 1)
    (hx : Work.MotAS.sAS2 (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal) :
    Work.MotAS.fwVecAS2 (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜) 3 ∉ x.asIdeal :=
  Work.MotAS.Nodes.fwVecAS2ThreeNotMemXProof 𝕜 D hD x hcoh hx

end Work.MotAS.ASRulV2M
