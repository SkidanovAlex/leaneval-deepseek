/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Submission.Work.FFResidual.CharP.Order
import Submission.Work.FFResidual.CharP.isDomain_asOrder
import Submission.Work.FFResidual.CharP.isDiscreteValuationRing_asOrder
import Submission.Work.FFResidual.CharP.isFractionRing_asOrder
import Submission.Work.FFResidual.CharP.modelPreserves_asOrder
import Submission.Work.FFResidual.CharP.modelResidueTrivial_asOrder
import Submission.Work.FFResidual.CharP.hasGoodReduction_asOrder

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The local model of the Artin–Schreier place (characteristic five)

This file collects the local theory of the place of the function field `𝕜` at the Artin–Schreier
extension `AsTop P = 𝕜(s)`, `s ^ 5 - s = π⁻¹`:

* `AsOrder P = R[X]/(X ^ 5 + π X ^ 4 - π) = R[w]`, `w = s⁻¹`, is a discrete valuation ring with
  fraction field `AsTop P` (instances `isDomain_asOrder`, `isDiscreteValuationRing_asOrder`,
  `isFractionRing_asOrder`);
* the Artin–Schreier automorphism `s ↦ s + 1` preserves the model and acts trivially on its
  residue field (`modelPreserves_asOrder`, `modelResidueTrivial_asOrder`);
* the constant Tate model has good reduction at the model (`hasGoodReduction_asOrder`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.FFResidual

noncomputable section

namespace FunctionFieldPlace

variable {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]

/-- The Artin–Schreier order of the place is a domain. -/
instance isDomain_asOrderInst (P : FunctionFieldPlace 𝔽 𝕜) : IsDomain P.AsOrder :=
  Work.FFResidual.CharP.isDomain_asOrder P

/-- The Artin–Schreier order of the place is a discrete valuation ring. -/
instance isDiscreteValuationRing_asOrderInst (P : FunctionFieldPlace 𝔽 𝕜) :
    IsDiscreteValuationRing P.AsOrder :=
  Work.FFResidual.CharP.isDiscreteValuationRing_asOrder P

/-- The Artin–Schreier order of the place has fraction field the top field. -/
instance isFractionRing_asOrderInst (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    IsFractionRing P.AsOrder P.AsTop :=
  Work.FFResidual.CharP.isFractionRing_asOrder P

instance decEqResidueAsOrder (P : FunctionFieldPlace 𝔽 𝕜) :
    DecidableEq (IsLocalRing.ResidueField P.AsOrder) :=
  Classical.decEq _

end FunctionFieldPlace

end

end Work.FFResidual
