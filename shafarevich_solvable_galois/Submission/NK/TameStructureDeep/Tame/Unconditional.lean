/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The local structure theorem at every place, unconditionally

The last unproved field of the local structure residual was `abelianisation`
(`G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}`).  It is now a theorem
(`NK.TameStructureDeep.Tame.tameAbelianization_mulEquiv_zhat_mul_mu`), proved *group-theoretically*
from the Tate twist and the single Kummer layer `κ^{ur}(π^{1/(q-1)})` — no local class field theory.
Consequently the whole residual is a theorem at every `𝔭`-adic completion:

* `NK.TameStructureDeep.Tame.tameRamificationResidual_adicCompletion_residueChar`;
* `NK.TameStructureDeep.Tame.tameRamificationCore_adicCompletion_residueChar`;

and so are the structures of the input catalogue `Submission/Work/TameData/Definitions.lean`:

* `NK.TameStructureDeep.Tame.tameAbelianisationInput_adicCompletion_residueChar`;
* `NK.TameStructureDeep.Tame.tameTorsionInput_adicCompletion_residueChar`;
* `NK.TameStructureDeep.Tame.tameDataInput_adicCompletion_residueChar`.

Everything is `Type*`-polymorphic in `K'`.
-/
import Submission.NK.TameStructureDeep.Tame.tameAbelianization_mulEquiv_zhat_mul_mu
import Submission.NK.TameStructureDeep.Tame.TameQuotientKummer
import Submission.NK.TameStructureDeep.Assembly
import Submission.NK.TameStructureDeep.Data
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
  [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']

/-- **The reduced residual at every place, unconditionally.**  Its `abelianisation` field is
`NK.TameStructureDeep.Tame.tameAbelianization_mulEquiv_zhat_mul_mu`; the remaining fields are the
proved `TameQuotientKummer` (`isTameInertia` and `frobenius_iff`). -/
theorem tameRamificationResidual_adicCompletion_residueChar :
    NK.TameStructureDeep.TameRamificationResidual (resCharAt 𝔭)
      (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K' :=
  NK.TameStructureDeep.Tame.tameRamificationResidual_of_abelianisation 𝔭
    (NK.TameStructureDeep.Tame.tameAbelianization_mulEquiv_zhat_mul_mu K 𝔭)

/-- **The local structure theorem for `G_κ` at every place, unconditionally**: the six-field
residual `NK.TameStructureDeep.TameRamificationCore` at `κ = K_𝔭`, `p = resCharAt 𝔭` and
`q = residueCard K 𝔭`. -/
theorem tameRamificationCore_adicCompletion_residueChar :
    NK.TameStructureDeep.TameRamificationCore (resCharAt 𝔭)
      (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K' :=
  NK.TameStructureDeep.tameRamificationCore_adicCompletion 𝔭
    (tameRamificationResidual_adicCompletion_residueChar 𝔭)

/-- **Shimizu's splitting `G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}` at every place, unconditionally**
(`NK.TameData.TameAbelianisationInput`). -/
theorem tameAbelianisationInput_adicCompletion_residueChar :
    NK.TameData.TameAbelianisationInput (resCharAt 𝔭)
      (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K' where
  hp := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  q_eq := NK.TameStructureDeep.q_eq_of_charP 𝔭
    (NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭)
    (NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭)
  nonempty_iso := NK.TameStructureDeep.Tame.tameAbelianization_mulEquiv_zhat_mul_mu K 𝔭

/-- **Shimizu's literal torsion statement at every place, unconditionally**: the torsion of the
abelianised tame quotient is cyclic of order `q - 1`
(`NK.TameData.TameTorsionInput`). -/
theorem tameTorsionInput_adicCompletion_residueChar :
    NK.TameData.TameTorsionInput (resCharAt 𝔭)
      (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K' :=
  (tameAbelianisationInput_adicCompletion_residueChar 𝔭).toTorsionInput

/-- **The reduced input catalogue `NK.TameData.TameDataInput` at every place, unconditionally**:
`Submission/Work/TameData/Definitions.lean` discharged at `κ = K_𝔭`. -/
theorem tameDataInput_adicCompletion_residueChar :
    NK.TameData.TameDataInput (resCharAt 𝔭)
      (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K' :=
  NK.TameStructureDeep.tameDataInput_adicCompletion 𝔭
    (NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭)
    (tameRamificationCore_adicCompletion_residueChar 𝔭)

/-- **The structure of the tamely ramified layer at every place, unconditionally**: the compositum
of the Kummer layers `κ^{ur}(π^{1/n})` (`n` prime to `p`) is the maximal tamely ramified extension
and the input `TameQuotientKummer` holds there. -/
theorem tameQuotientKummer_adicCompletion_residueChar' :
    NK.TameStructureDeep.TameQuotientKummer (resCharAt 𝔭)
      (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K' :=
  tameQuotientKummer_adicCompletion_residueChar (K := K) (K' := K') 𝔭

end

end NK.TameStructureDeep.Tame
