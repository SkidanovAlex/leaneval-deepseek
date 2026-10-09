import Mathlib
import Submission.NK.CFTLib.HR.isCyclotomic_onePlace_real
import Submission.NK.CFTLib.HR.localNormSubgroup_ofInfinite_eq_top
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Cyclotomic levels are totally complex, and their local norm subgroups at infinite places are trivial

Two small consequences of `NK.CFTLib.HR.isComplex_infinitePlace_of_isCyclotomic_neZero` and
`NK.CFTLib.HR.localNormSubgroup_ofInfinite_eq_top_of_isTotallyComplex`, used by the design's step
L7 (`Submission/Work/CFTLib/HR/STATUS_proof_owner.md`): for the auxiliary
`M = K(ζ_q)` (`q > 2`, so `M` is totally complex) the local condition
`hv₀` at an *infinite* place of `M` is vacuous — every element of `M_wˣ` is a norm from `E_w`
for **any** finite Galois `E/M`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open scoped NumberField

namespace NK.CFTLib.HR

/-- **A cyclotomic extension of conductor `m > 2` of a number field is totally complex**: every
infinite place of `K(ζ_m)` is complex (`isComplex_infinitePlace_of_isCyclotomic_neZero`). -/
theorem isTotallyComplex_of_isCyclotomicExtension {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {m : ℕ} [NeZero m] (hm : 2 < m) [IsCyclotomicExtension {m} K L] :
    NumberField.IsTotallyComplex L :=
  ⟨fun v => isComplex_infinitePlace_of_isCyclotomic_neZero (K := K) (L := L) hm v⟩

/-- **The local norm subgroup at an infinite place is everything for a level over a cyclotomic
field of conductor `> 2`.** -/
theorem localNormSubgroup_ofInfinite_eq_top_of_isCyclotomicExtension
    {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E]
    [Algebra K M] [Algebra M E] [FiniteDimensional K M] [FiniteDimensional M E]
    [IsGalois K M] [IsGalois M E]
    {m : ℕ} [NeZero m] (hm : 2 < m) [IsCyclotomicExtension {m} K M]
    (w : NumberField.InfinitePlace M) :
    NK.CFTLib.IdeleHasse.localNormSubgroup (K := M) (L := E)
      (NK.GlobalCFT.Place.ofInfinite w) = ⊤ :=
  localNormSubgroup_ofInfinite_eq_top_of_isTotallyComplex
    (isTotallyComplex_of_isCyclotomicExtension (K := K) (L := M) hm) w

end NK.CFTLib.HR
