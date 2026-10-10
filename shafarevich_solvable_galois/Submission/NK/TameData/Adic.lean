import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.LocalStructure.Main
import Submission.NK.TameData.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open NK.LocalTame

set_option linter.unusedSectionVars false

namespace NK.TameData

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- **The structure theorem for the `𝔭`-adic completion of a number field**, with residue field
cardinality `q = #(𝓞 K ⧸ 𝔭) = NK.LocalStructure.residueCard K 𝔭` and residue characteristic `p`:

  `TameData p (residueCard K 𝔭) (𝔭.adicCompletion K) K'`.

The residue field cardinality is the absolute norm of `𝔭`
(`NK.LocalStructure.residueCard_eq_absNorm`). -/
theorem tameData_adicCompletion
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hT : NK.LocalStructure.TameCore p K 𝔭 K')
    (hA : TameAbelianisationInput p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K')
    (hF : NK.LocalStructure.TameFrobeniusCore p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K') :
    TameData p (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K' where
  structure_input := NK.LocalStructure.tameStructureInput_of_TameCore 𝔭 hT
  residueCard := ResidueCardRecovery.of_abelianisation hA
  frobeniusLift := NK.LocalStructure.frobeniusLiftCharacterisation_of_cores 𝔭 hT hF

/-- **The structure theorem for the `𝔭`-adic completion of a number field**, from Shimizu's
literal torsion statement (no property of `Ẑ` is needed on this route). -/
theorem tameData_adicCompletion_of_torsionInput
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hT : NK.LocalStructure.TameCore p K 𝔭 K')
    (hTs : TameTorsionInput p (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K')
    (hF : NK.LocalStructure.TameFrobeniusCore p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K') :
    TameData p (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K' where
  structure_input := NK.LocalStructure.tameStructureInput_of_TameCore 𝔭 hT
  residueCard := ResidueCardRecovery.of_torsionInput hTs
  frobeniusLift := NK.LocalStructure.frobeniusLiftCharacterisation_of_cores 𝔭 hT hF

/-- The same statement with `K'` specialised to the separable closure of the completion — the
exact shape used by `Submission/Work/FrobeniusBridge/` (`localClosure`). -/
theorem tameData_separableClosure
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hT : NK.LocalStructure.TameCore p K 𝔭 (SeparableClosure (𝔭.adicCompletion K)))
    (hA : TameAbelianisationInput p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) (SeparableClosure (𝔭.adicCompletion K)))
    (hF : NK.LocalStructure.TameFrobeniusCore p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) (SeparableClosure (𝔭.adicCompletion K))) :
    TameData p (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K)
      (SeparableClosure (𝔭.adicCompletion K)) :=
  tameData_adicCompletion 𝔭 hT hA hF

/-- **`ResidueCardRecovery` is insensitive to the name of `q`**: it only uses the numerical value
of the residue field cardinality.  This lets a caller who knows
`q = #(𝓞 K ⧸ 𝔭) = 𝔭.asIdeal.absNorm` rewrite the residue field order in the packaged theorem. -/
theorem residueCardRecovery_congr {p q q' : ℕ} {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] (h : ResidueCardRecovery p q κ K') (hq : q = q') :
    ResidueCardRecovery p q' κ K' where
  hp := h.hp
  q_eq := hq ▸ h.q_eq
  card_torsion := hq ▸ h.card_torsion

/-! ## The completion vocabulary and the general vocabulary agree -/

/-- **The reduced input of `Submission/Work/LocalStructure/` is an instance of the general one**:
the fields of `NK.LocalStructure.TameCore` are exactly the fields of
`NK.TameData.TameInertiaInput` at the completion (the former carries the residue characteristic
`CharP` in place of the abstract `q_eq`, which the caller supplies separately). -/
def TameInertiaInput.ofTameCore
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (h : NK.LocalStructure.TameCore p K 𝔭 K') :
    TameInertiaInput p (𝔭.adicCompletion K) K' where
  hp := h.hp
  isTameInertia := h.isTameInertia
  isProPrimeToP_tameInertia := h.isProPrimeToP_tameInertia
  tameInertia_commutator_mem := h.tameInertia_commutator_mem
  unramifiedQuotient := h.unramifiedQuotient

end NK.TameData
