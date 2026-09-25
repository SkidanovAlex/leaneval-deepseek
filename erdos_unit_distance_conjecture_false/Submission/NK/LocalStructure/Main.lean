/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.LocalStructure.Main`: the reduced inputs, assembled into the vocabulary of the consumers

This file contains the *assembly* results of the chapter: it turns the reduced input catalogue
(`NK.LocalStructure.TameCore`, `TameFrobeniusCore`, `PrincipalUnitsCore`, `TowerRankCore`) into
the exact structures the Neukirch–Uchida development consumes
(`NK.LocalTame.TameStructureInput`, `NK.LocalTame.FrobeniusLiftCharacterisation`,
`NK.LocalInputs.LocalFieldInputs`, `NK.LocalInputs.LocalGaloisInputsOfUnits`,
`NK.LocalAnabelian.PadicGaloisInputs`).

The reductions themselves are proved in the sibling files of this directory (one lemma per file);
this file is only the glue that a caller imports.
-/
import Submission.NK.LocalStructure.Defs
import Submission.NK.LocalStructure.Tame.residueCard_eq_pow_of_charP
import Submission.NK.LocalStructure.Tame.exists_notMem_inertiaSubgroup_of_unramifiedQuotient
import Submission.NK.LocalStructure.Tame.tameStructureInput_of_core
import Submission.NK.LocalStructure.Frobenius.frobeniusLiftCharacterisation_of_core
import Submission.NK.LocalStructure.Power.natCard_pRootsOfUnity_eq_pow_zetaIndicator
import Submission.NK.LocalStructure.Power.principalUnits_card_of_core
import Submission.NK.LocalStructure.Tower.le_numIndexSubgroups_of_hasAbelianFrattiniRank
import Submission.NK.LocalStructure.Tower.hasUnboundedTowerRank_of_numIndexSubgroups_tower
import Submission.NK.LocalStructure.Tower.not_hasUnboundedTowerRank_of_card_extensions_le
import Submission.NK.LocalStructure.Tower.proP_unbounded_of_towerCore
import Submission.NK.LocalStructure.Tower.other_bounded_of_towerCore

open scoped Classical Pointwise
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalStructure

universe u

/-! ## The residue field cardinality -/

/-- The residue field cardinality of the completion is the absolute norm of the prime — the bridge
between `NK.LocalStructure.residueCard` and the global vocabulary used by
`Submission/Work/LocalInputs/` (`NK.LocalInputs.primeBelow`, `Ideal.absNorm`). -/
theorem residueCard_eq_absNorm {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    residueCard K 𝔭 = 𝔭.asIdeal.absNorm :=
  Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm 𝔭

/-! ## Item 1: the tame structure theorem -/

/-- **Item 1 discharged (modulo its reduced core).**  The reduced core `TameCore` for
`κ = 𝔭.adicCompletion K` yields the full `NK.LocalTame.TameStructureInput`: the two fields that
were dropped (`q_eq`, `exists_frobeniusLift`) are supplied by the arithmetic of the completion and
by the non-triviality of `Ẑ`, and `wildInertia_le_inertia` is part of `isTameInertia`. -/
theorem tameStructureInput_of_TameCore {p : ℕ} {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    (h : TameCore p K 𝔭 K') :
    NK.LocalTame.TameStructureInput p (residueCard K 𝔭) (𝔭.adicCompletion K) K' :=
  NK.LocalStructure.Tame.tameStructureInput_of_core 𝔭 h
    (NK.LocalStructure.Tame.residueCard_eq_pow_of_charP 𝔭 h.hp h.residue_char)
    (NK.LocalStructure.Tame.exists_notMem_inertiaSubgroup_of_unramifiedQuotient h.unramifiedQuotient)

/-! ## Item 2: the Frobenius normalisation -/

/-- **Item 2 discharged (modulo its reduced core).**  The reduced core `TameFrobeniusCore`
together with the commutator relation in the inertia (a field of `TameCore`) yields the full
`NK.LocalTame.FrobeniusLiftCharacterisation`. -/
theorem frobeniusLiftCharacterisation_of_cores {p q : ℕ} {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    (hT : TameCore p K 𝔭 K')
    (hF : TameFrobeniusCore p q (𝔭.adicCompletion K) K') :
    NK.LocalTame.FrobeniusLiftCharacterisation p q (𝔭.adicCompletion K) K' :=
  NK.LocalStructure.Frobenius.frobeniusLiftCharacterisation_of_core hF
    hT.tameInertia_commutator_mem

/-! ## Item 3: the `p`-power class count -/

/-- **Item 3 discharged (modulo its reduced core).**  The reduced core `PrincipalUnitsCore` (the
`p`-adic logarithm structure of the principal units) together with the residue characteristic
yields the arithmetic input `NK.LocalInputs.LocalFieldInputs`. -/
theorem localFieldInputs_of_core {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (h : PrincipalUnitsCore K 𝔭 p) :
    NK.LocalInputs.LocalFieldInputs K 𝔭 p where
  hp := h.hp
  residue_char := hres
  principal_units_card := NK.LocalStructure.Power.principalUnits_card_of_core 𝔭 h

/-- The `p`-power class count itself, in the form `|κˣ/(κˣ)^p| = p^{[κ:ℚ_p]+1+δ}` used by the
Kummer bridge of `NK.LocalAnabelian`: it is the contraction of the `principal_units_card` of
`NK.LocalInputs.LocalFieldInputs` with the triviality of the `p`-power quotient of the residue
units. -/
theorem natCard_KummerGroup_eq_pow_of_core {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (h : PrincipalUnitsCore K 𝔭 p) :
    Nat.card (NK.LocalAnabelian.KummerGroup p (𝔭.adicCompletion K)) =
      p ^ (NK.LocalInputs.localDegree K 𝔭 + 1 +
        NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K)) :=
  NK.LocalInputs.PowerQuotient.natCard_KummerGroup_eq_pow_of_principalUnits 𝔭 h.hp
    (NK.LocalInputs.PowerQuotient.natCard_residueUnits_quot_pow_eq_one 𝔭 h.hp hres)
    (NK.LocalStructure.Power.principalUnits_card_of_core 𝔭 h)

/-! ## Item 4: the tower ranks -/

/-- **Item 4 discharged (modulo its reduced core).**  The reduced core `TowerRankCore` together
with the three local-CFT-side inputs (`Lubin–Tate`, Nikolov–Segal openness of index-`p` subgroups,
and the `p`-torsion of the abelianisation) yields the full
`NK.LocalInputs.LocalGaloisInputsOfUnits`, i.e. Ivanov's Lemma 3.12 in the form in which
`Submission/Work/LocalInputs/` uses it. -/
theorem localGaloisInputsOfUnits_of_towerCore {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hT : TowerRankCore K 𝔭 K' p)
    (hlubinTate : NK.LocalReciprocity.LubinTateInput (𝔭.adicCompletion K) K')
    (hopen : ∀ H : Subgroup (Gal(K'/𝔭.adicCompletion K)), H.index = p → H.Normal →
      IsOpen (H : Set (Gal(K'/𝔭.adicCompletion K))))
    (htors : (NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K) = 1) ↔
      NK.LocalAnabelian.HasPTorsionAbelianization p (Gal(K'/𝔭.adicCompletion K))) :
    NK.LocalInputs.LocalGaloisInputsOfUnits K 𝔭 K' p where
  hp := hT.hp
  proP_unbounded := NK.LocalStructure.Tower.proP_unbounded_of_towerCore 𝔭 hT
  other_bounded := NK.LocalStructure.Tower.other_bounded_of_towerCore 𝔭 hT
  lubinTate := hlubinTate
  open_of_index_prime := hopen
  p_torsion_iff := htors

/-- **The instantiation of the local input `PadicGaloisInputs`** from the reduced catalogue: the
residue characteristic and the `p`-adic logarithm structure of the principal units (items 1–3)
together with the tower-rank core (item 4) and the three local-CFT-side inputs.  This is the form
in which `Submission/Work/LocalInputs/` and the Neukirch–Uchida endgame consume the local theory. -/
theorem padicGaloisInputs_of_core {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (hU : PrincipalUnitsCore K 𝔭 p)
    (hT : TowerRankCore K 𝔭 K' p)
    (hlubinTate : NK.LocalReciprocity.LubinTateInput (𝔭.adicCompletion K) K')
    (hopen : ∀ H : Subgroup (Gal(K'/𝔭.adicCompletion K)), H.index = p → H.Normal →
      IsOpen (H : Set (Gal(K'/𝔭.adicCompletion K))))
    (htors : (NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K) = 1) ↔
      NK.LocalAnabelian.HasPTorsionAbelianization p (Gal(K'/𝔭.adicCompletion K))) :
    NK.LocalAnabelian.PadicGaloisInputs p (NK.LocalInputs.localDegree K 𝔭)
      (NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K)) (𝔭.adicCompletion K) K' :=
  NK.LocalInputs.padicGaloisInputs_of_units 𝔭 K'
    (localFieldInputs_of_core 𝔭 hres hU)
    (localGaloisInputsOfUnits_of_towerCore 𝔭 hT hlubinTate hopen htors)

end NK.LocalStructure
