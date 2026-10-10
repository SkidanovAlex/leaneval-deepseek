import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Submission.Work.SSGRoute.local_lifting_setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The vocabulary of `Work.SSGRoute.local_tame_lifting`

This module fixes the objects that the proof of `Work.SSGRoute.local_tame_lifting` (part (a))
manipulates, so that they can be named in the statements of the auxiliary lemmas the argument
needs:

* `Work.SSGRoute.globalInertiaSub A'` — the inertia subgroup `I_A ≤ D_A` as a subgroup of the
  decomposition group `D_A = ↥(SSGRoute.decomp ℚ A.1)`;
* `Work.SSGRoute.levelSubQBar A' L` — the preimage in `D_A` of the inertia subgroup of a finite normal
  level `L/ℚ` (the elements acting trivially on the residue field of `L` at the prime below `A`);
* `Work.SSGRoute.localInertia A'` — the local inertia subgroup `I_κ ≤ Gal(κ̄/κ)`;
* `Work.SSGRoute.localTameData A'` — the local structure theory at the place, transported to the
  residue characteristic `Work.SSGRoute.residueChar A'` of `A`;
* `Work.SSGRoute.localZhatHom A' : D_A →* Ẑ` — the quotient map
  `D_A ↠ D_A/I_A ≅ Gal(κ̄/κ)/I_κ ≅ Ẑ`;
* `Work.SSGRoute.localFrobElem A'` — a chosen preimage of the canonical (topological) generator
  `1 ∈ Ẑ` under `localZhatHom A'`, i.e. a Frobenius element of `D_A`.

It also records the elementary arithmetic of the residue characteristic `residueChar A` of a finite
place of `ℚ̄` (`residueChar_prime`, `residueChar_eq_resCharAt`) and the two unconditional local
facts `tameData_rat`, `exists_localFrob`.
-/

open SSGRoute
open IsDedekindDomain

namespace Work.SSGRoute

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.defProp false

/-! ## The residue characteristic -/

/-- **A finite field whose cardinality is a prime has that prime as its characteristic.** -/
theorem ringChar_eq_of_card_prime (F : Type*) [Field F] [Finite F] (l : ℕ) (hl : l.Prime)
    (h : Nat.card F = l) : ringChar F = l := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hpp, hc⟩ := FiniteField.card F (ringChar F)
  have hcard : Fintype.card F = l := by rw [← Nat.card_eq_fintype_card, h]
  have hpn : (ringChar F) ^ (n : ℕ) = l := by rw [← hc, hcard]
  have hdvd : ringChar F ∣ l := hpn ▸ dvd_pow_self _ (by exact_mod_cast n.2.ne')
  exact ((Nat.Prime.dvd_iff_eq hl hpp.ne_one).mp hdvd).symm

/-- **The residue characteristic of a finite place of `ℚ̄` agrees with the residue characteristic
of the completion.** -/
theorem residueChar_eq_resCharAt (A : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) :
    residueChar A =
      NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A.1 A.2) := by
  set 𝔭 := Submission.NeukirchUchida.primeOf A.1 A.2 with h𝔭
  have h1 : residueChar A = NK.LocalStructure.residueCard ℚ 𝔭 := by
    unfold residueChar NK.LocalStructure.residueCard
    have h1 : Nat.card (NumberField.RingOfIntegers ℚ ⧸ 𝔭.asIdeal) = Ideal.absNorm 𝔭.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [h1, Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm]
  have h2 : NK.TameStructureDeep.Tame.resCharAt 𝔭 =
      (Rat.HeightOneSpectrum.primesEquiv 𝔭 : ℕ) := by
    haveI : Finite (IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ 𝔭)) :=
      Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion ℚ 𝔭
    have hcard : Nat.card (IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ 𝔭)) =
        (Rat.HeightOneSpectrum.primesEquiv 𝔭 : ℕ) := by
      rw [Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm,
        Commons.NumberTheory.NumberField.Set.absNorm_eq_primesEquiv]
    exact ringChar_eq_of_card_prime _ _ (Rat.HeightOneSpectrum.primesEquiv 𝔭).2 hcard
  rw [h1, NK.LocalStructure.residueCard,
    Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm,
    Commons.NumberTheory.NumberField.Set.absNorm_eq_primesEquiv, h2]

/-- **The residue characteristic of a finite place of `ℚ̄` is prime.** -/
theorem residueChar_prime (A : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) :
    (residueChar A).Prime := by
  rw [residueChar_eq_resCharAt A]
  exact NK.Mine.prime_ringChar_residueField_adicCompletion
    (Submission.NeukirchUchida.primeOf A.1 A.2)

/-- The residue-cardinality normalisation of `NK.ResidueFrob.ResidueCardMatches` holds for the
residue characteristic. -/
theorem residueCardMatches_residueChar (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) :
    NK.ResidueFrob.ResidueCardMatches A' (Work.SSGRoute.residueChar A') := by
  have h1 : residueChar A' = NK.LocalStructure.residueCard ℚ
      (Submission.NeukirchUchida.primeOf A'.1 A'.2) := by
    unfold residueChar NK.LocalStructure.residueCard
    have h1 : Nat.card (NumberField.RingOfIntegers ℚ ⧸
        (Submission.NeukirchUchida.primeOf A'.1 A'.2).asIdeal) =
        Ideal.absNorm (Submission.NeukirchUchida.primeOf A'.1 A'.2).asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [h1, Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm]
  rw [NK.ResidueFrob.ResidueCardMatches, h1]
  unfold NK.LocalStructure.residueCard
  rw [Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm,
    Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-! ## The local structure theory at the place -/

/-- **The local structure theory at a finite place of `ℚ̄`**, at the residue characteristic
`residueChar A`. -/
theorem tameData_rat (A : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) :
    NK.LocalTame.TameData (residueChar A)
      (NK.LocalStructure.residueCard ℚ (Submission.NeukirchUchida.primeOf A.1 A.2))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A) := by
  suffices h : NK.LocalTame.TameData
      (NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A.1 A.2))
      (NK.LocalStructure.residueCard ℚ (Submission.NeukirchUchida.primeOf A.1 A.2))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A) by
    rwa [residueChar_eq_resCharAt A]
  exact NK.TameData.TameDataInput.toTameData
    (NK.TameStructureDeep.Tame.tameDataInput_adicCompletion_residueChar
      (Submission.NeukirchUchida.primeOf A.1 A.2))

/-- **A local Frobenius element at the place.** -/
theorem exists_localFrob (A : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) :
    ∃ u : Gal(NK.FrobeniusBridge.localClosure A/NK.FrobeniusBridge.localField A),
      NK.LocalAnabelian.IsFrobeniusFor (residueChar A)
        (NK.LocalStructure.residueCard ℚ (Submission.NeukirchUchida.primeOf A.1 A.2)) u := by
  suffices h : ∃ u : Gal(NK.FrobeniusBridge.localClosure A/NK.FrobeniusBridge.localField A),
      NK.LocalAnabelian.IsFrobeniusFor
        (NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A.1 A.2))
        (NK.LocalStructure.residueCard ℚ (Submission.NeukirchUchida.primeOf A.1 A.2)) u by
    rw [residueChar_eq_resCharAt A]
    exact h
  exact (NK.TameStructureDeep.Tame.tameRamificationCore_adicCompletion_residueChar
    (Submission.NeukirchUchida.primeOf A.1 A.2)).exists_frobenius

/-! ## The group-theoretic vocabulary -/

/-- **The inertia subgroup `I_A ≤ D_A`**, as a subgroup of the decomposition group. -/
noncomputable def globalInertiaSub (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) :
    Subgroup ↥(SSGRoute.decomp ℚ A'.1) :=
  Subgroup.closure {g : ↥(SSGRoute.decomp ℚ A'.1) |
    SSGRoute.IsInertia ℚ A'.1 (g : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar)}

/-- **The level subgroup**: the elements of `D_A` acting trivially on the residue field of the
finite normal level `L/ℚ` at the prime below `A`. -/
noncomputable def levelSubQBar (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [Normal ℚ L]
    [NumberField ↥L] : Subgroup ↥(SSGRoute.decomp ℚ A'.1) :=
  Subgroup.closure {g : ↥(SSGRoute.decomp ℚ A'.1) |
    Work.SSGRoute.IsTrivialAtLevelQBar A' L (g : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar)}

/-- The local inertia subgroup `I_κ ≤ Gal(κ̄/κ)` at the place `A`. -/
noncomputable abbrev localInertia (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) :
    Subgroup (Gal(NK.FrobeniusBridge.localClosure A'/NK.FrobeniusBridge.localField A')) :=
  NK.LocalAnabelian.inertiaSubgroup (κ := NK.FrobeniusBridge.localField A')
    (K' := NK.FrobeniusBridge.localClosure A') (Work.SSGRoute.residueChar A')

/-- **The local structure theory at the place `A`, as a definition**. -/
noncomputable def localTameData (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) :
    NK.LocalTame.TameData (Work.SSGRoute.residueChar A')
      (NK.LocalStructure.residueCard ℚ (Submission.NeukirchUchida.primeOf A'.1 A'.2))
      (NK.FrobeniusBridge.localField A') (NK.FrobeniusBridge.localClosure A') :=
  Work.SSGRoute.tameData_rat A'

/-- **The quotient map `D_A ↠ Ẑ`** through which all the unramified (Frobenius) information at the
place flows: `D_A → Gal(κ̄/κ) → Gal(κ̄/κ)/I_κ ≃* Ẑ`, where the last isomorphism is the
`unramifiedQuotient` field of the local structure theory. -/
noncomputable def localZhatHom (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) :
    ↥(SSGRoute.decomp ℚ A'.1) →* NK.LocalAnabelian.Zhat :=
  let ψ : (Gal(NK.FrobeniusBridge.localClosure A'/NK.FrobeniusBridge.localField A') ⧸
      localInertia A') ≃* NK.LocalAnabelian.Zhat :=
    Classical.choice ((localTameData A').structure_input.unramifiedQuotient)
  ψ.toMonoidHom.comp ((QuotientGroup.mk' (localInertia A')).comp
    (NK.FrobeniusBridge.localGaloisEquiv A').toMonoidHom)

/-- **The quotient map is surjective.** -/
theorem localZhatHom_surjective (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) :
    Function.Surjective (localZhatHom A') :=
  (MulEquiv.surjective (Classical.choice
      ((localTameData A').structure_input.unramifiedQuotient))).comp
    ((QuotientGroup.mk'_surjective (localInertia A')).comp
      (MulEquiv.surjective (NK.FrobeniusBridge.localGaloisEquiv A')))

/-- **A chosen Frobenius element of `D_A`**: a preimage of the canonical topological generator
`1 ∈ Ẑ`. -/
noncomputable def localFrobElem (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) :
    ↥(SSGRoute.decomp ℚ A'.1) :=
  Classical.choose (localZhatHom_surjective A' NK.TowerRank.zhatGen)

/-- The defining property of the chosen Frobenius element. -/
theorem localZhatHom_localFrobElem (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) :
    localZhatHom A' (localFrobElem A') = NK.TowerRank.zhatGen :=
  Classical.choose_spec (localZhatHom_surjective A' NK.TowerRank.zhatGen)


end Work.SSGRoute
