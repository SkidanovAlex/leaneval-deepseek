import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.TameStructureDeep.Tame.residue_adicCompletionMap_pow_card_eq_self
import Submission.NK.TameStructureDeep.Tame.units_mem_pow_of_residue_pow_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

namespace NK.TameStructureDeep.Tame

/-- **Lifting an `ℓ`-th root of a unit through a tower of completions.**

Let `K ⊆ L₁ ⊆ L₂` be number fields, `𝔭 ⊂ 𝔮₁ ⊂ 𝔮₂` a tower of primes with `𝔮₂/𝔮₁`
unramified (`e = 1`), and `ℓ` a prime different from the residue characteristic `p` of `𝔭`.
Assume the residue field of `𝔮₁` has cardinality `q ^ d` and that of `𝔮₂` has cardinality
`q ^ (d * ℓ * (ℓ - 1))`, where `q` is the residue cardinality of `𝔭`.

Then every unit `u` of the integers of the `𝔮₁`-adic completion of `L₁` has an `ℓ`-th root
among the units of the integers of the `𝔮₂`-adic completion of `L₂`; precisely, its image
under `adicCompletionMap` is an `ℓ`-th power in the units.

The point is that the residue of the image always lies in the image of `κ(𝔮₁)^×`, whose
order `q ^ d - 1` divides `(q ^ (d * ℓ * (ℓ - 1)) - 1) / ℓ = (#κ(𝔮₂)^×) / ℓ`; hence the
residue is an `ℓ`-th power in `κ(𝔮₂)^×`, and `ℓ` being a unit of the Henselian ring
`𝒪_{𝔮₂}` lifts the root (`units_mem_pow_of_residue_pow_eq_one`). -/
theorem exists_pow_eq_unit_adicCompletion_tower
    {K : Type*} [Field K] [NumberField K] {L₁ : Type*} [Field L₁] [NumberField L₁]
    {L₂ : Type*} [Field L₂] [NumberField L₂]
    [Algebra K L₁] [Algebra L₁ L₂] [Algebra K L₂] [IsScalarTower K L₁ L₂]
    [FiniteDimensional K L₁] [FiniteDimensional L₁ L₂] [FiniteDimensional K L₂]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₁))
    (𝔮₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₂))
    (h₁ : 𝔮₁.asIdeal.LiesOver 𝔭.asIdeal) (h₂ : 𝔮₂.asIdeal.LiesOver 𝔮₁.asIdeal)
    (he₂ : 𝔮₂.asIdeal.ramificationIdx (NumberField.RingOfIntegers L₁) = 1)
    {ℓ d : ℕ} (hℓ : ℓ.Prime) (hℓd : ℓ ≠ NK.TameStructureDeep.Tame.resCharAt 𝔭) (hd : 0 < d)
    (hunit : IsUnit (ℓ : 𝔮₂.adicCompletionIntegers L₂))
    (hcard₁ : Nat.card (IsLocalRing.ResidueField (𝔮₁.adicCompletionIntegers L₁))
      = (NK.LocalStructure.residueCard K 𝔭) ^ d)
    (hcard₂ : Nat.card (IsLocalRing.ResidueField (𝔮₂.adicCompletionIntegers L₂))
      = (NK.LocalStructure.residueCard K 𝔭) ^ (d * ℓ * (ℓ - 1)))
    (u : (𝔮₁.adicCompletionIntegers L₁)ˣ) :
    ∃ w : (𝔮₂.adicCompletionIntegers L₂)ˣ,
      (w : 𝔮₂.adicCompletion L₂) ^ ℓ =
        Commons.RingTheory.Henselian.adicCompletionMap 𝔮₁ 𝔮₂ h₂
          (u : 𝔮₁.adicCompletion L₁) := by
  classical
  haveI hfin₁ : Finite (IsLocalRing.ResidueField (𝔮₁.adicCompletionIntegers L₁)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion L₁ 𝔮₁
  haveI hfin₂ : Finite (IsLocalRing.ResidueField (𝔮₂.adicCompletionIntegers L₂)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion L₂ 𝔮₂
  haveI hfinK : Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K 𝔭
  haveI hhen₂ : HenselianLocalRing (𝔮₂.adicCompletionIntegers L₂) :=
    Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing 𝔮₂
  set q := NK.LocalStructure.residueCard K 𝔭 with hqdef
  -- The residue characteristic is prime.
  have hp : Nat.Prime (resCharAt 𝔭) := by
    haveI : Fintype (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) := Fintype.ofFinite _
    obtain ⟨n, hpn, -⟩ :=
      FiniteField.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)))
    simpa [NK.TameStructureDeep.Tame.resCharAt] using hpn
  -- `q` is a power of the residue characteristic.
  obtain ⟨f, hf, hqf⟩ :=
    NK.LocalStructure.Tame.residueCard_eq_pow_of_charP 𝔭 hp
      (ringChar.charP _ : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) (resCharAt 𝔭))
  -- Hence `ℓ` is coprime to `q`.
  have hcop : ℓ.Coprime q := by
    rw [hqdef, hqf, Nat.Prime.coprime_iff_not_dvd hℓ]
    intro hdvd
    have hdvd' : ℓ ∣ resCharAt 𝔭 := (Nat.Prime.dvd_of_dvd_pow hℓ) hdvd
    rcases (Nat.dvd_prime hp).mp hdvd' with h | h
    · exact hℓ.ne_one h
    · exact hℓd h
  have hq2 : 2 ≤ q := by
    rw [hqdef, hqf]
    have hp2 : 2 ≤ resCharAt 𝔭 := hp.two_le
    calc 2 ≤ resCharAt 𝔭 := hp2
      _ = (resCharAt 𝔭) ^ 1 := (pow_one _).symm
      _ ≤ (resCharAt 𝔭) ^ f := Nat.pow_le_pow_right (by omega) hf
  -- The arithmetic of the residue field degrees.
  have hdvd : ℓ * (q ^ d - 1) ∣ q ^ (d * ℓ * (ℓ - 1)) - 1 :=
    ell_mul_pow_sub_one_dvd hℓ hq2 hd hcop
  rw [hqdef] at hdvd
  have hdvd' : ℓ * (Nat.card (IsLocalRing.ResidueField (𝔮₁.adicCompletionIntegers L₁)) - 1) ∣
      Nat.card (IsLocalRing.ResidueField (𝔮₂.adicCompletionIntegers L₂)) - 1 := by
    rw [hcard₁, hcard₂]
    exact hdvd
  have hdiv : ℓ ∣ Nat.card (IsLocalRing.ResidueField (𝔮₂.adicCompletionIntegers L₂)) - 1 :=
    dvd_trans (dvd_mul_right ℓ _) hdvd'
  have hdiv2 : (Nat.card (IsLocalRing.ResidueField (𝔮₁.adicCompletionIntegers L₁)) - 1) ∣
      (Nat.card (IsLocalRing.ResidueField (𝔮₂.adicCompletionIntegers L₂)) - 1) / ℓ :=
    (Nat.dvd_div_iff_mul_dvd hdiv).mpr hdvd'
  -- The image unit.
  let u₂ : (𝔮₂.adicCompletionIntegers L₂)ˣ :=
    Units.map (Commons.NumberTheory.NumberField.Completion.intCompletionMap 𝔮₁ 𝔮₂ h₂).toMonoidHom u
  have hcoe : (u₂ : 𝔮₂.adicCompletionIntegers L₂) =
      ⟨Commons.RingTheory.Henselian.adicCompletionMap 𝔮₁ 𝔮₂ h₂ (u : 𝔮₁.adicCompletion L₁),
       Commons.RingTheory.Henselian.adicCompletionMap_mem_integers 𝔮₁ 𝔮₂ h₂
        (u : 𝔮₁.adicCompletionIntegers L₁).2⟩ := rfl
  set a := IsLocalRing.residue (𝔮₂.adicCompletionIntegers L₂) (u₂ : 𝔮₂.adicCompletionIntegers L₂) with ha
  -- Its residue is fixed by the `#κ(𝔮₁)`-th power map.
  have hpow : a ^ (Nat.card (IsLocalRing.ResidueField (𝔮₁.adicCompletionIntegers L₁))) = a := by
    rw [ha, hcoe]
    exact residue_adicCompletionMap_pow_card_eq_self 𝔮₁ 𝔮₂ h₂ he₂ (u : 𝔮₁.adicCompletionIntegers L₁)
  have hane : a ≠ 0 := by
    rw [ha, IsLocalRing.residue_ne_zero_iff_isUnit]
    exact u₂.isUnit
  have hpow1 : a ^ (Nat.card (IsLocalRing.ResidueField (𝔮₁.adicCompletionIntegers L₁)) - 1) = 1 := by
    have hpos : 0 < Nat.card (IsLocalRing.ResidueField (𝔮₁.adicCompletionIntegers L₁)) := Nat.card_pos
    have hn : Nat.card (IsLocalRing.ResidueField (𝔮₁.adicCompletionIntegers L₁)) =
        (Nat.card (IsLocalRing.ResidueField (𝔮₁.adicCompletionIntegers L₁)) - 1) + 1 := by omega
    rw [hn, pow_succ] at hpow
    exact mul_right_cancel₀ hane (by rw [one_mul]; exact hpow)
  have hM : a ^ ((Nat.card (IsLocalRing.ResidueField (𝔮₂.adicCompletionIntegers L₂)) - 1) / ℓ) = 1 := by
    obtain ⟨s, hs⟩ := hdiv2
    rw [hs, pow_mul, hpow1, one_pow]
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp
    (units_mem_pow_of_residue_pow_eq_one hℓ hunit hdiv u₂ (by rw [← ha]; exact hM))
  refine ⟨w, ?_⟩
  have hw1 : (w : 𝔮₂.adicCompletionIntegers L₂) ^ ℓ = (u₂ : 𝔮₂.adicCompletionIntegers L₂) := by
    have h := congrArg (fun z : (𝔮₂.adicCompletionIntegers L₂)ˣ => (z : 𝔮₂.adicCompletionIntegers L₂)) hw
    simpa [powMonoidHom_apply] using h
  have hfield : ((w : 𝔮₂.adicCompletionIntegers L₂) : 𝔮₂.adicCompletion L₂) ^ ℓ =
      ((u₂ : 𝔮₂.adicCompletionIntegers L₂) : 𝔮₂.adicCompletion L₂) := by
    have h := congrArg (fun z : 𝔮₂.adicCompletionIntegers L₂ => (z : 𝔮₂.adicCompletion L₂)) hw1
    simpa using h
  rw [hfield, hcoe]

end NK.TameStructureDeep.Tame
