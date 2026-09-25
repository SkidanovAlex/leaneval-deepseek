/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The reduced input catalogue for a `p`-adic field, assembled

This file assembles the three structures of the reduced input catalogue
`Submission/Work/TameData/Definitions.lean` for a genuine local field `κ = K_𝔭` and a separable
closure `K'`, from the named classical inputs of `NK.TameStructure.Defs`:

* `NK.TameData.TameInertiaInput p (K_𝔭) K'` — NSW (7.5.7) Corollary, (7.5.11), Iwasawa
  (`NK.TameStructure.tameInertiaInput_adicCompletion`, deliverable 2);
* `NK.LocalStructure.TameFrobeniusCore p q (K_𝔭) K'` — NSW (12.1.8), Iwasawa
  (`NK.TameStructure.tameFrobeniusCore_adicCompletion`, deliverable 3);
* `NK.TameData.TameAbelianisationInput p q (K_𝔭) K'` — Shimizu 2.1 via local class field theory
  (`NK.TameStructure.tameAbelianisationInput_adicCompletion`, deliverable 4),

with the residue field cardinality `q = NK.LocalStructure.residueCard K 𝔭`.

The main outputs are

* `NK.TameStructure.tameDataInput_adicCompletion` — the *bundle*
  `NK.TameData.TameDataInput p (residueCard K 𝔭) (K_𝔭) K'`, which is exactly the local input
  consumed by `Submission/Work/ResidueFrob/` (`NK.ResidueFrob.TameDataInputs K K' A` once the
  place vocabulary of `NK.FrobeniusBridge` is substituted, and together with
  `NK.LocalTame.Zl2ResidueChar`, which is discharged in
  `NK.Mine.zl2ResidueChar_adicCompletion`);
* `NK.TameStructure.tameData_adicCompletion` — the packaged structure theorem
  `NK.LocalTame.TameData p (residueCard K 𝔭) (K_𝔭) K'`.

Two variants of deliverable 2 are provided: `tameInertiaInput_adicCompletion` (which *derives* the
commutator relation from the maximality of `I_κ/V_κ`, `NK.TameStructure.TameInertiaStructure`)
and `tameInertiaInput_of_commutator`, which takes the commutator relation as an input — the route
for a caller who already has `NK.LocalStructure.TameCore`, whose fields include it.
-/
import Submission.NK.TameStructure.Inertia
import Submission.NK.TameStructure.Frobenius
import Submission.NK.TameStructure.Abelianisation

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.TameStructure

universe u

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- **Deliverable 2, alternative route**: `NK.TameData.TameInertiaInput p (K_𝔭) K'` from the
maximality of `I_κ/V_κ`, the pro-prime-to-`p`-ness of `I_κ/V_κ`, the *commutator relation*, and
the unramified quotient — the form in which `NK.LocalStructure.TameCore` supplies the data
(whose fields include `tameInertia_commutator_mem` directly, without closure of `V_κ`). -/
theorem tameInertiaInput_of_commutator
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ} (hp : p.Prime)
    (hisTame : NK.LocalTame.IsMaxNormalProCyclicInQuotient
      (NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p)
      (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p))
    (hpro : NK.LocalTame.IsProPrimeToP p
      ↥(NK.LocalTame.tameInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p))
    (hcomm : ∀ y ∈ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p,
      ∀ z ∈ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p,
        y * z * y⁻¹ * z⁻¹ ∈
          NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p)
    (hu : UnramifiedZhat p K 𝔭 K') :
    NK.TameData.TameInertiaInput p (𝔭.adicCompletion K) K' where
  hp := hp
  isTameInertia := hisTame
  isProPrimeToP_tameInertia := hpro
  tameInertia_commutator_mem := hcomm
  unramifiedQuotient := unramifiedQuotient_adicCompletion 𝔭 K' p hu

/-- The conjunction of the three structures of the reduced input catalogue at the completion,
from the named classical inputs: this is the local input catalogue
`NK.TameData.TameDataInput p (residueCard K 𝔭) (K_𝔭) K'` in the vocabulary of
`Submission/Work/ResidueFrob/` (`NK.ResidueFrob.TameDataInputs K K' A` up to the place
vocabulary and the residue-character detector `NK.LocalTame.Zl2ResidueChar`). -/
theorem tameDataInput_adicCompletion
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ} (hp : p.Prime)
    (h : TameStructureInputs p (NK.LocalStructure.residueCard K 𝔭) K 𝔭 K') :
    NK.TameData.TameDataInput p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K' where
  inertia := tameInertiaInput_adicCompletion 𝔭 K' p hp h.tameInertia h.unramified
  abelianisation :=
    tameAbelianisationInput_residueCard 𝔭 hp h.charP h.abelianisation
  frobenius := tameFrobeniusCore_adicCompletion 𝔭 hp h.frobenius

/-- **The packaged structure theorem for the `𝔭`-adic completion** (NSW (7.5.7), (7.5.11),
(12.1.8); Iwasawa; Shimizu 2.1) from the named classical inputs. -/
theorem tameData_adicCompletion
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ} (hp : p.Prime)
    (h : TameStructureInputs p (NK.LocalStructure.residueCard K 𝔭) K 𝔭 K') :
    NK.LocalTame.TameData p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K' :=
  (tameDataInput_adicCompletion 𝔭 hp h).toTameData

/-- **The structure theorem in the `SeparableClosure` presentation** — the shape in which
`Submission/Work/FrobeniusBridge/` states its local inputs (`localClosure A`). -/
theorem tameData_separableClosure
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (h : TameStructureInputs p (NK.LocalStructure.residueCard K 𝔭) K 𝔭
      (SeparableClosure (𝔭.adicCompletion K))) :
    NK.LocalTame.TameData p (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K)
      (SeparableClosure (𝔭.adicCompletion K)) :=
  tameData_adicCompletion 𝔭 hp h

/-- **The Frobenius characterisation** (NSW (12.1.8) in the packaged form consumed downstream):
`NK.LocalTame.FrobeniusLiftCharacterisation p q (K_𝔭) K'`, i.e. an element acts on the
prime-to-`p` roots of unity by `ζ ↦ ζ^q` if and only if it lies outside `I_κ` and conjugates the
tame inertia by the `q`-th power map.

This is derived from the named inputs exactly as in
`NK.LocalStructure.Frobenius.frobeniusLiftCharacterisation_of_core`: the commutator relation is
*derived* here (`NK.TameStructure.tameInertia_commutator_mem`) rather than assumed. -/
theorem frobeniusLiftCharacterisation_adicCompletion
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ} (hp : p.Prime)
    (h : TameStructureInputs p (NK.LocalStructure.residueCard K 𝔭) K 𝔭 K') :
    NK.LocalTame.FrobeniusLiftCharacterisation p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K' :=
  NK.LocalStructure.Frobenius.frobeniusLiftCharacterisation_of_core
    (tameFrobeniusCore_adicCompletion 𝔭 hp h.frobenius)
    (tameInertia_commutator_mem 𝔭 K' p h.tameInertia)

/-! ## The named inputs, listed -/

/-- `NK.TameStructure.TameStructureInputs` at the residue field cardinality of `𝔭`, with all
components named for the reader: the *entire* list of classical inputs this area consumes. -/
theorem tameStructureInputs_iff
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ} :
    TameStructureInputs p (NK.LocalStructure.residueCard K 𝔭) K 𝔭 K' ↔
      (CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p ∧
        UnramifiedZhat p K 𝔭 K' ∧
        TameInertiaStructure p K 𝔭 K' ∧
        FrobeniusNormalisation p (NK.LocalStructure.residueCard K 𝔭) K 𝔭 K' ∧
        TameAbelianisationStructure p (NK.LocalStructure.residueCard K 𝔭) K 𝔭 K') :=
  ⟨fun h => ⟨h.charP, h.unramified, h.tameInertia, h.frobenius, h.abelianisation⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

end

end NK.TameStructure
