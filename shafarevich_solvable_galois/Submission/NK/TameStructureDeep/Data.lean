/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The reduced input catalogue and the local structure core, from the residual

This file assembles, from the single residual `NK.TameStructureDeep.TameRamificationCore`, the
structures of the reduced input catalogue at a genuine local field `κ = K_𝔭`:

* `NK.LocalStructure.TameCore p K 𝔭 K'` (the core of the tame structure theorem),
* `NK.TameData.TameDataInput p (residueCard K 𝔭) (K_𝔭) K'` (the bundle),
* `NK.LocalTame.TameData p (residueCard K 𝔭) (K_𝔭) K'` (the packaged structure theorem),
* `NK.TameData.TameInertiaInput`, `NK.TameData.TameAbelianisationInput`,
  `NK.TameData.TameTorsionInput`, `NK.LocalStructure.TameFrobeniusCore`,

and the compatibility theorem `tameStructureInputs_of_core`, showing that the residual implies the
*whole* named-input list `NK.TameStructure.TameStructureInputs` of the sibling chapter — so this
chapter strictly subsumes `Submission/Work/TameStructure/`.
-/
import Submission.NK.TameStructureDeep.Inertia
import Submission.NK.TameStructureDeep.Abelianisation
import Submission.NK.TameStructureDeep.Frobenius
import Submission.NK.TameStructure.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.TameStructureDeep

universe u

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- **The core of the tame structure theorem `NK.LocalStructure.TameCore`** from the residual.

All six fields are obtained: `hp` and `residue_char` from the residual and the arithmetic of the
completion, `unramifiedQuotient` and `isTameInertia` from the residual, and
`isProPrimeToP_tameInertia` and `tameInertia_commutator_mem` *derived* (they are not inputs). -/
theorem tameCore_adicCompletion
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p q : ℕ}
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (h : TameRamificationCore p q (𝔭.adicCompletion K) K') :
    NK.LocalStructure.TameCore p K 𝔭 K' where
  hp := h.hp
  residue_char := hchar
  unramifiedQuotient := h.unramifiedQuotient
  isTameInertia := h.isTameInertia
  isProPrimeToP_tameInertia := isProPrimeToP_tameInertia h
  tameInertia_commutator_mem := tameInertia_commutator_mem h

/-- **The reduced input catalogue `NK.TameData.TameDataInput`** at the completion, from the
residual with `q = NK.LocalStructure.residueCard K 𝔭`. -/
theorem tameDataInput_adicCompletion
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (h : TameRamificationCore p (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K') :
    NK.TameData.TameDataInput p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K' where
  inertia := tameInertiaInput_adicCompletion 𝔭 hchar h
  abelianisation := tameAbelianisationInput_adicCompletion 𝔭 hchar h
  frobenius := tameFrobeniusCore_adicCompletion 𝔭 h

/-- **The packaged structure theorem `NK.LocalTame.TameData`** at the completion. -/
theorem tameData_adicCompletion
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (h : TameRamificationCore p (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K') :
    NK.LocalTame.TameData p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K' :=
  (tameDataInput_adicCompletion 𝔭 hchar h).toTameData

/-- **The packaged Frobenius characterisation at the completion** (NSW (12.1.8) in the form used
downstream by `NK.LocalTame.isFrobeniusFor_map_iff`): an element acts on the prime-to-`p` roots
of unity by `ζ ↦ ζ^q` if and only if it lies outside `I_κ` and conjugates the tame inertia
`I_κ/V_κ` by the `q`-th power map. -/
theorem frobeniusLiftCharacterisation_adicCompletion
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p q : ℕ}
    (h : TameRamificationCore p q (𝔭.adicCompletion K) K') :
    NK.LocalTame.FrobeniusLiftCharacterisation p q (𝔭.adicCompletion K) K' :=
  frobeniusLiftCharacterisation_of_core h

/-- **`NK.LocalTame.TameStructureInput` at the completion** — the eight-field packaged form of
the tame structure theorem, from the residual.  The two fields that
`NK.LocalStructure.TameCore` does not carry (`q_eq`, `exists_frobeniusLift`) are supplied by the
proved arithmetic of the completion and by `NK.LocalStructure.Tame.exists_notMem_inertiaSubgroup_of_unramifiedQuotient`. -/
theorem tameStructureInput_adicCompletion
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p q : ℕ}
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (h : TameRamificationCore p q (𝔭.adicCompletion K) K') :
    NK.LocalTame.TameStructureInput p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K' :=
  NK.LocalStructure.tameStructureInput_of_TameCore 𝔭
    (tameCore_adicCompletion 𝔭 hchar h)

/-! ## Compatibility with `Submission/Work/TameStructure/` -/

/-- **The residual implies the whole named-input list of `NK.TameStructure`.**  This shows that
the single residual `TameRamificationCore` is at least as strong as the five named classical inputs
of the sibling chapter (`CharP`, `UnramifiedZhat`, `TameInertiaStructure`,
`FrobeniusNormalisation`, `TameAbelianisationStructure`):

* `CharP` of the residue field is `NK.Mine.charP_ringChar_residueField_adicCompletion` at
  `p = ringChar`, so the caller must supply `p` with `hchar` (they are the *same* datum);
* `UnramifiedZhat` is `h.unramifiedQuotient` transported across the *proved* Galois-correspondence
  bridge `NK.TameStructure.quotient_inertiaSubgroup_mulEquiv_unramifiedClosure`;
* `TameInertiaStructure` is `h.isTameInertia` together with the closedness of `V_κ`, which is a
  field of the residual;
* `FrobeniusNormalisation` is `h.exists_frobenius` + `h.frobenius_iff`;
* `TameAbelianisationStructure` is `h.abelianisation`. -/
theorem tameStructureInputs_of_core
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p q : ℕ}
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (h : TameRamificationCore p q (𝔭.adicCompletion K) K') :
    NK.TameStructure.TameStructureInputs p q K 𝔭 K' where
  charP := hchar
  unramified := by
    obtain ⟨e⟩ := NK.TameStructure.quotient_inertiaSubgroup_mulEquiv_unramifiedClosure
      (κ := 𝔭.adicCompletion K) (K' := K') p
    obtain ⟨e'⟩ := h.unramifiedQuotient
    exact ⟨e.symm.trans e'⟩
  tameInertia := ⟨h.isTameInertia, h.wildInertia_closed⟩
  frobenius := ⟨h.exists_isFrobeniusFor_and_isTameFrobeniusLift, fun _ hx =>
    h.actsAsFrobenius_of_isTameFrobeniusLift hx⟩
  abelianisation := h.abelianisation

end

end NK.TameStructureDeep
