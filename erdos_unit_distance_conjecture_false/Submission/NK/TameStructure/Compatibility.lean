/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Compatibility with the sibling reductions

The named classical inputs of `NK.TameStructure.Defs` are stated *at the field* `κ(μ_{p'})` (for
the unramified quotient) and *at the quotient* `G_κ/V_κ` (for the tame inertia), which is the form
in which this chapter's derivations run.  The sibling chapters
`Submission/Work/LocalStructure/` and `Submission/Work/TameData/` state their (equivalent) reduced
inputs at `G_κ` and `G_κ/V_κ` directly.  This file records the equivalence, so that either form of
the boundary can be used.

* `NK.TameStructure.unramifiedZhat_of_quotient_iso`: `G_κ ⧸ I_κ ≅ Ẑ` ⟹ `UnramifiedZhat`
  (the field form), by the Galois correspondence;
* `NK.TameStructure.unramifiedZhat_iff`: the two are equivalent;
* `NK.TameStructure.tameInertiaStructure_of_core`: the fields of
  `NK.LocalStructure.TameCore` *plus* closedness of `V_κ` deliver `TameInertiaStructure`
  (whose other components are the very fields of `TameCore` and whose commutator field is then
  *derived*) — this is the bridge from the sibling chapter's reduced input to this one;
* `NK.TameStructure.tameStructureInputs_of_core`: the same at the level of the bundled inputs.
-/
import Submission.NK.TameStructure.Assembly

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.TameStructure

universe u

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- **The unramified quotient in the field form**, from its form at `G_κ`: if
`Gal(K'/κ) ⧸ I_κ ≅ Ẑ` then `Gal(κ(μ_{p'})/κ) ≅ Ẑ`
(`NK.TameStructure.UnramifiedZhat`), by the Galois correspondence. -/
theorem unramifiedZhat_of_quotient_iso
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (h : Nonempty (Gal(K'/𝔭.adicCompletion K) ⧸
      NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p ≃*
      NK.LocalAnabelian.Zhat)) :
    UnramifiedZhat p K 𝔭 K' := by
  obtain ⟨e1⟩ := quotient_inertiaSubgroup_mulEquiv_unramifiedClosure
    (κ := 𝔭.adicCompletion K) (K' := K') p
  obtain ⟨e2⟩ := h
  exact ⟨e1.symm.trans e2⟩

/-- **The two forms of the unramified-quotient input are equivalent.** -/
theorem unramifiedZhat_iff
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ} :
    UnramifiedZhat p K 𝔭 K' ↔
      Nonempty (Gal(K'/𝔭.adicCompletion K) ⧸
        NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p ≃*
        NK.LocalAnabelian.Zhat) :=
  ⟨fun h => unramifiedQuotient_adicCompletion 𝔭 K' p h,
    fun h => unramifiedZhat_of_quotient_iso 𝔭 h⟩

/-- **`TameInertiaStructure` from the sibling reduction `NK.LocalStructure.TameCore`.**
`TameCore` carries the maximality of `I_κ/V_κ`, the pro-prime-to-`p`-ness of `I_κ/V_κ`, the
commutator relation and the unramified quotient; all that is added here is the closedness of
`V_κ` — which is what makes both the commutator relation *and* the pro-prime-to-`p`-ness of
`I_κ/V_κ` *derivable* rather than assumed. -/
theorem tameInertiaStructure_of_core
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hT : NK.LocalStructure.TameCore p K 𝔭 K')
    (hc : IsClosed (NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p :
      Set (Gal(K'/𝔭.adicCompletion K)))) :
    TameInertiaStructure p K 𝔭 K' :=
  ⟨hT.isTameInertia, hc⟩

/-- **The bundled inputs from the sibling reduction**: `NK.LocalStructure.TameCore` (the
structure of the tame quotient), `NK.TameData.TameAbelianisationInput` (Shimizu 2.1) and
`NK.LocalStructure.TameFrobeniusCore` (NSW (12.1.8)) deliver `TameStructureInputs`, modulo the
two normalisations that this chapter proves or isolates: the closedness of `V_κ` and the
`CharP` of the residue field. -/
theorem tameStructureInputs_of_core
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hT : NK.LocalStructure.TameCore p K 𝔭 K')
    (hA : NK.TameData.TameAbelianisationInput p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K')
    (hF : NK.LocalStructure.TameFrobeniusCore p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K')
    (hc : IsClosed (NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p :
      Set (Gal(K'/𝔭.adicCompletion K)))) :
    TameStructureInputs p (NK.LocalStructure.residueCard K 𝔭) K 𝔭 K' where
  charP := hT.residue_char
  unramified := unramifiedZhat_of_quotient_iso 𝔭 hT.unramifiedQuotient
  tameInertia := tameInertiaStructure_of_core 𝔭 hT hc
  frobenius := ⟨hF.exists_frob, hF.actsAsFrobenius_of_isTameFrobeniusLift⟩
  abelianisation := hA.nonempty_iso

/-- **From the sibling reduction to the bundled local input catalogue**:
`NK.TameData.TameDataInput p (residueCard K 𝔭) (K_𝔭) K'` from
`NK.LocalStructure.TameCore`, `NK.TameData.TameAbelianisationInput`,
`NK.LocalStructure.TameFrobeniusCore` and closedness of the wild inertia. -/
theorem tameDataInput_of_core
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hT : NK.LocalStructure.TameCore p K 𝔭 K')
    (hA : NK.TameData.TameAbelianisationInput p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K')
    (hF : NK.LocalStructure.TameFrobeniusCore p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K')
    (hc : IsClosed (NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p :
      Set (Gal(K'/𝔭.adicCompletion K)))) :
    NK.TameData.TameDataInput p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K' :=
  tameDataInput_adicCompletion 𝔭 hT.hp (tameStructureInputs_of_core 𝔭 hT hA hF hc)

end

end NK.TameStructure
