/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The weak Neukirch–Uchida chain for fields in *independent* universes

`Submission.neukirch_uchida` (and `Submission.NeukirchUchida.exists_sigma`) are stated with
`{K₁ K₂ K₁' K₂' : Type*}`, i.e. with **four independent universe parameters**, and so is the
reconstruction input `NK.ReconstructField.LevelIsoInput ϕ hϕ`
(`Submission/Work/Reconstruct/endgameOfInputs.lean` is likewise stated at four universes).  The
chain of `Main.lean` is uniform-universe (`{K₁ K₂ K₁' K₂' : Type u}`), which is what the request
asked for, and is the case used in the requestor's test.

This file removes the uniformity assumption.  The point that makes this possible is the following.

* In the §6 argument the module data is evaluated **only at the common field** `L = ↥N` produced by
  `NK.UchidaKummer.Uchida.exists_isGalois_sup_le` inside a chosen algebraically closed field
  `Ω`; everything else about the two number fields `K₁`, `K₂` is transported along *ring
  isomorphisms* `K_i ≃+* ↥(fixedField H_i)`, which are universe-polymorphic.

Consequently the module data (and the Čebotarev input) are needed at a **single, freely chosen**
universe `w` — the universe of `Ω = AlgebraicClosure (ULift.{w,0} ℚ)` — while the fields `K₁`, `K₂`
and their separable closures `K₁'`, `K₂'` live in four *independent* universes `u₁ u₂ u₃ u₄`.

Two consequences:

* instantiating `w = u₁ = u₂ = u₃ = u₄ = u` recovers the uniform chain of `Main.lean`;
* instantiating `w = 0` shows that the **existing universe-0 inputs**
  `NK.UchidaKummer.IsUchidaModuleData 2` and `NK.WeakNU.ChebotarevFrobeniusInput` are enough to
  produce `LevelIsoInput ϕ hϕ` for fields in *arbitrary* universes — because the common field is
  built in `Type 0` and the two number fields are embedded into it by `IsAlgClosed.lift`, which
  does not require a common universe.

The main results are

* `NK.UniverseWeakNU.hasIsomorphicAbsGaloisU_of_galoisEquiv_congr` — the universe-bridging step:
  a ring isomorphism `K_i ≃+* M_i` and an isomorphism of the absolute Galois groups of `K₁`, `K₂`
  *in their own universes* produce `HasIsomorphicAbsGaloisU M₁ M₂` for the (possibly larger)
  universe of the `M_i`;
* `NK.UniverseWeakNU.nonempty_ringEquiv_of_uchidaModuleData_and_perlis_absUV`;
* `NK.UniverseWeakNU.isWeakUchidaUV`, `isWeakUchidaUV_of_chebotarev`;
* `NK.UniverseWeakNU.levelIsoInput_of_isWeakUchidaUV`,
  `levelIsoInput_of_chebotarevUV` — the endgame input `LevelIsoInput ϕ hϕ` for
  `{K₁ K₂ K₁' K₂' : Type*}` (four universes), from the residual catalogue at the working universe
  `w`.  With `w = 0` this is `NK.UniverseWeakNU.levelIsoInput_of_chebotarev`
  (`IsUchidaModuleData 2`, `ChebotarevFrobeniusInput`) at arbitrary universes.
-/

import Mathlib
import Submission.NK.UniverseWeakNU.Defs
import Submission.NK.UniverseWeakNU.UchidaU
import Submission.NK.UniverseWeakNU.MainWeak
import Submission.NK.UniverseWeakNU.PrimeCountU
import Submission.NK.ReconstructField.LevelCandidate
import Submission.NK.Reconstruct.LevelMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.UniverseWeakNU

noncomputable section

universe u₁ u₂ u₃ u₄ w

/-! ## Bridging the universes -/

/-- **The universe-bridging step of the multi-universe chain.**

Let `e_i : K_i ≃+* M_i` be ring isomorphisms of number fields, with the `M_i` in a possibly larger
universe `w`, and let `ϕ` be an isomorphism of the absolute Galois groups of `K₁`, `K₂` computed with
separable closures `K_i'` in their *own* universes.  Then the absolute Galois groups of `M₁`, `M₂`
computed with separable closures in `Type w` are isomorphic (`HasIsomorphicAbsGaloisU.{w}`).

The proof pulls the `M_i`-algebra structure of a `Type w` separable closure back to `K_i` along `e_i`
(so that it becomes a separable closure of `K_i`), applies the universe-polymorphic uniqueness of the
separable closure `NK.FieldTheory.Galois.nonempty_mulEquiv_algEquiv_of_isSepClosure`
(`{K : Type u_1} {L : Type u_2} {M : Type u_3}` — three independent universes) on both sides, and
replaces `K_i`-linearity by `M_i`-linearity by
`NK.UchidaKummer.algEquivCongrOfAlgebraMap`. -/
theorem hasIsomorphicAbsGaloisU_of_galoisEquiv_congr
    {K₁ : Type u₁} [Field K₁] [NumberField K₁] {K₂ : Type u₂} [Field K₂] [NumberField K₂]
    {K₁' : Type u₃} [Field K₁'] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']
    {K₂' : Type u₄} [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂']
    {M₁ : Type w} [Field M₁] [NumberField M₁] {M₂ : Type w} [Field M₂] [NumberField M₂]
    (e₁ : K₁ ≃+* M₁) (e₂ : K₂ ≃+* M₂)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) : HasIsomorphicAbsGaloisU.{w} M₁ M₂ := by
  intro A _ _ _ C _ _ _
  let φ₁ : K₁ →+* A := (algebraMap M₁ A).comp e₁.toRingHom
  letI : Algebra K₁ A := φ₁.toAlgebra
  have hsep₁ : Algebra.IsSeparable K₁ A :=
    (Algebra.IsSeparable.iff_of_equiv_equiv e₁ (RingEquiv.refl A) (by ext x; rfl)).mpr
      (inferInstance : Algebra.IsSeparable M₁ A)
  haveI : IsSepClosure K₁ A := ⟨(inferInstance : IsSepClosure M₁ A).sep_closed, hsep₁⟩
  let φ₂ : K₂ →+* C := (algebraMap M₂ C).comp e₂.toRingHom
  letI : Algebra K₂ C := φ₂.toAlgebra
  have hsep₂ : Algebra.IsSeparable K₂ C :=
    (Algebra.IsSeparable.iff_of_equiv_equiv e₂ (RingEquiv.refl C) (by ext x; rfl)).mpr
      (inferInstance : Algebra.IsSeparable M₂ C)
  haveI : IsSepClosure K₂ C := ⟨(inferInstance : IsSepClosure M₂ C).sep_closed, hsep₂⟩
  refine ⟨((NK.UchidaKummer.algEquivCongrOfAlgebraMap e₁ (fun x => rfl)).symm.trans
    ((NK.FieldTheory.Galois.nonempty_mulEquiv_algEquiv_of_isSepClosure
        (K := K₁) (L := A) (M := K₁')).some.trans
      (ϕ.trans (NK.FieldTheory.Galois.nonempty_mulEquiv_algEquiv_of_isSepClosure
        (K := K₂) (L := C) (M := K₂')).some.symm))).trans
    (NK.UchidaKummer.algEquivCongrOfAlgebraMap e₂ (fun x => rfl))⟩

/-! ## §6 for fields in independent universes -/

/-- **§6 of arXiv:2601.01251 with four independent universes for the fields and a free universe for
the common field.**  Given the module data and the Perlis/Gassmann input at the working universe `w`,
two number fields `K₁`, `K₂` (in any universes) with `μ_ℓ ⊆ K_i` and isomorphic absolute Galois
groups (computed with the given separable closures `K_i'`) are isomorphic. -/
theorem nonempty_ringEquiv_of_uchidaModuleData_and_perlis_absUV {ℓ : ℕ} [Fact ℓ.Prime]
    (hU : IsUchidaModuleDataU.{w} ℓ) (hP : PerlisGassmannInputU.{w})
    (K₁ : Type u₁) [Field K₁] [NumberField K₁] (K₂ : Type u₂) [Field K₂] [NumberField K₂]
    (hμ₁ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) (hμ₂ : ∃ ζ : K₂, IsPrimitiveRoot ζ ℓ)
    {K₁' : Type u₃} [Field K₁'] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']
    {K₂' : Type u₄} [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) :
    Nonempty (K₁ ≃+* K₂) := by
  classical
  let Ω := AlgebraicClosure (ULift.{w,0} ℚ)
  haveI : IsAlgClosed Ω := inferInstance
  haveI : Algebra.IsAlgebraic ℚ Ω :=
    Algebra.IsAlgebraic.trans ℚ (ULift.{w,0} ℚ) Ω
  let i : K₁ →ₐ[ℚ] Ω := IsAlgClosed.lift
  let j : K₂ →ₐ[ℚ] Ω := IsAlgClosed.lift
  haveI hi : FiniteDimensional ℚ ↥(i.fieldRange) := i.toLinearMap.finiteDimensional_range
  haveI hj : FiniteDimensional ℚ ↥(j.fieldRange) := j.toLinearMap.finiteDimensional_range
  obtain ⟨N, hN₁, hN₂, hfinN, hgalN⟩ :=
    NK.UchidaKummer.Uchida.exists_isGalois_sup_le i.fieldRange j.fieldRange
  haveI : FiniteDimensional ℚ ↥N := hfinN
  haveI : IsGalois ℚ ↥N := hgalN
  haveI : NumberField ↥N :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := ℚ) N
  let iN : K₁ →ₐ[ℚ] ↥N :=
    i.codRestrict N.toSubalgebra (fun x => hN₁ (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩))
  let jN : K₂ →ₐ[ℚ] ↥N :=
    j.codRestrict N.toSubalgebra (fun x => hN₂ (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩))
  let H₁ : Subgroup Gal(↥N/ℚ) := iN.fieldRange.fixingSubgroup
  let H₂ : Subgroup Gal(↥N/ℚ) := jN.fieldRange.fixingSubgroup
  have hiso₁ : Nonempty (K₁ ≃+* ↥(IntermediateField.fixedField H₁)) :=
    ⟨(AlgEquiv.ofInjective iN iN.injective).toRingEquiv.trans
      ((IntermediateField.equivOfEq (IsGalois.fixedField_fixingSubgroup iN.fieldRange)).symm.toRingEquiv)⟩
  have hiso₂ : Nonempty (K₂ ≃+* ↥(IntermediateField.fixedField H₂)) :=
    ⟨(AlgEquiv.ofInjective jN jN.injective).toRingEquiv.trans
      ((IntermediateField.equivOfEq (IsGalois.fixedField_fixingSubgroup jN.fieldRange)).symm.toRingEquiv)⟩
  obtain ⟨e₁⟩ := hiso₁
  obtain ⟨e₂⟩ := hiso₂
  have hμH₁ : ∃ ζ : ↥(IntermediateField.fixedField H₁), IsPrimitiveRoot ζ ℓ := by
    obtain ⟨ζ, hζ⟩ := hμ₁
    exact ⟨e₁ ζ, hζ.map_of_injective e₁.injective⟩
  have hμH₂ : ∃ ζ : ↥(IntermediateField.fixedField H₂), IsPrimitiveRoot ζ ℓ := by
    obtain ⟨ζ, hζ⟩ := hμ₂
    exact ⟨e₂ ζ, hζ.map_of_injective e₂.injective⟩
  obtain ⟨ζ, hζ⟩ := hμ₁
  obtain ⟨e⟩ := nonempty_ringEquiv_of_uchidaModuleData_and_perlisU hU hP (L := ↥N)
    ⟨iN ζ, hζ.map_of_injective iN.injective⟩ H₁ H₂ hμH₁ hμH₂
    (hasIsomorphicAbsGaloisU_of_galoisEquiv_congr e₁ e₂ ϕ)
  exact ⟨e₁.trans (e.trans e₂.symm)⟩

/-! ## The weak theorem, and the level-wise input, in independent universes -/

/-- The weak Neukirch–Uchida theorem with the paper's cyclotomic hypothesis, for fields in four
independent universes. -/
def IsWeakUchidaOfUV (ℓ : ℕ) : Prop :=
  ∀ (K₁ : Type u₁) (K₂ : Type u₂) [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    (K₁' : Type u₃) [Field K₁'] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']
    (K₂' : Type u₄) [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂'],
    (∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) → (∃ ζ : K₂, IsPrimitiveRoot ζ ℓ) →
    Nonempty (Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) → Nonempty (K₁ ≃+* K₂)

/-- The weak Neukirch–Uchida theorem, for fields in four independent universes. -/
def IsWeakUchidaUV (ℓ : ℕ) : Prop :=
  ∀ (K₁ : Type u₁) (K₂ : Type u₂) [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    (K₁' : Type u₃) [Field K₁'] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']
    (K₂' : Type u₄) [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂'],
    Nonempty (Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) → Nonempty (K₁ ≃+* K₂)

/-- **§6 with the cyclotomic hypothesis, in independent universes**, from the residual catalogue at
the working universe `w`. -/
theorem isWeakUchidaOfUV {ℓ : ℕ} [Fact ℓ.Prime] (hU : IsUchidaModuleDataU.{w} ℓ)
    (hP : PerlisGassmannInputU.{w}) : IsWeakUchidaOfUV.{u₁,u₂,u₃,u₄} ℓ := by
  intro K₁ K₂ _ _ _ _ K₁' _ _ _ K₂' _ _ _ hμ₁ hμ₂ hiso
  obtain ⟨ϕ⟩ := hiso
  exact nonempty_ringEquiv_of_uchidaModuleData_and_perlis_absUV hU hP K₁ K₂ hμ₁ hμ₂ ϕ

/-- **The weak Neukirch–Uchida theorem in independent universes**, from Uchida's module data at
`ℓ = 2` and the Perlis/Gassmann input, both at the working universe `w`. -/
theorem isWeakUchidaUV {ℓ : ℕ} (hU : IsUchidaModuleDataU.{w} 2) (hP : PerlisGassmannInputU.{w}) :
    IsWeakUchidaUV.{u₁,u₂,u₃,u₄} ℓ := by
  intro K₁ K₂ _ _ _ _ K₁' _ _ _ K₂' _ _ _ hiso
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isWeakUchidaOfUV (ℓ := 2) hU hP K₁ K₂ K₁' K₂'
    ⟨-1, IsPrimitiveRoot.neg_one 0 (by norm_num)⟩
    ⟨-1, IsPrimitiveRoot.neg_one 0 (by norm_num)⟩ hiso

/-- **The weak Neukirch–Uchida theorem in independent universes, from the residual catalogue**
(Uchida's module data at `ℓ = 2` and Čebotarev's theorem at the working universe `w`). -/
theorem isWeakUchidaUV_of_chebotarev {ℓ : ℕ} (hU : IsUchidaModuleDataU.{w} 2)
    (hC : ChebotarevFrobeniusInputU.{w}) : IsWeakUchidaUV.{u₁,u₂,u₃,u₄} ℓ :=
  isWeakUchidaUV hU (perlisGassmannInputU hC)

/-! ## The level-wise input in independent universes -/

/-- **The level-wise input `NK.ReconstructField.LevelIsoInput` for fields in four independent
universes.**

The weak theorem must be available at the universes of the *levels*: a level
`L : IntermediateField K₁ K₁'` is a subtype of `K₁'`, so it lives in the universe `u₃` of `K₁'`
(and `levelMap ϕ L` in the universe `u₄` of `K₂'`); the separable closures used in
`NK.ReconstructField.levelIsoInput_of_isWeakUchida` are `K₁'`, `K₂'` themselves.  Hence the
hypothesis `IsWeakUchidaUV` is taken at `(u₃, u₄, u₃, u₄)`. -/
theorem levelIsoInput_of_isWeakUchidaUV {K₁ : Type u₁} [Field K₁] [NumberField K₁]
    {K₂ : Type u₂} [Field K₂] [NumberField K₂] {K₁' : Type u₃} [Field K₁'] [Algebra K₁ K₁']
    [IsSepClosure K₁ K₁'] {K₂' : Type u₄} [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂']
    {ℓ : ℕ} (hW : IsWeakUchidaUV.{u₃, u₄, u₃, u₄} ℓ)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  fun L _ =>
    @hW ↥L ↥(NK.Reconstruct.levelMap ϕ L) _ _ _
      (NK.Reconstruct.numberField_levelMap hϕ L) K₁' _ _
      (NK.Reconstruct.isSepClosure_level L) K₂' _ _
      (NK.Reconstruct.isSepClosure_level (NK.Reconstruct.levelMap ϕ L))
      ⟨NK.ReconstructField.levelGalEquiv ϕ hϕ L⟩

/-- **The level-wise input for fields in four independent universes, from the residual catalogue at
the working universe `w`**: Uchida's module data at `ℓ = 2` and Čebotarev's theorem, both at `w`.

With `w = 0` (and, more generally, whenever the caller has the props at *some* universe) this
produces `LevelIsoInput ϕ hϕ` for `{K₁ K₂ K₁' K₂' : Type*}` — see
`NK.UniverseWeakNU.levelIsoInput_of_chebotarevRat` for the case in which the caller's hypotheses
are the existing universe-0 inputs. -/
theorem levelIsoInput_of_chebotarevUV {K₁ : Type u₁} [Field K₁] [NumberField K₁]
    {K₂ : Type u₂} [Field K₂] [NumberField K₂] {K₁' : Type u₃} [Field K₁'] [Algebra K₁ K₁']
    [IsSepClosure K₁ K₁'] {K₂' : Type u₄} [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂']
    (hU : IsUchidaModuleDataU.{w} 2) (hC : ChebotarevFrobeniusInputU.{w})
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  levelIsoInput_of_isWeakUchidaUV (ℓ := 2)
    (isWeakUchidaUV (ℓ := 2) hU (perlisGassmannInputU hC)) ϕ hϕ

/-- **The endgame hypothesis at an arbitrary universe, from the *existing universe-0* inputs.**

This is the requestor's blocked derivation, now working at `{K₁ K₂ K₁' K₂' : Type*}`
(four independent universe parameters, or any single one of them): the universe-0 inputs
`NK.UchidaKummer.IsUchidaModuleData 2` and `NK.WeakNU.ChebotarevFrobeniusInput` suffice, because
the working universe of `levelIsoInput_of_chebotarevUV` may be taken to be `0` — the common field of
the §6 argument is built inside the `Type 0` field `AlgebraicClosure ℚ`, and the two number fields
are embedded into it by `IsAlgClosed.lift`, which requires no common universe. -/
theorem levelIsoInput_of_chebotarevRat {K₁ : Type u₁} [Field K₁] [NumberField K₁]
    {K₂ : Type u₂} [Field K₂] [NumberField K₂] {K₁' : Type u₃} [Field K₁'] [Algebra K₁ K₁']
    [IsSepClosure K₁ K₁'] {K₂' : Type u₄} [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂']
    (hU : IsUchidaModuleDataU.{0} 2) (hC : ChebotarevFrobeniusInputU.{0})
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  levelIsoInput_of_chebotarevUV hU hC ϕ hϕ

/-- **The `.{0}` instance of `levelIsoInput_of_chebotarevUV`**: the same statement with the inputs
written as the originals `NK.UchidaKummer.IsUchidaModuleData 2` and
`NK.WeakNU.ChebotarevFrobeniusInput` (definitionally the `.{0}` props). -/
theorem levelIsoInput_of_chebotarev_universePoly {K₁ : Type u₁} [Field K₁] [NumberField K₁]
    {K₂ : Type u₂} [Field K₂] [NumberField K₂] {K₁' : Type u₃} [Field K₁'] [Algebra K₁ K₁']
    [IsSepClosure K₁ K₁'] {K₂' : Type u₄} [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂']
    (hU : NK.UchidaKummer.IsUchidaModuleData 2) (hC : NK.WeakNU.ChebotarevFrobeniusInput)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  levelIsoInput_of_chebotarevRat hU hC ϕ hϕ

/-- The weak theorem itself, at four independent universes, from the universe-0 inputs. -/
theorem isWeakUchidaRat {ℓ : ℕ} (hU : NK.UchidaKummer.IsUchidaModuleData 2)
    (hC : NK.WeakNU.ChebotarevFrobeniusInput) : IsWeakUchidaUV.{u₁,u₂,u₃,u₄} ℓ :=
  isWeakUchidaUV_of_chebotarev hU hC

end

end NK.UniverseWeakNU
