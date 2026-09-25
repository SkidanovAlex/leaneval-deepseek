/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Transport of the Neukirch–Uchida endgame statement along `ULift`

This module contains the purely formal heart of the universe unification: the statement

  `∃! σ : K₂' ≃+* K₁', MapsBase ∧ ∀ g, ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)`

is transported along the `ULift` ring equivalences, i.e. it holds for the data `(K₁, K₂, K₁', K₂')`
and the isomorphism `ϕ` **iff** it holds for the lifted data `(ULift K₁, ULift K₂, ULift K₁',
ULift K₂')` and the transported isomorphism `transportGalEquiv ϕ` (`Submission/Work/UniverseUnify/
Defs.lean`).

Three ingredients:

* `uliftRingEquivEquiv` — the conjugation bijection
  `(ULift K₂' ≃+* ULift K₁') ≃ (K₂' ≃+* K₁')`, `σ' ↦ e₂⁻¹ ∘ σ' ∘ e₁` where
  `eᵢ = ULift.ringEquiv : ULift Kᵢ' ≃+* Kᵢ'`.
* `mapsBase_ulift_iff` — the range condition of `MapsBase` transports along it (this is where the
  *same* algebra structure of `Defs.lean` is used: the range of `algebraMap (ULift K) (ULift L)` is
  the `ULift`-image of the range of `algebraMap K L`).
* `conjCondition_ulift_iff` — the conjugacy condition transports along it.

Together they give `existsUnique_ulift`, which is stated as an `↔` and therefore gives both the
descent (lifted data ⟹ original data) and the ascent.
-/

import Submission.NK.UniverseUnify.Defs

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.UniverseUnify

open scoped Topology
open Submission.NeukirchUchida

universe u v w u₁ u₂ u₃ u₄

/-! ## §1. The conjugation bijection of ring isomorphisms -/

section RingEquivEquiv

variable {K₁' : Type u₃} {K₂' : Type u₄} [Field K₁'] [Field K₂']

/-- **Conjugation of ring isomorphisms by the `ULift` equivalences.**

`σ' ↦ e₂⁻¹ ∘ σ' ∘ e₁`, where `eᵢ = ULift.ringEquiv : ULift Kᵢ' ≃+* Kᵢ'`.  This is the bijection
along which the endgame data are transported: a solution `σ'` for the lifted fields is the same
thing as a solution `σ` for the original fields, via `σ = e₂⁻¹ ∘ σ' ∘ e₁`. -/
noncomputable def uliftRingEquivEquiv :
    (ULift.{w} K₂' ≃+* ULift.{w} K₁') ≃ (K₂' ≃+* K₁') where
  toFun σ := (ULift.ringEquiv : ULift.{w} K₂' ≃+* K₂').symm.trans
    (σ.trans (ULift.ringEquiv : ULift.{w} K₁' ≃+* K₁'))
  invFun τ := (ULift.ringEquiv : ULift.{w} K₂' ≃+* K₂').trans
    (τ.trans (ULift.ringEquiv : ULift.{w} K₁' ≃+* K₁').symm)
  left_inv σ := by
    ext x
    simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply]
  right_inv τ := by
    ext x
    simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply]

/-- The defining formula of `uliftRingEquivEquiv`. -/
theorem uliftRingEquivEquiv_apply (σ : ULift.{w} K₂' ≃+* ULift.{w} K₁') :
    uliftRingEquivEquiv σ = (ULift.ringEquiv : ULift.{w} K₂' ≃+* K₂').symm.trans
      (σ.trans (ULift.ringEquiv : ULift.{w} K₁' ≃+* K₁')) := rfl

end RingEquivEquiv

/-! ## §2. The general `MapsBase` conjugation lemma -/

section MapsBaseConj

variable {A₁ : Type*} {A₂ : Type*} {B₁ : Type*} {B₂ : Type*} [Field A₁] [Field A₂] [Field B₁]
  [Field B₂] {M₁' : Type*} {M₂' : Type*} {L₁' : Type*} {L₂' : Type*} [Field M₁'] [Field M₂']
  [Field L₁'] [Field L₂']

/-- **`MapsBase` from the two pointwise conditions.**

`MapsBase i₁ i₂ σ` (the range equality) is equivalent to: `σ` maps `i₂.range` into `i₁.range` and
`σ.symm` maps `i₁.range` into `i₂.range`.  This pointwise form is the robust one to work with: it
avoids all coercions of ring isomorphisms to ring homomorphisms. -/
theorem mapsBase_of_mem (i₁ : A₁ →+* M₁') (i₂ : A₂ →+* M₂') (σ : M₂' ≃+* M₁')
    (h₁ : ∀ x ∈ i₂.range, σ x ∈ i₁.range) (h₂ : ∀ y ∈ i₁.range, σ.symm y ∈ i₂.range) :
    Submission.NeukirchUchida.MapsBase i₁ i₂ σ := by
  rw [Submission.NeukirchUchida.MapsBase]
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Subring.mem_map.mp hy
    exact h₁ x hx
  · intro hy
    exact Subring.mem_map.mpr ⟨σ.symm y, h₂ y hy, σ.apply_symm_apply y⟩

/-- **Conjugation of the `MapsBase` condition.**

Let `i₁ : A₁ →+* M₁'`, `i₂ : A₂ →+* M₂'` be the "base field" embeddings of one pair of fields, and
let `j₁ : B₁ →+* L₁'`, `j₂ : B₂ →+* L₂'` be those of another, related by ring isomorphisms
`e₁ : M₁' ≃+* L₁'`, `e₂ : M₂' ≃+* L₂'` carrying the first range onto the second.  Then `MapsBase i₁ i₂`
for `σ` implies `MapsBase j₁ j₂` for the conjugate `e₂⁻¹ ∘ σ ∘ e₁`.

This is the formal content of "the range condition must be transported along the *same* ring
isomorphism as the isomorphism itself", the trap flagged in the audit: with a different algebra
structure on `ULift L` than the one the ring isomorphism is taken along, the transported statement
is not equivalent to the original. -/
theorem mapsBase_conj (i₁ : A₁ →+* M₁') (i₂ : A₂ →+* M₂') (j₁ : B₁ →+* L₁') (j₂ : B₂ →+* L₂')
    (e₁ : M₁' ≃+* L₁') (e₂ : M₂' ≃+* L₂')
    (h₁ : Subring.map (e₁ : M₁' →+* L₁') i₁.range = j₁.range)
    (h₂ : Subring.map (e₂ : M₂' →+* L₂') i₂.range = j₂.range)
    (σ : M₂' ≃+* M₁') (hσ : Submission.NeukirchUchida.MapsBase i₁ i₂ σ) :
    Submission.NeukirchUchida.MapsBase j₁ j₂ (e₂.symm.trans (σ.trans e₁)) := by
  refine mapsBase_of_mem j₁ j₂ _ (fun x hx => ?_) (fun y hy => ?_)
  · have hx₂ : e₂.symm x ∈ i₂.range := by
      have hx' : x ∈ Subring.map (e₂ : M₂' →+* L₂') i₂.range := by rw [h₂]; exact hx
      obtain ⟨z, hz, hzx⟩ := Subring.mem_map.mp hx'
      rw [← hzx]
      simpa only [RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] using hz
    have hσx : σ (e₂.symm x) ∈ i₁.range :=
      Submission.NeukirchUchida.mapsBase_mem i₁ i₂ hσ hx₂
    have hy₁ : e₁ (σ (e₂.symm x)) ∈ j₁.range := by
      have h : e₁ (σ (e₂.symm x)) ∈ Subring.map (e₁ : M₁' →+* L₁') i₁.range :=
        Subring.mem_map.mpr ⟨σ (e₂.symm x), hσx, rfl⟩
      rwa [h₁] at h
    simpa only [RingEquiv.trans_apply] using hy₁
  · have hy₁ : e₁.symm y ∈ i₁.range := by
      have hy' : y ∈ Subring.map (e₁ : M₁' →+* L₁') i₁.range := by rw [h₁]; exact hy
      obtain ⟨z, hz, hzy⟩ := Subring.mem_map.mp hy'
      rw [← hzy]
      simpa only [RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] using hz
    have hσy : σ.symm (e₁.symm y) ∈ i₂.range :=
      Submission.NeukirchUchida.mapsBase_mem_symm i₁ i₂ hσ hy₁
    have hy₂ : e₂ (σ.symm (e₁.symm y)) ∈ j₂.range := by
      have h : e₂ (σ.symm (e₁.symm y)) ∈ Subring.map (e₂ : M₂' →+* L₂') i₂.range :=
        Subring.mem_map.mpr ⟨σ.symm (e₁.symm y), hσy, rfl⟩
      rwa [h₂] at h
    simpa only [RingEquiv.symm_trans_apply, RingEquiv.trans_apply, RingEquiv.symm_symm] using hy₂

/-- The converse of `mapsBase_conj`: conjugation by the inverse isomorphisms. -/
theorem mapsBase_conj_symm (i₁ : A₁ →+* M₁') (i₂ : A₂ →+* M₂') (j₁ : B₁ →+* L₁')
    (j₂ : B₂ →+* L₂') (e₁ : M₁' ≃+* L₁') (e₂ : M₂' ≃+* L₂')
    (h₁ : Subring.map (e₁ : M₁' →+* L₁') i₁.range = j₁.range)
    (h₂ : Subring.map (e₂ : M₂' →+* L₂') i₂.range = j₂.range)
    (τ : L₂' ≃+* L₁') (hτ : Submission.NeukirchUchida.MapsBase j₁ j₂ τ) :
    Submission.NeukirchUchida.MapsBase i₁ i₂ (e₂.trans (τ.trans e₁.symm)) := by
  have h₁' : Subring.map ((e₁.symm) : L₁' →+* M₁') j₁.range = i₁.range :=
    Submission.NeukirchUchida.subring_map_symm_of_map_eq e₁ i₁.range j₁.range h₁
  have h₂' : Subring.map ((e₂.symm) : L₂' →+* M₂') j₂.range = i₂.range :=
    Submission.NeukirchUchida.subring_map_symm_of_map_eq e₂ i₂.range j₂.range h₂
  exact mapsBase_conj j₁ j₂ i₁ i₂ e₁.symm e₂.symm h₁' h₂' τ hτ

end MapsBaseConj

/-! ## §3. The `MapsBase` condition for the `ULift` pair -/

section MapsBaseULift

variable {K₁ : Type u₁} [Field K₁] {K₂ : Type u₂} [Field K₂]
  {K₁' : Type u₃} [Field K₁'] [Algebra K₁ K₁'] {K₂' : Type u₄} [Field K₂'] [Algebra K₂ K₂']

/-- The (`rfl`-)formula for the inverse of the conjugation bijection. -/
theorem uliftRingEquivEquiv_symm_apply_def (X : K₂' ≃+* K₁') :
    uliftRingEquivEquiv.symm X =
      (ULift.ringEquiv : ULift.{w} K₂' ≃+* K₂').trans
        (X.trans (ULift.ringEquiv : ULift.{w} K₁' ≃+* K₁').symm) := rfl

/-- `uliftRingEquivEquiv` is a bijection with the expected inverse: applying the conjugate of `σ'`
back recovers `σ'`. -/
theorem uliftRingEquivEquiv_inv_trans (σ' : ULift.{w} K₂' ≃+* ULift.{w} K₁') :
    (ULift.ringEquiv : ULift.{w} K₂' ≃+* K₂').trans
        ((uliftRingEquivEquiv σ').trans (ULift.ringEquiv : ULift.{w} K₁' ≃+* K₁').symm) = σ' :=
  Equiv.symm_apply_apply uliftRingEquivEquiv σ'

/-- **The `MapsBase` condition transports along the `ULift` conjugation.** -/
theorem mapsBase_ulift_iff (σ' : ULift.{w} K₂' ≃+* ULift.{w} K₁') :
    Submission.NeukirchUchida.MapsBase (algebraMap (ULift.{w} K₁) (ULift.{w} K₁'))
      (algebraMap (ULift.{w} K₂) (ULift.{w} K₂')) σ' ↔
    Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂')
      (uliftRingEquivEquiv σ') := by
  constructor
  · intro hσ
    exact mapsBase_conj (A₁ := ULift.{w} K₁) (B₁ := K₁) (A₂ := ULift.{w} K₂) (B₂ := K₂)
      (M₁' := ULift.{w} K₁') (M₂' := ULift.{w} K₂') (L₁' := K₁') (L₂' := K₂')
      (algebraMap (ULift.{w} K₁) (ULift.{w} K₁')) (algebraMap (ULift.{w} K₂) (ULift.{w} K₂'))
      (algebraMap K₁ K₁') (algebraMap K₂ K₂') (ULift.ringEquiv : ULift.{w} K₁' ≃+* K₁')
      (ULift.ringEquiv : ULift.{w} K₂' ≃+* K₂')
      (Submission.NeukirchUchida.mapsBase_symm_alg (mapsBase_ulift K₁ K₁'))
      (Submission.NeukirchUchida.mapsBase_symm_alg (mapsBase_ulift K₂ K₂')) σ' hσ
  · intro hσ
    have h := mapsBase_conj_symm (A₁ := ULift.{w} K₁) (B₁ := K₁) (A₂ := ULift.{w} K₂) (B₂ := K₂)
      (M₁' := ULift.{w} K₁') (M₂' := ULift.{w} K₂') (L₁' := K₁') (L₂' := K₂')
      (algebraMap (ULift.{w} K₁) (ULift.{w} K₁')) (algebraMap (ULift.{w} K₂) (ULift.{w} K₂'))
      (algebraMap K₁ K₁') (algebraMap K₂ K₂') (ULift.ringEquiv : ULift.{w} K₁' ≃+* K₁')
      (ULift.ringEquiv : ULift.{w} K₂' ≃+* K₂')
      (Submission.NeukirchUchida.mapsBase_symm_alg (mapsBase_ulift K₁ K₁'))
      (Submission.NeukirchUchida.mapsBase_symm_alg (mapsBase_ulift K₂ K₂'))
      (uliftRingEquivEquiv σ') hσ
    rwa [uliftRingEquivEquiv_inv_trans σ'] at h

end MapsBaseULift

/-! ## §4. The conjugacy condition -/

section ConjCondition

variable {K₁ : Type u₁} [Field K₁] {K₂ : Type u₂} [Field K₂]
  {K₁' : Type u₃} [Field K₁'] [Algebra K₁ K₁'] {K₂' : Type u₄} [Field K₂'] [Algebra K₂ K₂']

/-- **The pure `RingEquiv` computation of the descent.**

With `Σ = e₂⁻¹ ∘ σ ∘ e₁` and `T = e₁⁻¹ ∘ τ ∘ e₁`, conjugating `σ` by `T` and pushing through `e₂` is
the same as conjugating `Σ` by `τ`:
`e₂⁻¹ ∘ (σ ∘ T ∘ σ⁻¹) ∘ e₂ = Σ ∘ τ ∘ Σ⁻¹`.  (All compositions are read right to left.) -/
theorem ulift_conj_identity_down {M₁ M₂ L₁ L₂ : Type*} [Field M₁] [Field M₂] [Field L₁] [Field L₂]
    (e₁ : M₁ ≃+* L₁) (e₂ : M₂ ≃+* L₂) (σ : M₂ ≃+* M₁) (τ : L₁ ≃+* L₁) :
    e₂.symm.trans ((σ.trans ((e₁.trans (τ.trans e₁.symm)).trans σ.symm)).trans e₂) =
      (e₂.symm.trans (σ.trans e₁)).trans (τ.trans (e₂.symm.trans (σ.trans e₁)).symm) := by
  ext x
  simp only [RingEquiv.trans_apply, RingEquiv.symm_trans_apply, RingEquiv.symm_apply_apply,
    RingEquiv.symm_symm]

/-- **The pure `RingEquiv` computation of the ascent**, the reverse of
`ulift_conj_identity_down`. -/
theorem ulift_conj_identity_up {M₁ M₂ L₁ L₂ : Type*} [Field M₁] [Field M₂] [Field L₁] [Field L₂]
    (e₁ : M₁ ≃+* L₁) (e₂ : M₂ ≃+* L₂) (σ : M₂ ≃+* M₁) (τ : M₁ ≃+* M₁) :
    e₂.trans (((e₂.symm.trans (σ.trans e₁)).trans
        ((e₁.symm.trans (τ.trans e₁)).trans (e₂.symm.trans (σ.trans e₁)).symm)).trans e₂.symm) =
      σ.trans (τ.trans σ.symm) := by
  ext x
  simp only [RingEquiv.trans_apply, RingEquiv.symm_trans_apply, RingEquiv.symm_apply_apply,
    RingEquiv.symm_symm]

/-- **The conjugacy condition transports from the lifted data to the original data.** -/
theorem conjCondition_ulift_down (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (σ' : ULift.{w} K₂' ≃+* ULift.{w} K₁')
    (h : ∀ g' : Gal(ULift.{w} K₁' / ULift.{w} K₁),
      transportGalEquiv ϕ g' = σ'.trans (g'.toRingEquiv.trans σ'.symm)) :
    ∀ g : Gal(K₁'/K₁),
      ϕ g = (uliftRingEquivEquiv σ').trans (g.toRingEquiv.trans (uliftRingEquivEquiv σ').symm) := by
  intro g
  rw [transportGalEquiv_symm_apply ϕ g, uliftGalEquiv_toRingEquiv, h,
    uliftGalEquiv_symm_toRingEquiv, uliftRingEquivEquiv_apply]
  exact ulift_conj_identity_down (ULift.ringEquiv : ULift.{w} K₁' ≃+* K₁')
    (ULift.ringEquiv : ULift.{w} K₂' ≃+* K₂') σ' g.toRingEquiv

/-- **The conjugacy condition transports from the original data to the lifted data.** -/
theorem conjCondition_ulift_up (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (σ' : ULift.{w} K₂' ≃+* ULift.{w} K₁')
    (h : ∀ g : Gal(K₁'/K₁),
      ϕ g = (uliftRingEquivEquiv σ').trans (g.toRingEquiv.trans (uliftRingEquivEquiv σ').symm)) :
    ∀ g' : Gal(ULift.{w} K₁' / ULift.{w} K₁),
      transportGalEquiv ϕ g' = σ'.trans (g'.toRingEquiv.trans σ'.symm) := by
  intro g'
  rw [transportGalEquiv_apply ϕ g', uliftGalEquiv_symm_toRingEquiv, h,
    uliftGalEquiv_toRingEquiv, uliftRingEquivEquiv_apply]
  exact ulift_conj_identity_up (ULift.ringEquiv : ULift.{w} K₁' ≃+* K₁')
    (ULift.ringEquiv : ULift.{w} K₂' ≃+* K₂') σ' g'.toRingEquiv

/-- **The conjugacy condition transports along the `ULift` conjugation** (both directions). -/
theorem conjCondition_ulift_iff (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (σ' : ULift.{w} K₂' ≃+* ULift.{w} K₁') :
    (∀ g' : Gal(ULift.{w} K₁' / ULift.{w} K₁),
        transportGalEquiv ϕ g' = σ'.trans (g'.toRingEquiv.trans σ'.symm)) ↔
      (∀ g : Gal(K₁'/K₁),
        ϕ g = (uliftRingEquivEquiv σ').trans (g.toRingEquiv.trans (uliftRingEquivEquiv σ').symm)) :=
  ⟨conjCondition_ulift_down ϕ σ', conjCondition_ulift_up ϕ σ'⟩

end ConjCondition

/-! ## §5. The `∃!` statement -/

section ExistsUnique

variable {K₁ : Type u₁} [Field K₁] {K₂ : Type u₂} [Field K₂]
  {K₁' : Type u₃} [Field K₁'] [Algebra K₁ K₁'] {K₂' : Type u₄} [Field K₂'] [Algebra K₂ K₂']

/-- **The universe-unification of the endgame `∃!` statement.**

For data in four independent universes `u₁ u₂ u₃ u₄` and any universe `w`, the `∃!` statement of
Neukirch–Uchida for `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` is equivalent to the corresponding statement
for the lifted data (`ULift.{w} Kᵢ` — in `Type (max uᵢ w)`) and the transported isomorphism
`transportGalEquiv ϕ`.  The equivalence is realized by conjugation of the solution with
`ULift.ringEquiv`, `σ ↦ e₂⁻¹ ∘ σ ∘ e₁` (`uliftRingEquivEquiv`).

Both directions of the `↔` are the useful ones: the `.mp` direction descends a solution of the wall
at the lifted types to the challenge's own universes, and the `.mpr` direction ascends. -/
theorem existsUnique_ulift (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) :
    (∃! σ' : ULift.{w} K₂' ≃+* ULift.{w} K₁',
        Submission.NeukirchUchida.MapsBase (algebraMap (ULift.{w} K₁) (ULift.{w} K₁'))
            (algebraMap (ULift.{w} K₂) (ULift.{w} K₂')) σ' ∧
          ∀ g' : Gal(ULift.{w} K₁' / ULift.{w} K₁),
            transportGalEquiv ϕ g' = σ'.trans (g'.toRingEquiv.trans σ'.symm)) ↔
      (∃! σ : K₂' ≃+* K₁',
        Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
          ∀ g : Gal(K₁'/K₁),
            ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)) :=
  Equiv.existsUnique_congr uliftRingEquivEquiv
    fun σ' => and_congr (mapsBase_ulift_iff σ') (conjCondition_ulift_iff ϕ σ')

/-- The descent form of `existsUnique_ulift`: **a solution at the lifted types gives a solution at
the original universes.** -/
theorem existsUnique_ulift_mp (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (h : ∃! σ' : ULift.{w} K₂' ≃+* ULift.{w} K₁',
        Submission.NeukirchUchida.MapsBase (algebraMap (ULift.{w} K₁) (ULift.{w} K₁'))
            (algebraMap (ULift.{w} K₂) (ULift.{w} K₂')) σ' ∧
          ∀ g' : Gal(ULift.{w} K₁' / ULift.{w} K₁),
            transportGalEquiv ϕ g' = σ'.trans (g'.toRingEquiv.trans σ'.symm)) :
    ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  (existsUnique_ulift ϕ).mp h

/-- The ascent form of `existsUnique_ulift`: **a solution at the original universes gives a solution
at the lifted types.** -/
theorem existsUnique_ulift_mpr (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (h : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)) :
    ∃! σ' : ULift.{w} K₂' ≃+* ULift.{w} K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap (ULift.{w} K₁) (ULift.{w} K₁'))
          (algebraMap (ULift.{w} K₂) (ULift.{w} K₂')) σ' ∧
        ∀ g' : Gal(ULift.{w} K₁' / ULift.{w} K₁),
          transportGalEquiv ϕ g' = σ'.trans (g'.toRingEquiv.trans σ'.symm) :=
  (existsUnique_ulift ϕ).mpr h

end ExistsUnique

end NK.UniverseUnify
