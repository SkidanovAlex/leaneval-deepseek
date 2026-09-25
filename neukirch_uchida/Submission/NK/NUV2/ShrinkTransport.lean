/-
# Shrinking the Neukirch–Uchida challenge to universe zero

The four inputs of the second Neukirch–Uchida wall (`NK.NUV2.LCAll`, `…FrobAll`, `…ResAll`,
`…ChebAll`) are available at every universe `u` in which the fields live; the version
`NK.NUV2.Capstone0` uses them only at `u = 0`.  This module performs the "universe bookkeeping"
which bridges the two: it compares an arbitrary pair of number fields `K ⊂ K'` with their
universe-zero models `Shrink K`, `Shrink K'`.

Mathlib (and `NK.GlobalCFTdeep.HasseIndex`) already transport the field, number-field, algebra
and finite-dimensionality structures to `Shrink`.  What is added here:

* the smallness of a separable closure of a number field (`countable_of_isSepClosure`), from
  Mathlib's `Algebraic.countable`;
* the `IsSepClosed`/`IsSepClosure` structures on the shrunk model
  (`isSepClosed_of_ringEquiv`, `instIsSepClosureShrink`);
* the transport of the whole endgame statement — the comparison isomorphism of Galois groups
  `shrinkGalEquiv` (a *homeomorphism* for the Krull topologies, from
  `NK.NeukirchUchida.isHomeomorph_conjHomEquiv`), the transported isomorphism
  `transportGalEquiv` of a homeomorphic isomorphism of absolute Galois groups, and the equivalence
  of the `∃!` statements (`existsUnique_shrink`).

This is the exact analogue, for `Shrink.{0}`, of
`Submission/Work/UniverseUnify/Transport.lean` for `ULift`.
-/

import Mathlib
import Submission.NK.GlobalCFTdeep.hasseNorm_index_eq_universe
import Submission.NK.UniverseUnify.Transport

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace NK.NUV2.ShrinkModels

open Submission.NeukirchUchida
open scoped Topology

universe u v u₁ u₂ u₃ u₄

/-! ## §1. The universe-zero models -/

/-- A number field is countable. -/
theorem countable_of_numberField (K : Type u) [Field K] [NumberField K] : Countable K :=
  Finsupp.Countable.of_moduleFinite (R := ℚ) (M := K)

/-- **A separable closure of a number field is countable.**  The extension is algebraic
(`Algebra.IsSeparable.isAlgebraic`), so it is contained in the set of algebraic elements of `K'`
over `K`, which is countable (`Algebraic.countable`) because `K` is. -/
theorem countable_of_isSepClosure (K : Type u) [Field K] [NumberField K] (K' : Type v) [Field K']
    [Algebra K K'] [IsSepClosure K K'] : Countable K' := by
  haveI : Countable K := countable_of_numberField K
  refine Set.countable_univ_iff.mp ?_
  refine (Algebraic.countable K K').mono ?_
  intro x _
  exact Algebra.IsAlgebraic.isAlgebraic x

/-- A number field, being countable, is small at universe zero. -/
theorem small_of_numberField (K : Type u) [Field K] [NumberField K] : Small.{0} K := by
  haveI : Countable K := countable_of_numberField K
  exact Countable.toSmall K

/-- A separable closure of a number field is small at universe zero. -/
theorem small_of_isSepClosure (K : Type u) [Field K] [NumberField K] (K' : Type v) [Field K']
    [Algebra K K'] [IsSepClosure K K'] : Small.{0} K' := by
  haveI : Countable K' := countable_of_isSepClosure K K'
  exact Countable.toSmall K'

/-- **Separable closedness is invariant under ring equivalences**: if `M` is separably closed and
`e : L ≃+* M`, then `L` is separably closed.  A separable polynomial over `L` is carried to a
separable polynomial over `M`, which splits there, and the roots are pulled back along the
surjection `e`. -/
theorem isSepClosed_of_ringEquiv {L M : Type*} [Field L] [Field M] (e : L ≃+* M) [IsSepClosed M] :
    IsSepClosed L where
  splits_of_separable p hp := by
    refine Polynomial.Splits.of_splits_map (e : L →+* M) ?_ ?_
    · exact IsSepClosed.splits_of_separable (p.map (e : L →+* M))
        (hp.map (f := (e : L →+* M)))
    · intro a _
      exact RingHom.mem_range.mpr ⟨e.symm a, e.apply_symm_apply a⟩

/-- The universe-zero model of a separably closed field is separably closed. -/
instance instIsSepClosedShrink {L : Type u} [Field L] [IsSepClosed L] [Small.{0} L] :
    IsSepClosed (Shrink.{0} L) :=
  isSepClosed_of_ringEquiv (Shrink.ringEquiv L)

/-- **The universe-zero model of a separable closure is a separable closure.**  Separable closedness
is transferred by `instIsSepClosedShrink`; separability of the extension by
`Algebra.IsSeparable.iff_of_equiv_equiv` applied to the two shrink equivalences, whose compatibility
with the algebra maps is `NK.GlobalCFTdeep.HasseIndex.shrink_hc`. -/
instance instIsSepClosureShrink {K : Type u} {K' : Type v} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] [Small.{0} K] [Small.{0} K'] :
    IsSepClosure (Shrink.{0} K) (Shrink.{0} K') := by
  haveI hsc : IsSepClosed K' := IsSepClosure.sep_closed K
  haveI : IsSepClosed (Shrink.{0} K') := instIsSepClosedShrink
  haveI : Algebra.IsSeparable (Shrink.{0} K) (Shrink.{0} K') :=
    (Algebra.IsSeparable.iff_of_equiv_equiv (Shrink.ringEquiv K).symm (Shrink.ringEquiv K').symm
      (NK.GlobalCFTdeep.HasseIndex.shrink_hc K K')).mp
      (IsSepClosure.separable : Algebra.IsSeparable K K')
  exact ⟨inferInstance, inferInstance⟩

/-! ## §2. The comparison of Galois groups -/

/-- **The comparison isomorphism of Galois groups.**  Conjugation by the ring equivalence
`Shrink.ringEquiv L : Shrink L ≃+* L` identifies `Gal(Shrink L / Shrink K)` with `Gal(L/K)`; this
is `Submission.NeukirchUchida.conjHomEquiv` applied to the `MapsBase` computation
`NK.GlobalCFTdeep.HasseIndex.shrink_mapsBase`. -/
noncomputable def shrinkGalEquiv (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] : Gal(Shrink.{0} L / Shrink.{0} K) ≃* Gal(L/K) :=
  conjHomEquiv (NK.GlobalCFTdeep.HasseIndex.shrink_mapsBase K L)

/-- **Continuity of the comparison isomorphism** (the direction
`Gal(Shrink L / Shrink K) → Gal(L/K)`): conjugation by `Shrink.ringEquiv L` is continuous for the
Krull topologies. -/
theorem continuous_shrinkGalEquiv (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] :
    Continuous (shrinkGalEquiv K L : Gal(Shrink.{0} L / Shrink.{0} K) → Gal(L/K)) :=
  NK.NeukirchUchida.continuous_conjHom (Shrink.ringEquiv L).symm
    (NK.GlobalCFTdeep.HasseIndex.shrink_mapsBase K L)

/-- **Continuity of the inverse** (the direction `Gal(L/K) → Gal(Shrink L / Shrink K)`), i.e. of
conjugation by `(Shrink.ringEquiv L).symm`. -/
theorem continuous_shrinkGalEquiv_symm (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [Small.{0} K] [Small.{0} L] :
    Continuous ((shrinkGalEquiv K L).symm : Gal(L/K) → Gal(Shrink.{0} L / Shrink.{0} K)) :=
  NK.NeukirchUchida.continuous_conjHom (Shrink.ringEquiv L)
    (Submission.NeukirchUchida.mapsBase_symm_alg
      (NK.GlobalCFTdeep.HasseIndex.shrink_mapsBase K L))

/-- **The comparison isomorphism is a homeomorphism for the Krull topologies.** -/
theorem isHomeomorph_shrinkGalEquiv (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] :
    IsHomeomorph (shrinkGalEquiv K L : Gal(Shrink.{0} L / Shrink.{0} K) → Gal(L/K)) :=
  NK.UniverseUnify.isHomeomorph_of_continuous (shrinkGalEquiv K L)
    (continuous_shrinkGalEquiv K L) (continuous_shrinkGalEquiv_symm K L)

/-- **The inverse of the comparison isomorphism is a homeomorphism** (the form used when the
universe-zero data are the source). -/
theorem isHomeomorph_shrinkGalEquiv_symm (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [Small.{0} K] [Small.{0} L] :
    IsHomeomorph ((shrinkGalEquiv K L).symm : Gal(L/K) → Gal(Shrink.{0} L / Shrink.{0} K)) :=
  NK.UniverseUnify.isHomeomorph_of_continuous (shrinkGalEquiv K L).symm
    (continuous_shrinkGalEquiv_symm K L) (continuous_shrinkGalEquiv K L)

/-- The underlying ring equivalence of `shrinkGalEquiv K L g` is `g` conjugated by the shrink ring
equivalence (`Submission.NeukirchUchida.conj_toRingEquiv`). -/
theorem shrinkGalEquiv_toRingEquiv (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] (g : Gal(Shrink.{0} L / Shrink.{0} K)) :
    (shrinkGalEquiv K L g).toRingEquiv =
      (Shrink.ringEquiv L).symm.trans (g.toRingEquiv.trans (Shrink.ringEquiv L)) :=
  Submission.NeukirchUchida.conj_toRingEquiv
    (NK.GlobalCFTdeep.HasseIndex.shrink_mapsBase K L) g

/-- The underlying ring equivalence of `(shrinkGalEquiv K L).symm g` is `g` conjugated by the
inverse of the shrink ring equivalence. -/
theorem shrinkGalEquiv_symm_toRingEquiv (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [Small.{0} K] [Small.{0} L] (g : Gal(L/K)) :
    ((shrinkGalEquiv K L).symm g).toRingEquiv =
      (Shrink.ringEquiv L).trans (g.toRingEquiv.trans (Shrink.ringEquiv L).symm) :=
  Submission.NeukirchUchida.conj_toRingEquiv
    (Submission.NeukirchUchida.mapsBase_symm_alg
      (NK.GlobalCFTdeep.HasseIndex.shrink_mapsBase K L)) g

/-! ## §3. The transport of the endgame data -/

section Transport

variable {K₁ : Type u₁} [Field K₁] {K₂ : Type u₂} [Field K₂]
  {K₁' : Type u₃} [Field K₁'] [Algebra K₁ K₁'] {K₂' : Type u₄} [Field K₂'] [Algebra K₂ K₂']
  [Small.{0} K₁] [Small.{0} K₂] [Small.{0} K₁'] [Small.{0} K₂']

/-- **The conjugation bijection of ring isomorphisms.**  `σ ↦ e₂⁻¹ ∘ σ ∘ e₁` with
`eᵢ = Shrink.ringEquiv Kᵢ'`: a solution for the universe-zero models is the same thing as a solution
for the original fields. -/
noncomputable def shrinkRingEquivEquiv :
    (Shrink.{0} K₂' ≃+* Shrink.{0} K₁') ≃ (K₂' ≃+* K₁') where
  toFun σ := (Shrink.ringEquiv K₂').symm.trans (σ.trans (Shrink.ringEquiv K₁'))
  invFun τ := (Shrink.ringEquiv K₂').trans (τ.trans (Shrink.ringEquiv K₁').symm)
  left_inv σ := by
    ext x
    simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply]
  right_inv τ := by
    ext x
    simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply]

/-- The defining formula of `shrinkRingEquivEquiv`. -/
theorem shrinkRingEquivEquiv_apply (σ : Shrink.{0} K₂' ≃+* Shrink.{0} K₁') :
    shrinkRingEquivEquiv σ = (Shrink.ringEquiv K₂').symm.trans
      (σ.trans (Shrink.ringEquiv K₁')) := rfl

/-- The inverse formula of `shrinkRingEquivEquiv`. -/
theorem shrinkRingEquivEquiv_symm_apply_def (X : K₂' ≃+* K₁') :
    shrinkRingEquivEquiv.symm X = (Shrink.ringEquiv K₂').trans
      (X.trans (Shrink.ringEquiv K₁').symm) := rfl

/-- `shrinkRingEquivEquiv` is a bijection with the expected inverse. -/
theorem shrinkRingEquivEquiv_inv_trans (σ' : Shrink.{0} K₂' ≃+* Shrink.{0} K₁') :
    (Shrink.ringEquiv K₂').trans
      ((shrinkRingEquivEquiv σ').trans (Shrink.ringEquiv K₁').symm) = σ' :=
  Equiv.symm_apply_apply shrinkRingEquivEquiv σ'

/-- **The `MapsBase` condition transports along the shrink conjugation.** -/
theorem mapsBase_shrink_iff (σ' : Shrink.{0} K₂' ≃+* Shrink.{0} K₁') :
    Submission.NeukirchUchida.MapsBase (algebraMap (Shrink.{0} K₁) (Shrink.{0} K₁'))
      (algebraMap (Shrink.{0} K₂) (Shrink.{0} K₂')) σ' ↔
    Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂')
      (shrinkRingEquivEquiv σ') := by
  constructor
  · intro hσ
    exact NK.UniverseUnify.mapsBase_conj
      (A₁ := Shrink K₁) (B₁ := K₁) (A₂ := Shrink K₂) (B₂ := K₂)
      (M₁' := Shrink K₁') (M₂' := Shrink K₂') (L₁' := K₁') (L₂' := K₂')
      (algebraMap (Shrink K₁) (Shrink K₁')) (algebraMap (Shrink K₂) (Shrink K₂'))
      (algebraMap K₁ K₁') (algebraMap K₂ K₂') (Shrink.ringEquiv K₁') (Shrink.ringEquiv K₂')
      (Submission.NeukirchUchida.mapsBase_symm_alg
        (NK.GlobalCFTdeep.HasseIndex.shrink_mapsBase K₁ K₁'))
      (Submission.NeukirchUchida.mapsBase_symm_alg
        (NK.GlobalCFTdeep.HasseIndex.shrink_mapsBase K₂ K₂')) σ' hσ
  · intro hσ
    have h := NK.UniverseUnify.mapsBase_conj_symm
      (A₁ := Shrink K₁) (B₁ := K₁) (A₂ := Shrink K₂) (B₂ := K₂)
      (M₁' := Shrink K₁') (M₂' := Shrink K₂') (L₁' := K₁') (L₂' := K₂')
      (algebraMap (Shrink K₁) (Shrink K₁')) (algebraMap (Shrink K₂) (Shrink K₂'))
      (algebraMap K₁ K₁') (algebraMap K₂ K₂') (Shrink.ringEquiv K₁') (Shrink.ringEquiv K₂')
      (Submission.NeukirchUchida.mapsBase_symm_alg
        (NK.GlobalCFTdeep.HasseIndex.shrink_mapsBase K₁ K₁'))
      (Submission.NeukirchUchida.mapsBase_symm_alg
        (NK.GlobalCFTdeep.HasseIndex.shrink_mapsBase K₂ K₂'))
      (shrinkRingEquivEquiv σ') hσ
    rwa [shrinkRingEquivEquiv_inv_trans σ'] at h

/-- **Transport of an isomorphism of absolute Galois groups to the universe-zero models.** -/
noncomputable def transportGalEquiv (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) :
    Gal(Shrink.{0} K₁' / Shrink.{0} K₁) ≃* Gal(Shrink.{0} K₂' / Shrink.{0} K₂) :=
  (shrinkGalEquiv K₁ K₁').trans (ϕ.trans (shrinkGalEquiv K₂ K₂').symm)

/-- The defining computation of the transported isomorphism. -/
theorem transportGalEquiv_apply (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (g : Gal(Shrink.{0} K₁' / Shrink.{0} K₁)) :
    transportGalEquiv ϕ g = (shrinkGalEquiv K₂ K₂').symm (ϕ (shrinkGalEquiv K₁ K₁' g)) := rfl

/-- The inverse relation of `transportGalEquiv_apply`. -/
theorem transportGalEquiv_symm_apply (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (g : Gal(K₁'/K₁)) :
    ϕ g = shrinkGalEquiv K₂ K₂'
      ((transportGalEquiv ϕ) ((shrinkGalEquiv K₁ K₁').symm g)) := by
  rw [transportGalEquiv_apply]
  simp

/-- **The transported isomorphism is a homeomorphism if `ϕ` is.** -/
theorem isHomeomorph_transportGalEquiv (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    IsHomeomorph (transportGalEquiv ϕ :
      Gal(Shrink.{0} K₁' / Shrink.{0} K₁) → Gal(Shrink.{0} K₂' / Shrink.{0} K₂)) := by
  have h₁ : IsHomeomorph (shrinkGalEquiv K₁ K₁' :
      Gal(Shrink.{0} K₁' / Shrink.{0} K₁) → Gal(K₁'/K₁)) := isHomeomorph_shrinkGalEquiv K₁ K₁'
  have h₂ : IsHomeomorph ((shrinkGalEquiv K₂ K₂').symm :
      Gal(K₂'/K₂) → Gal(Shrink.{0} K₂' / Shrink.{0} K₂)) := isHomeomorph_shrinkGalEquiv_symm K₂ K₂'
  have hcomp : IsHomeomorph
      (((shrinkGalEquiv K₂ K₂').symm : Gal(K₂'/K₂) → Gal(Shrink.{0} K₂' / Shrink.{0} K₂)) ∘
        (ϕ : Gal(K₁'/K₁) → Gal(K₂'/K₂)) ∘
        (shrinkGalEquiv K₁ K₁' : Gal(Shrink.{0} K₁' / Shrink.{0} K₁) → Gal(K₁'/K₁))) :=
    (h₂.comp he).comp h₁
  exact ⟨hcomp.continuous, hcomp.isOpenMap, (transportGalEquiv ϕ).bijective⟩

/-- **The conjugacy condition transports from the model to the original data.** -/
theorem conjCondition_shrink_down (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (σ' : Shrink.{0} K₂' ≃+* Shrink.{0} K₁')
    (h : ∀ g' : Gal(Shrink.{0} K₁' / Shrink.{0} K₁),
      transportGalEquiv ϕ g' = σ'.trans (g'.toRingEquiv.trans σ'.symm)) :
    ∀ g : Gal(K₁'/K₁),
      ϕ g = (shrinkRingEquivEquiv σ').trans
        (g.toRingEquiv.trans (shrinkRingEquivEquiv σ').symm) := by
  intro g
  rw [transportGalEquiv_symm_apply ϕ g, shrinkGalEquiv_toRingEquiv, h,
    shrinkGalEquiv_symm_toRingEquiv, shrinkRingEquivEquiv_apply]
  exact NK.UniverseUnify.ulift_conj_identity_down (Shrink.ringEquiv K₁') (Shrink.ringEquiv K₂')
    σ' g.toRingEquiv

/-- **The conjugacy condition transports from the original data to the model.** -/
theorem conjCondition_shrink_up (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (σ' : Shrink.{0} K₂' ≃+* Shrink.{0} K₁')
    (h : ∀ g : Gal(K₁'/K₁),
      ϕ g = (shrinkRingEquivEquiv σ').trans
        (g.toRingEquiv.trans (shrinkRingEquivEquiv σ').symm)) :
    ∀ g' : Gal(Shrink.{0} K₁' / Shrink.{0} K₁),
      transportGalEquiv ϕ g' = σ'.trans (g'.toRingEquiv.trans σ'.symm) := by
  intro g'
  rw [transportGalEquiv_apply ϕ g', shrinkGalEquiv_symm_toRingEquiv, h,
    shrinkGalEquiv_toRingEquiv, shrinkRingEquivEquiv_apply]
  exact NK.UniverseUnify.ulift_conj_identity_up (Shrink.ringEquiv K₁') (Shrink.ringEquiv K₂')
    σ' g'.toRingEquiv

/-- **The conjugacy condition transports along the shrink conjugation** (both directions). -/
theorem conjCondition_shrink_iff (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (σ' : Shrink.{0} K₂' ≃+* Shrink.{0} K₁') :
    (∀ g' : Gal(Shrink.{0} K₁' / Shrink.{0} K₁),
        transportGalEquiv ϕ g' = σ'.trans (g'.toRingEquiv.trans σ'.symm)) ↔
      (∀ g : Gal(K₁'/K₁),
        ϕ g = (shrinkRingEquivEquiv σ').trans
          (g.toRingEquiv.trans (shrinkRingEquivEquiv σ').symm)) :=
  ⟨conjCondition_shrink_down ϕ σ', conjCondition_shrink_up ϕ σ'⟩

/-- **The universe bookkeeping of the endgame `∃!` statement.**

For data in four independent universes and any pair of number fields, the `∃!` statement of
Neukirch–Uchida for `ϕ` is equivalent to the corresponding statement for the universe-zero models
`Shrink Kᵢ'` and the transported isomorphism `transportGalEquiv ϕ`. -/
theorem existsUnique_shrink (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) :
    (∃! σ' : Shrink.{0} K₂' ≃+* Shrink.{0} K₁',
        Submission.NeukirchUchida.MapsBase (algebraMap (Shrink.{0} K₁) (Shrink.{0} K₁'))
            (algebraMap (Shrink.{0} K₂) (Shrink.{0} K₂')) σ' ∧
          ∀ g' : Gal(Shrink.{0} K₁' / Shrink.{0} K₁),
            transportGalEquiv ϕ g' = σ'.trans (g'.toRingEquiv.trans σ'.symm)) ↔
      (∃! σ : K₂' ≃+* K₁',
        Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
          ∀ g : Gal(K₁'/K₁),
            ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)) :=
  Equiv.existsUnique_congr shrinkRingEquivEquiv
    fun σ' => and_congr (mapsBase_shrink_iff σ') (conjCondition_shrink_iff ϕ σ')

/-- The descent form of `existsUnique_shrink`: a solution for the universe-zero models gives a
solution for the original fields. -/
theorem existsUnique_shrink_mp (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (h : ∃! σ' : Shrink.{0} K₂' ≃+* Shrink.{0} K₁',
        Submission.NeukirchUchida.MapsBase (algebraMap (Shrink.{0} K₁) (Shrink.{0} K₁'))
            (algebraMap (Shrink.{0} K₂) (Shrink.{0} K₂')) σ' ∧
          ∀ g' : Gal(Shrink.{0} K₁' / Shrink.{0} K₁),
            transportGalEquiv ϕ g' = σ'.trans (g'.toRingEquiv.trans σ'.symm)) :
    ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  (existsUnique_shrink ϕ).mp h

end Transport

end NK.NUV2.ShrinkModels
