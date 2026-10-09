/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Universe unification for the Neukirch–Uchida endgame — the `ULift` interface

`Submission.neukirch_uchida` (`Challenge.lean`) is stated with `{K₁ K₂ K₁' K₂' : Type*}`, i.e. it
is polymorphic in **four independent universes**.  Every chapter of this workspace, however, states
its endgame capstones for fields in a **single** universe
(`NK.EndgameRepair.ClassicalChaptersRepaired (K₁ K₂ K₁' K₂' : Type u)`,
`NK.EndgameRepair.challenge_of_repairedChapters`, …), and a single-universe statement cannot be
applied to the challenge's data.

This directory removes that gap by transporting everything along `ULift`.  This first module builds
the interface:

* the `ULift` structure instances needed to phrase the wall at the lifted types —
  `Algebra (ULift K) (ULift L)`, `NumberField (ULift K)`, `IsSepClosure (ULift K) (ULift L)`;
* the comparison isomorphism `NK.UniverseUnify.uliftGalEquiv K L`, a *topological* group
  isomorphism `Gal(ULift L / ULift K) ≃* Gal(L/K)` (Krull topologies), and the induced transport
  `NK.UniverseUnify.transportGalEquiv` of a group isomorphism of absolute Galois groups to the
  lifted types.

Nothing here mentions any hypothesis of the wall; the transport of the *endgame* (σ and `∃!`) is in
`Submission/Work/UniverseUnify/Transport.lean`.
-/

import Mathlib
import Submission.NK.NeukirchUchida.isHomeomorph_conjHomEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.UniverseUnify

open scoped Topology

universe u v w u₁ u₂ u₃ u₄

/-! ## §1. The `ULift` instances -/

/-- **The canonical `ULift K`-algebra structure on `ULift L`.**

Mathlib provides `ULift.algebra' : Algebra (ULift R) A` (deliberately *not* an instance, to avoid a
diamond) and `ULift.algebra : Algebra R (ULift A)`; their composite is the structure we need.  It is
written here directly through `RingHom.toAlgebra`, so that `algebraMap` is *definitionally*
`ULift.up ∘ algebraMap K L ∘ ULift.down` (see `algebraMap_ulift_up`). -/
instance instAlgebraULift {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] :
    Algebra (ULift.{w} K) (ULift.{w} L) :=
  RingHom.toAlgebra
    (((ULift.ringEquiv : ULift.{w} L ≃+* L).symm : L →+* ULift.{w} L).comp
      ((algebraMap K L).comp ((ULift.ringEquiv : ULift.{w} K ≃+* K) : ULift.{w} K →+* K)))

/-- The defining computation of the lifted algebra structure: `algebraMap` is `ULift.up` composed
with `algebraMap K L` composed with `ULift.down`.  The proof is `rfl`. -/
@[simp]
theorem algebraMap_ulift_up {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (x : K) :
    algebraMap (ULift.{w} K) (ULift.{w} L) (ULift.up x) = ULift.up (algebraMap K L x) := rfl

/-- The same computation in the `down` direction. -/
@[simp]
theorem ulift_down_algebraMap {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (x : ULift.{w} K) :
    (algebraMap (ULift.{w} K) (ULift.{w} L) x).down = algebraMap K L x.down := by
  obtain ⟨a⟩ := x
  rfl

/-- `ULift` preserves characteristic zero. -/
instance instCharZeroULift {K : Type u} [Field K] [CharZero K] : CharZero (ULift.{w} K) where
  cast_injective m n h := by
    refine (@CharZero.cast_injective K _ _) ?_
    simpa using congrArg ULift.down h

/-- `ULift` preserves finite-dimensionality over `ℚ`. -/
instance instFiniteDimensionalULift {K : Type u} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] : FiniteDimensional ℚ (ULift.{w} K) :=
  Module.Finite.equiv ((ULift.moduleEquiv (M := K) : ULift.{w} K ≃ₗ[ℚ] K).symm)

/-- `ULift` preserves the property of being a number field. -/
instance instNumberFieldULift {K : Type u} [Field K] [NumberField K] :
    NumberField (ULift.{w} K) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

/-- `ULift` preserves separable closedness: if `p` is separable over `ULift L`, its image under
`ULift.ringEquiv` is a separable polynomial over the separably closed field `L`, hence splits;
pulling the splitting back along the (surjective) ring homomorphism `ULift.ringEquiv` splits `p`. -/
instance instIsSepClosedULift {L : Type v} [Field L] [IsSepClosed L] :
    IsSepClosed (ULift.{w} L) where
  splits_of_separable p hp := by
    have hmap : (p.map ((ULift.ringEquiv : ULift.{w} L ≃+* L) : ULift.{w} L →+* L)).Splits :=
      IsSepClosed.splits_of_separable _
        (Polynomial.Separable.map (f := ((ULift.ringEquiv : ULift.{w} L ≃+* L) :
          ULift.{w} L →+* L)) hp)
    exact hmap.of_splits_map ((ULift.ringEquiv : ULift.{w} L ≃+* L) : ULift.{w} L →+* L)
      (fun a _ => RingHom.mem_range.mpr
        ((ULift.ringEquiv : ULift.{w} L ≃+* L).surjective a))

/-- **`ULift` preserves separable closures.** -/
instance instIsSepClosureULift {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsSepClosure K L] : IsSepClosure (ULift.{w} K) (ULift.{w} L) := by
  haveI hsc : IsSepClosed L := IsSepClosure.sep_closed K
  haveI hsc' : IsSepClosed (ULift.{w} L) := instIsSepClosedULift
  haveI hsep : Algebra.IsSeparable (ULift.{w} K) (ULift.{w} L) :=
    (Algebra.IsSeparable.iff_of_equiv_equiv
      (ULift.ringEquiv : ULift.{w} K ≃+* K) (ULift.ringEquiv : ULift.{w} L ≃+* L) (by
        ext x
        exact (ulift_down_algebraMap (K := K) (L := L) x).symm)).mpr
      (IsSepClosure.separable)
  exact ⟨hsc', hsep⟩

/-! ## §2. `MapsBase` for the `ULift` ring equivalence -/

/-- **The `ULift` ring equivalence maps the lifted base field onto the base field.**

With the lifted algebra structure of §1, the range condition of
`Submission.NeukirchUchida.MapsBase` is satisfied by `(ULift.ringEquiv).symm : L ≃+* ULift L`.  This
is the crucial computation of the transport: it exhibits `Gal(ULift L / ULift K)` as *conjugation by
`ULift.ringEquiv`*, which is exactly the vocabulary of `Submission.NeukirchUchida.conjHomEquiv` and
of the already-proved continuity theorem `NK.NeukirchUchida.continuous_conjHom`. -/
theorem mapsBase_ulift (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Submission.NeukirchUchida.MapsBase (algebraMap (ULift.{w} K) (ULift.{w} L)) (algebraMap K L)
      ((ULift.ringEquiv : ULift.{w} L ≃+* L).symm : L ≃+* ULift.{w} L) := by
  rw [Submission.NeukirchUchida.MapsBase]
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Subring.mem_map.mp hy
    obtain ⟨a, rfl⟩ := RingHom.mem_range.mp hx
    refine RingHom.mem_range.mpr ⟨ULift.up a, ?_⟩
    rw [← hxy]
    exact (algebraMap_ulift_up (K := K) (L := L) a).symm
  · intro hy
    obtain ⟨b, rfl⟩ := RingHom.mem_range.mp hy
    obtain ⟨a⟩ := b
    exact Subring.mem_map.mpr
      ⟨algebraMap K L a, RingHom.mem_range.mpr ⟨a, rfl⟩,
        (algebraMap_ulift_up (K := K) (L := L) a).symm⟩

/-! ## §3. The comparison isomorphism `Gal(ULift L / ULift K) ≃* Gal(L/K)` -/

/-- **The comparison isomorphism of Galois groups.**

Conjugation by the ring equivalence `ULift.ringEquiv : ULift L ≃+* L` identifies the Galois group of
the lifted extension `ULift L / ULift K` with `Gal(L/K)`.  This is
`Submission.NeukirchUchida.conjHomEquiv` applied to the range condition `mapsBase_ulift`. -/
noncomputable def uliftGalEquiv (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Gal(ULift.{w} L / ULift.{w} K) ≃* Gal(L/K) :=
  Submission.NeukirchUchida.conjHomEquiv (mapsBase_ulift K L)

/-- A multiplicative equivalence of topological groups is a homeomorphism as soon as it and its
inverse are continuous (a bijection with continuous inverse is open). -/
theorem isHomeomorph_of_continuous {G : Type*} {H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] (e : G ≃* H) (h : Continuous (e : G → H))
    (h' : Continuous (e.symm : H → G)) : IsHomeomorph (e : G → H) :=
  ⟨h, (Equiv.continuous_symm_iff e.toEquiv).mp h', e.bijective⟩

/-- **Continuity of the comparison isomorphism** (the direction
`Gal(ULift L / ULift K) → Gal(L/K)`).  This is `NK.NeukirchUchida.continuous_conjHom` applied to
`ULift.ringEquiv`. -/
theorem continuous_uliftGalEquiv_forward (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] :
    Continuous (uliftGalEquiv K L : Gal(ULift.{w} L / ULift.{w} K) → Gal(L/K)) :=
  NK.NeukirchUchida.continuous_conjHom
    ((ULift.ringEquiv : ULift.{w} L ≃+* L).symm : L ≃+* ULift.{w} L) (mapsBase_ulift K L)

/-- **Continuity of the inverse of the comparison isomorphism** (the direction
`Gal(L/K) → Gal(ULift L / ULift K)`), i.e. of conjugation by `ULift.ringEquiv` itself. -/
theorem continuous_uliftGalEquiv_backward (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] :
    Continuous ((uliftGalEquiv K L).symm : Gal(L/K) → Gal(ULift.{w} L / ULift.{w} K)) :=
  NK.NeukirchUchida.continuous_conjHom (ULift.ringEquiv : ULift.{w} L ≃+* L)
    (Submission.NeukirchUchida.mapsBase_symm_alg (mapsBase_ulift K L))

/-- **The comparison isomorphism is a homeomorphism for the Krull topologies.**

This is the only topological input of the universe unification. -/
theorem isHomeomorph_uliftGalEquiv (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    IsHomeomorph (uliftGalEquiv K L : Gal(ULift.{w} L / ULift.{w} K) → Gal(L/K)) :=
  isHomeomorph_of_continuous _ (continuous_uliftGalEquiv_forward K L)
    (continuous_uliftGalEquiv_backward K L)

/-- **The inverse of the comparison isomorphism is a homeomorphism** (the form needed when the
single-universe capstone is applied to the lifted data). -/
theorem isHomeomorph_uliftGalEquiv_symm (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] :
    IsHomeomorph ((uliftGalEquiv K L).symm : Gal(L/K) → Gal(ULift.{w} L / ULift.{w} K)) :=
  isHomeomorph_of_continuous _ (continuous_uliftGalEquiv_backward K L)
    (continuous_uliftGalEquiv_forward K L)

/-- The underlying ring equivalence of `uliftGalEquiv K L g` is `g` conjugated by
`ULift.ringEquiv` (this is `Submission.NeukirchUchida.conj_toRingEquiv`).  It is the explicit formula
used to transport the conjugacy condition of the challenge statement. -/
theorem uliftGalEquiv_toRingEquiv (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (g : Gal(ULift.{w} L / ULift.{w} K)) :
    (uliftGalEquiv K L g).toRingEquiv =
      (ULift.ringEquiv : ULift.{w} L ≃+* L).symm.trans
        (g.toRingEquiv.trans (ULift.ringEquiv : ULift.{w} L ≃+* L)) :=
  Submission.NeukirchUchida.conj_toRingEquiv (mapsBase_ulift K L) g

/-- The underlying ring equivalence of `(uliftGalEquiv K L).symm g` is `g` conjugated by the
inverse of `ULift.ringEquiv`. -/
theorem uliftGalEquiv_symm_toRingEquiv (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] (g : Gal(L/K)) :
    ((uliftGalEquiv K L).symm g).toRingEquiv =
      (ULift.ringEquiv : ULift.{w} L ≃+* L).trans
        (g.toRingEquiv.trans (ULift.ringEquiv : ULift.{w} L ≃+* L).symm) :=
  Submission.NeukirchUchida.conj_toRingEquiv
    (Submission.NeukirchUchida.mapsBase_symm_alg (mapsBase_ulift K L)) g

/-! ## §4. Transport of an isomorphism of absolute Galois groups -/

section TransportIso

variable {K₁ : Type u₁} [Field K₁] {K₂ : Type u₂} [Field K₂]
  {K₁' : Type u₃} [Field K₁'] [Algebra K₁ K₁']
  {K₂' : Type u₄} [Field K₂'] [Algebra K₂ K₂']

/-- **Transport of a group isomorphism of absolute Galois groups to the lifted types.**

Given `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)`, this is the isomorphism
`Gal(ULift K₁' / ULift K₁) ≃* Gal(ULift K₂' / ULift K₂)` obtained by conjugating with the comparison
isomorphisms `uliftGalEquiv`.  It is the `ϕ'` to which the single-universe wall is applied.

Note the universes: `K₁` and `K₁'` may live in different universes, but the *lifted* fields
`ULift K₁`, `ULift K₁'` live in `Type (max u₁ w)` respectively `Type (max u₃ w)`; of course the wall
itself requires all four lifted fields in a single universe. -/
noncomputable def transportGalEquiv (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) :
    Gal(ULift.{w} K₁' / ULift.{w} K₁) ≃* Gal(ULift.{w} K₂' / ULift.{w} K₂) :=
  (uliftGalEquiv K₁ K₁').trans (ϕ.trans (uliftGalEquiv K₂ K₂').symm)

/-- The defining computation of the transported isomorphism: it is `ϕ` read through the comparison
isomorphisms. -/
theorem transportGalEquiv_apply (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (g : Gal(ULift.{w} K₁' / ULift.{w} K₁)) :
    transportGalEquiv ϕ g = (uliftGalEquiv K₂ K₂').symm
      (ϕ (uliftGalEquiv K₁ K₁' g)) := rfl

/-- The inverse relation: `ϕ = (uliftGalEquiv K₁ K₁').symm.trans (ϕ'.trans (uliftGalEquiv K₂ K₂'))`,
read pointwise.  This is the identity which converts the conjugacy formula for the lifted data back
to the conjugacy formula for the original data (and conversely). -/
theorem transportGalEquiv_symm_apply (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (g : Gal(K₁'/K₁)) :
    ϕ g = uliftGalEquiv K₂ K₂'
      ((transportGalEquiv ϕ) ((uliftGalEquiv K₁ K₁').symm g)) := rfl

/-- **The transported isomorphism is a homeomorphism if `ϕ` is.**  Immediate from
`isHomeomorph_uliftGalEquiv` and `IsHomeomorph.comp`. -/
theorem isHomeomorph_transportGalEquiv (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    IsHomeomorph (transportGalEquiv ϕ :
      Gal(ULift.{w} K₁' / ULift.{w} K₁) → Gal(ULift.{w} K₂' / ULift.{w} K₂)) := by
  have h₁ : IsHomeomorph (uliftGalEquiv K₁ K₁' :
      Gal(ULift.{w} K₁' / ULift.{w} K₁) → Gal(K₁'/K₁)) := isHomeomorph_uliftGalEquiv K₁ K₁'
  have h₂ : IsHomeomorph ((uliftGalEquiv K₂ K₂').symm :
      Gal(K₂'/K₂) → Gal(ULift.{w} K₂' / ULift.{w} K₂)) := isHomeomorph_uliftGalEquiv_symm K₂ K₂'
  have hcomp : IsHomeomorph
      (((uliftGalEquiv K₂ K₂').symm : Gal(K₂'/K₂) → Gal(ULift.{w} K₂' / ULift.{w} K₂)) ∘
        (ϕ : Gal(K₁'/K₁) → Gal(K₂'/K₂)) ∘
        (uliftGalEquiv K₁ K₁' : Gal(ULift.{w} K₁' / ULift.{w} K₁) → Gal(K₁'/K₁))) :=
    (h₂.comp he).comp h₁
  exact ⟨hcomp.continuous, hcomp.isOpenMap, (transportGalEquiv ϕ).bijective⟩

end TransportIso

end NK.UniverseUnify
