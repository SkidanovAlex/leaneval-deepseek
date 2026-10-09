/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.FourTwoExact
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles
import Submission.NK.GlobalCFTdeep.Herbrand.quot_TIdeles_mulEquiv_ideleClassGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The equivariant short exact sequence `0 → U(T) → 𝕀_{L,T} → C_L → 0`

This file inhabits the structure `NK.GlobalCFTdeep.MilneFourTwoExact` attached to a finite
`Gal(L/K)`-stable set `T` of places of `L` for which `𝕀_L = Lˣ · 𝕀_{L,T}`: the *second
isomorphism theorem* for the chain of `ℤ[Gal(L/K)]`-submodules

  `U(T) = Lˣ ∩ 𝕀_{L,T} ⊆ 𝕀_{L,T} ⊆ 𝕀_L`

assembled into the short exact sequence of `ℤ[Gal(L/K)]`-modules

  `0 ⟶ U(T) ⟶ 𝕀_{L,T} ⟶ C_L ⟶ 0`

(Milne, *Class Field Theory*, Lemma 4.2), the input of the Herbrand-quotient assembly
`NK.GlobalCFTdeep.herbrandEq_of_milneData`.

Concretely we build the two `Rep ℤ Gal(L/K)`-morphisms

* `tUnitsIncl T hT : tUnitsRep T hT ⟶ tIdelesRep T hT`, the inclusion `U(T) ↪ 𝕀_{L,T}` (which is
  `Idele.principalIdele` on the underlying units), and
* `tIdelesToClassGroup T hT : tIdelesRep T hT ⟶ IdeleClassGroup.rep K L`, the quotient map
  `𝕀_{L,T} ↠ C_L` (the restriction of `IdeleClassGroup.mk`),

prove `tUnitsIncl ≫ tIdelesToClassGroup = 0`, the injectivity of the first, the surjectivity of
the second (using `𝕀_L = Lˣ · 𝕀_{L,T}`), and exactness in the middle (an element of `𝕀_{L,T}` with
trivial class is a principal idèle, hence lies in `U(T)`), and feed the three into the elementwise
criterion `Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise`.

## Implementation notes

The Galois action on a `T`-stable subgroup `H ≤ 𝕀_L` is *not* an instance (stability is data), so
the actions on `TUnits T` and `TIdeles T` are the local instances `stableMulDistribMulAction`
built in `SIdeles.lean`; we reintroduce the very same local instances in the proofs below, so that
the `Rep`-computations (`Rep.ofMulDistribMulAction_ρ_apply_apply`) apply definitionally.

The elementwise criterion is used in place of the forgetful-functor recipe
`(forget₂ (Rep ℤ G) (ModuleCat ℤ)).reflects_exact_of_faithful`: at `k = ℤ` the `Module ℤ`-structure
of a `Rep ℤ G`-object is a diamond (see
`Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise`, which is proved
once over an arbitrary commutative ring for exactly this reason).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The underlying monoid homomorphism `U(T) → 𝕀_{L,T}`: the diagonal embedding `Lˣ ↪ 𝕀_L`
restricted to the `T`-units. -/
def tUnitsHom (T : Set (Place L)) : TUnits T →* TIdeles T where
  toFun a := ⟨Idele.principalIdele L (a : Lˣ), a.2⟩
  map_one' := Subtype.ext (map_one (Idele.principalIdele L))
  map_mul' a b := Subtype.ext (map_mul (Idele.principalIdele L) (a : Lˣ) (b : Lˣ))

/-- **The inclusion `U(T) ↪ 𝕀_{L,T}` of `ℤ[Gal(L/K)]`-modules.** -/
def tUnitsIncl (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) :
    tUnitsRep (K := K) (L := L) T hT ⟶ tIdelesRep (K := K) (L := L) T hT :=
  letI : MulDistribMulAction (L ≃ₐ[K] L) (TUnits T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (TUnits T) (fun σ x hx => smul_mem_TUnits hT hx)
  letI : MulDistribMulAction (L ≃ₐ[K] L) (TIdeles T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (TIdeles T) (fun σ x hx => smul_mem_TIdeles hT hx)
  Rep.ofHom
    { toFun := fun x => Additive.ofMul (tUnitsHom T (Additive.toMul x))
      map_add' := fun x y => by
        change Additive.ofMul (tUnitsHom T (Additive.toMul x * Additive.toMul y)) =
          Additive.ofMul (tUnitsHom T (Additive.toMul x) * tUnitsHom T (Additive.toMul y))
        rw [map_mul]
      map_smul' := fun n x => by
        change Additive.ofMul (tUnitsHom T ((Additive.toMul x) ^ n)) =
          n • Additive.ofMul (tUnitsHom T (Additive.toMul x))
        rw [map_zpow]
        rfl
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        apply Additive.ofMul.injective
        apply Subtype.ext
        show Idele.principalIdele L ((σ • Additive.toMul x : TUnits T) : Lˣ) =
          σ • Idele.principalIdele L ((Additive.toMul x : TUnits T) : Lˣ)
        rw [show ((σ • Additive.toMul x : TUnits T) : Lˣ) =
          Units.map σ.toMulEquiv.toMonoidHom ((Additive.toMul x : TUnits T) : Lˣ) from rfl]
        rw [Galois.globalCFT_smul_principalIdele] }

/-- **The quotient map `𝕀_{L,T} ↠ C_L` of `ℤ[Gal(L/K)]`-modules**, the restriction of the quotient
`𝕀_L ↠ C_L`. -/
def tIdelesToClassGroup (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) :
    tIdelesRep (K := K) (L := L) T hT ⟶ IdeleClassGroup.rep K L :=
  letI : MulDistribMulAction (L ≃ₐ[K] L) (TIdeles T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (TIdeles T) (fun σ x hx => smul_mem_TIdeles hT hx)
  letI : MulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup L) := inferInstance
  Rep.ofHom
    { toFun := fun x =>
        Additive.ofMul (IdeleClassGroup.mk L ((Additive.toMul x : TIdeles T) : Idele L))
      map_add' := fun x y => by
        change Additive.ofMul (IdeleClassGroup.mk L ((Additive.toMul x : TIdeles T) *
            (Additive.toMul y : TIdeles T) : Idele L)) =
          Additive.ofMul (IdeleClassGroup.mk L ((Additive.toMul x : TIdeles T) : Idele L) *
            IdeleClassGroup.mk L ((Additive.toMul y : TIdeles T) : Idele L))
        rw [map_mul]
      map_smul' := fun n x => by
        change Additive.ofMul (IdeleClassGroup.mk L
          (((Additive.toMul x : TIdeles T) : Idele L) ^ n)) =
          n • Additive.ofMul (IdeleClassGroup.mk L ((Additive.toMul x : TIdeles T) : Idele L))
        rw [map_zpow]
        rfl
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        apply Additive.ofMul.injective
        show IdeleClassGroup.mk L (((σ • Additive.toMul x : TIdeles T) : TIdeles T) : Idele L) =
          σ • IdeleClassGroup.mk L ((Additive.toMul x : TIdeles T) : Idele L)
        rw [show (((σ • Additive.toMul x : TIdeles T) : TIdeles T) : Idele L) =
          σ • ((Additive.toMul x : TIdeles T) : Idele L) from rfl]
        rw [IdeleClassGroup.smul_mk] }

/-- **The composite `U(T) → 𝕀_{L,T} → C_L` is zero**: a principal idèle is trivial in `C_L`. -/
theorem tUnitsIncl_comp_tIdelesToClassGroup (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) :
    tUnitsIncl (K := K) (L := L) T hT ≫ tIdelesToClassGroup (K := K) (L := L) T hT = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  show Additive.ofMul (IdeleClassGroup.mk L
    ((tUnitsHom T (Additive.toMul x) : TIdeles T) : Idele L)) = 0
  rw [show IdeleClassGroup.mk L
      ((tUnitsHom T (Additive.toMul x) : TIdeles T) : Idele L) = 1 from
    (QuotientGroup.eq_one_iff _).mpr
      ⟨((Additive.toMul x : TUnits T) : Lˣ), rfl⟩]
  rfl

/-- **The inclusion `U(T) ↪ 𝕀_{L,T}` is injective**: the principal idèle attached to a unit
determines that unit. -/
theorem tUnitsIncl_injective (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) :
    Function.Injective ⇑(Rep.Hom.hom (tUnitsIncl (K := K) (L := L) T hT)) := by
  intro x y hxy
  have h2 : tUnitsHom T (Additive.toMul x) = tUnitsHom T (Additive.toMul y) :=
    Additive.ofMul.injective hxy
  have h3 := congrArg Subtype.val h2
  have h4 : ((Additive.toMul x : TUnits T) : Lˣ) = ((Additive.toMul y : TUnits T) : Lˣ) :=
    Ideles.globalCFT_principalIdele_injective h3
  exact Additive.ext (Subtype.ext h4)

/-- **The quotient map `𝕀_{L,T} ↠ C_L` is surjective** as soon as `𝕀_L = Lˣ · 𝕀_{L,T}`: every
idèle class is represented by a `T`-idèle. -/
theorem tIdelesToClassGroup_surjective (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (h : (⊤ : Subgroup (Idele L)) = Idele.principalSubgroup L ⊔ TIdeles T) :
    Function.Surjective ⇑(Rep.Hom.hom (tIdelesToClassGroup (K := K) (L := L) T hT)) := by
  intro q
  obtain ⟨y, hy⟩ := IdeleClassGroup.mk_surjective L (Additive.toMul q)
  have hyT : y ∈ (⊤ : Subgroup (Idele L)) := trivial
  rw [h] at hyT
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hyT
  refine ⟨Additive.ofMul ⟨b, hb⟩, ?_⟩
  have ha1 : IdeleClassGroup.mk L a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
  have hby : IdeleClassGroup.mk L y = IdeleClassGroup.mk L b := by
    rw [← hab, map_mul, ha1, one_mul]
  rw [show (tIdelesToClassGroup (K := K) (L := L) T hT).hom (Additive.ofMul ⟨b, hb⟩) =
      Additive.ofMul (IdeleClassGroup.mk L b) from rfl, hby.symm.trans hy]
  rfl

/-- **Exactness in the middle**: a `T`-idèle whose class in `C_L` is trivial is a principal idèle,
whose unit is a `T`-unit; hence it lies in the image of `tUnitsIncl`. -/
theorem exists_tUnitsIncl_eq_of_tIdelesToClassGroup_eq_zero (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    {x : Additive (TIdeles T)}
    (hx : (tIdelesToClassGroup (K := K) (L := L) T hT).hom x = 0) :
    ∃ y : Additive (TUnits T), (tUnitsIncl (K := K) (L := L) T hT).hom y = x := by
  have hxw : Additive.ofMul
      (IdeleClassGroup.mk L ((Additive.toMul x : TIdeles T) : Idele L)) = 0 := hx
  have hx1 : IdeleClassGroup.mk L ((Additive.toMul x : TIdeles T) : Idele L) = 1 := by
    have h1 := congrArg Additive.toMul hxw
    exact h1
  obtain ⟨a, ha⟩ := Idele.mem_principalSubgroup.mp ((QuotientGroup.eq_one_iff _).mp hx1)
  have hmem : a ∈ TUnits T :=
    Subgroup.mem_comap.mpr (by rw [ha]; exact (Additive.toMul x : TIdeles T).2)
  refine ⟨Additive.ofMul ⟨a, hmem⟩, ?_⟩
  show Additive.ofMul (tUnitsHom T ⟨a, hmem⟩) = x
  change Additive.ofMul (tUnitsHom T ⟨a, hmem⟩) = Additive.ofMul (Additive.toMul x)
  apply Additive.ofMul.injective
  apply Subtype.ext
  exact ha

/-- **The equivariant second isomorphism theorem** (Milne, *Class Field Theory*, Lemma 4.2): for a
`Gal(L/K)`-stable set `T` of places of `L` with `𝕀_L = Lˣ · 𝕀_{L,T}`, the sequence
`0 → U(T) → 𝕀_{L,T} → C_L → 0` is a short exact sequence of `ℤ[Gal(L/K)]`-modules, i.e.
`NK.GlobalCFTdeep.MilneFourTwoExact T hT h` is inhabited. -/
theorem milneFourTwoExact_nonempty {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (T : Set (NK.GlobalCFT.Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (h : (⊤ : Subgroup (NK.GlobalCFT.Idele L)) =
      NK.GlobalCFT.Idele.principalSubgroup L ⊔ NK.GlobalCFTdeep.TIdeles T) :
    Nonempty (NK.GlobalCFTdeep.MilneFourTwoExact T hT h) := by
  refine ⟨tUnitsIncl (K := K) (L := L) T hT, tIdelesToClassGroup (K := K) (L := L) T hT,
    tUnitsIncl_comp_tIdelesToClassGroup (K := K) (L := L) T hT, ?_⟩
  exact Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise _
    ((Rep.mono_iff_injective _).2 (tUnitsIncl_injective (K := K) (L := L) T hT))
    ((Rep.epi_iff_surjective _).2 (tIdelesToClassGroup_surjective (K := K) (L := L) T hT h))
    (fun x hx => exists_tUnitsIncl_eq_of_tIdelesToClassGroup_eq_zero (K := K) (L := L) T hT hx)

end NK.GlobalCFTdeep.Herbrand
