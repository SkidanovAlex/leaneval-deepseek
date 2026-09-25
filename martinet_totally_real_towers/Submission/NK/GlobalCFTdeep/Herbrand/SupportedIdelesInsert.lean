/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.Fiber
import Submission.NK.GlobalCFTdeep.Herbrand.FiniteIndex
import Submission.NK.GlobalCFTdeep.Herbrand.fiberIdelesRep_iso_coind
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique

/-!
# Idèles supported on the places above `S ∪ {v₀}`

For a finite extension `L / K` of number fields and a place `v₀` of `K`, the idèles supported on
the places of `L` above `S ∪ {v₀}` decompose as the direct product of the idèles supported on the
places above `S` and the idèles supported on the fibre of `v₀`:

  `𝕀_{L,T'} = 𝕀_{L,T} × ∏_{w | v₀} L_wˣ`,   `T = {w | ∃ v ∈ S, w | v}`,
  `T' = {w | ∃ v ∈ S ∪ {v₀}, w | v}`.

This file builds the corresponding **short exact sequence** of `ℤ[Gal(L/K)]`-modules

  `0 ⟶ 𝕀_{L,T} ⟶ 𝕀_{L,T'} ⟶ ∏_{w | v₀} L_wˣ ⟶ 0`

(the inclusion, and the projection that puts `1` at the places of `T`), proves it short exact
with the elementwise criterion `shortExact_of_mono_epi_elementwise`, and records the resulting
decomposition of the `ℤ[Gal(L/K)]`-module `𝕀_{L,T'}` up to the short exact sequence
(`supportedIdelesSES`).  The Herbrand-quotient consequence, namely that the Herbrand quotient
of `𝕀_{L,T'}` is the product of those of `𝕀_{L,T}` and of the fibre, is the content of
`herbrandEq_supportedIdeles_of_insert` in `Herbrand/herbrandEq_supportedIdeles_of_insert.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-! ## The projection onto the places outside `T` -/

/-- The underlying function of the idèle `supportedProj T x`. -/
def supportedProjFun (T : Set (Place L)) (x : Idele L) :
    ∀ w : Place L, (Place.localField L w)ˣ := by
  intro w
  classical
  exact if w ∈ T then 1 else x w

/-- **The idèle obtained from `x` by putting `1` at every place of `T`.**  The values outside `T`
are those of `x`, so this is again an idèle: the restricted-product condition is inherited
from `x`. -/
def supportedProj (T : Set (Place L)) (x : Idele L) : Idele L := by
  classical
  refine ⟨supportedProjFun T x, ?_⟩
  rw [Filter.eventually_cofinite]
  refine (Filter.eventually_cofinite.mp x.2).subset ?_
  intro w hw
  rw [Set.mem_ofPred_eq] at hw
  by_cases h : w ∈ T
  · rw [show supportedProjFun T x w = 1 from if_pos h] at hw
    exact absurd (one_mem (Place.localUnits L w)) hw
  · rwa [show supportedProjFun T x w = x w from if_neg h] at hw

theorem supportedProj_apply_of_mem {T : Set (Place L)} {w : Place L} (h : w ∈ T) (x : Idele L) :
    supportedProj T x w = 1 := by
  classical
  change supportedProjFun T x w = 1
  exact if_pos h

theorem supportedProj_apply_of_notMem {T : Set (Place L)} {w : Place L} (h : w ∉ T)
    (x : Idele L) : supportedProj T x w = x w := by
  classical
  change supportedProjFun T x w = x w
  exact if_neg h

/-- `supportedProj` is a monoid homomorphism: it is the identity outside `T` and sends everything
in `T` to `1`. -/
def supportedProjHom (T : Set (Place L)) : Idele L →* Idele L where
  toFun := supportedProj T
  map_one' := by
    classical
    ext w
    by_cases h : w ∈ T
    · simp only [supportedProj_apply_of_mem h, Idele.one_apply]
    · simp only [supportedProj_apply_of_notMem h, Idele.one_apply]
  map_mul' := by
    classical
    intro x y
    ext w
    by_cases h : w ∈ T
    · simp only [supportedProj_apply_of_mem h, Idele.mul_apply, one_mul]
    · simp only [supportedProj_apply_of_notMem h, Idele.mul_apply]

theorem supportedProjHom_apply (T : Set (Place L)) (x : Idele L) :
    supportedProjHom T x = supportedProj T x := rfl

theorem supportedProj_eq_one_of_mem {T : Set (Place L)} {x : Idele L}
    (hx : x ∈ supportedIdeles (L := L) T) : supportedProj T x = 1 := by
  classical
  ext w
  by_cases h : w ∈ T
  · rw [supportedProj_apply_of_mem h, Idele.one_apply]
  · rw [supportedProj_apply_of_notMem h, Idele.one_apply]
    simpa using (mem_supportedIdeles.mp hx) w h

/-- The places of `T` are permuted by `Gal(L/K)`; in particular membership in `T` is invariant
under the action. -/
theorem mem_smul_iff_of_stable {T : Set (Place L)}
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) (σ : L ≃ₐ[K] L) (w : Place L) :
    σ • w ∈ T ↔ w ∈ T := by
  constructor
  · intro h
    have h' : σ⁻¹ • (σ • w) ∈ T := @hT σ⁻¹ (σ • w) h
    rwa [inv_smul_smul] at h'
  · exact fun h => hT σ h

/-- `supportedProj` is equivariant for the action of `Gal(L/K)` on the idèles when `T` is
`Gal(L/K)`-stable. -/
theorem supportedProj_smul {T : Set (Place L)}
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) (σ : L ≃ₐ[K] L) (x : Idele L) :
    supportedProj T (σ • x) = σ • supportedProj T x := by
  classical
  ext w
  rw [Idele.smul_apply]
  by_cases h : w ∈ T
  · rw [supportedProj_apply_of_mem h,
      supportedProj_apply_of_mem ((mem_smul_iff_of_stable hT σ⁻¹ w).mpr h)]
    simp
  · rw [supportedProj_apply_of_notMem h,
      supportedProj_apply_of_notMem (fun hh => h ((mem_smul_iff_of_stable hT σ⁻¹ w).mp hh))]
    rw [Idele.smul_apply]

/-- Monotonicity of `supportedIdeles` in the support. -/
theorem supportedIdeles_mono {T T' : Set (Place L)} (h : T ⊆ T') :
    supportedIdeles (L := L) T ≤ supportedIdeles (L := L) T' :=
  fun x hx w hw => hx w (fun hwT => hw (h hwT))

/-! ## The projection of the idèles supported on `T'` onto the fibre of `v₀` -/

/-- The projection of an idèle supported on `T'` to the fibre of `v₀` lands in the idèles
supported on the fibre. -/
theorem supportedProj_mem_fiberIdeles {T T' : Set (Place L)} {v₀ : Place K}
    (hdisj : ∀ w, w ∈ T → ¬ Place.LiesOver w v₀)
    (hcomp : ∀ w, w ∈ T' → w ∈ T ∨ Place.LiesOver w v₀)
    {x : Idele L} (hx : x ∈ supportedIdeles (L := L) T') :
    supportedProj T x ∈ fiberIdeles (K := K) (L := L) v₀ := by
  intro w hw
  by_cases h : w ∈ T
  · rw [supportedProj_apply_of_mem h]
  · rw [supportedProj_apply_of_notMem h]
    have hwT' : w ∉ T' := by
      intro h'
      rcases hcomp w h' with h2 | h2
      · exact h h2
      · exact hw h2
    exact (mem_supportedIdeles.mp hx) w hwT'

/-- The projection onto the fibre of `v₀`, as a homomorphism of groups. -/
def supportedToFiberHom (T T' : Set (Place L)) (v₀ : Place K)
    (hdisj : ∀ w, w ∈ T → ¬ Place.LiesOver w v₀)
    (hcomp : ∀ w, w ∈ T' → w ∈ T ∨ Place.LiesOver w v₀) :
    supportedIdeles (L := L) T' →* fiberIdeles (K := K) (L := L) v₀ where
  toFun x := ⟨supportedProjHom T (x : Idele L),
    supportedProj_mem_fiberIdeles hdisj hcomp x.2⟩
  map_one' := Subtype.ext (map_one (supportedProjHom T))
  map_mul' := fun x y =>
    Subtype.ext (map_mul (supportedProjHom T) (x : Idele L) (y : Idele L))

/-! ## The two morphisms of `ℤ[Gal(L/K)]`-modules -/

/-- **The inclusion `𝕀_{L,T} ⟶ 𝕀_{L,T'}`** of `ℤ[Gal(L/K)]`-modules, for `T ⊆ T'`. -/
def supportedIdelesInclRep (T T' : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hT' : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T' → σ • w ∈ T')
    (hsub : T ⊆ T') :
    supportedIdelesRep (L := L) T hT ⟶ supportedIdelesRep (L := L) T' hT' :=
  letI : MulDistribMulAction (L ≃ₐ[K] L) (supportedIdeles (L := L) T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (supportedIdeles (L := L) T)
      (fun σ x hx => smul_mem_supportedIdeles hT hx)
  letI : MulDistribMulAction (L ≃ₐ[K] L) (supportedIdeles (L := L) T') :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (supportedIdeles (L := L) T')
      (fun σ x hx => smul_mem_supportedIdeles hT' hx)
  Rep.ofHom
    { toFun := fun x => Additive.ofMul (Subgroup.inclusion (supportedIdeles_mono hsub) (Additive.toMul x))
      map_add' := by
        intro x y
        change Additive.ofMul (Subgroup.inclusion (supportedIdeles_mono hsub)
            (Additive.toMul x * Additive.toMul y)) =
          Additive.ofMul (Subgroup.inclusion (supportedIdeles_mono hsub) (Additive.toMul x)) +
            Additive.ofMul (Subgroup.inclusion (supportedIdeles_mono hsub) (Additive.toMul y))
        rw [map_mul]
        rfl
      map_smul' := by
        intro n x
        change Additive.ofMul (Subgroup.inclusion (supportedIdeles_mono hsub) ((Additive.toMul x) ^ n)) =
          n • Additive.ofMul (Subgroup.inclusion (supportedIdeles_mono hsub) (Additive.toMul x))
        rw [map_zpow]
        rfl
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        apply Additive.ofMul.injective
        apply Subtype.ext
        rfl }

/-- **The projection `𝕀_{L,T'} ⟶ ∏_{w | v₀} L_wˣ`** of `ℤ[Gal(L/K)]`-modules: an idèle supported
on `T'` is sent to the idèle which keeps its components over `v₀` and is `1` at the places of
`T`. -/
def supportedToFiberRep (T T' : Set (Place L)) (v₀ : Place K)
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hT' : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T' → σ • w ∈ T')
    (hdisj : ∀ w, w ∈ T → ¬ Place.LiesOver w v₀)
    (hcomp : ∀ w, w ∈ T' → w ∈ T ∨ Place.LiesOver w v₀) :
    supportedIdelesRep (L := L) T' hT' ⟶ fiberIdelesRep (K := K) (L := L) v₀ :=
  letI : MulDistribMulAction (L ≃ₐ[K] L) (supportedIdeles (L := L) T') :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (supportedIdeles (L := L) T')
      (fun σ x hx => smul_mem_supportedIdeles hT' hx)
  Rep.ofHom
    { toFun := fun x => Additive.ofMul
        (supportedToFiberHom T T' v₀ hdisj hcomp (Additive.toMul x))
      map_add' := by
        intro x y
        change Additive.ofMul (supportedToFiberHom T T' v₀ hdisj hcomp
            (Additive.toMul x * Additive.toMul y)) =
          Additive.ofMul (supportedToFiberHom T T' v₀ hdisj hcomp (Additive.toMul x)) +
            Additive.ofMul (supportedToFiberHom T T' v₀ hdisj hcomp (Additive.toMul y))
        rw [map_mul]
        rfl
      map_smul' := by
        intro n x
        change Additive.ofMul (supportedToFiberHom T T' v₀ hdisj hcomp
            ((Additive.toMul x) ^ n)) =
          n • Additive.ofMul (supportedToFiberHom T T' v₀ hdisj hcomp (Additive.toMul x))
        rw [map_zpow]
        rfl
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        apply Additive.ofMul.injective
        apply Subtype.ext
        exact supportedProj_smul hT σ ((Additive.toMul x : supportedIdeles (L := L) T') : Idele L) }

/-! ## Short exactness -/

/-- The composite `𝕀_{L,T} ⟶ 𝕀_{L,T'} ⟶ ∏_{w | v₀} L_wˣ` is zero. -/
theorem supportedIdelesIncl_comp_supportedToFiber (T T' : Set (Place L)) (v₀ : Place K)
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hT' : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T' → σ • w ∈ T')
    (hsub : T ⊆ T')
    (hdisj : ∀ w, w ∈ T → ¬ Place.LiesOver w v₀)
    (hcomp : ∀ w, w ∈ T' → w ∈ T ∨ Place.LiesOver w v₀) :
    supportedIdelesInclRep T T' hT hT' hsub ≫
      supportedToFiberRep T T' v₀ hT hT' hdisj hcomp = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Additive.ofMul.injective
  apply Subtype.ext
  show supportedProj T ((Additive.toMul x : supportedIdeles (L := L) T) : Idele L) = 1
  exact supportedProj_eq_one_of_mem (Additive.toMul x).2




/-! ## Injectivity, surjectivity and exactness of the decomposition sequence -/

/-- The inclusion `𝕀_{L,T} ⟶ 𝕀_{L,T'}` is injective. -/
theorem supportedIdelesInclRep_injective (T T' : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hT' : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T' → σ • w ∈ T')
    (hsub : T ⊆ T') :
    Function.Injective ⇑(Rep.Hom.hom (supportedIdelesInclRep T T' hT hT' hsub)) := by
  intro x y hxy
  have hxy' : Additive.ofMul (Subgroup.inclusion (supportedIdeles_mono hsub)
        (Additive.toMul x)) =
      Additive.ofMul (Subgroup.inclusion (supportedIdeles_mono hsub) (Additive.toMul y)) := hxy
  have h2 : Subgroup.inclusion (supportedIdeles_mono hsub) (Additive.toMul x) =
      Subgroup.inclusion (supportedIdeles_mono hsub) (Additive.toMul y) :=
    Additive.ofMul.injective hxy'
  have h3 : ((Additive.toMul x : supportedIdeles (L := L) T) : Idele L) =
      ((Additive.toMul y : supportedIdeles (L := L) T) : Idele L) :=
    congrArg (fun q : supportedIdeles (L := L) T' => (q : Idele L)) h2
  exact Additive.toMul.injective (Subtype.ext h3)

/-- The projection `𝕀_{L,T'} ⟶ ∏_{w | v₀} L_wˣ` is surjective, because an idèle supported on the
fibre of `v₀` is a `T'`-idèle and is fixed by the projection. -/
theorem supportedToFiberRep_surjective (T T' : Set (Place L)) (v₀ : Place K)
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hT' : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T' → σ • w ∈ T')
    (hdisj : ∀ w, w ∈ T → ¬ Place.LiesOver w v₀)
    (hcomp : ∀ w, w ∈ T' → w ∈ T ∨ Place.LiesOver w v₀)
    (hfiberT' : ∀ w, Place.LiesOver w v₀ → w ∈ T') :
    Function.Surjective ⇑(Rep.Hom.hom (supportedToFiberRep T T' v₀ hT hT' hdisj hcomp)) := by
  classical
  intro z
  set zz : Additive (fiberIdeles (K := K) (L := L) v₀) := z with hzz
  have hzmem : fiberToIdele (K := K) (L := L) v₀ zz ∈ supportedIdeles (L := L) T' := by
    intro w hw
    by_contra h
    refine hw (hfiberT' w ?_)
    by_contra hh
    exact h ((mem_fiberIdeles.mp (Additive.toMul zz).2) w hh)
  refine ⟨Additive.ofMul ⟨fiberToIdele (K := K) (L := L) v₀ zz, hzmem⟩, ?_⟩
  apply Additive.ofMul.injective
  apply Subtype.ext
  show supportedProjHom T (fiberToIdele (K := K) (L := L) v₀ zz) =
    fiberToIdele (K := K) (L := L) v₀ zz
  refine Idele.ext fun w => ?_
  by_cases h : w ∈ T
  · rw [supportedProjHom_apply, supportedProj_apply_of_mem h]
    simpa only [fiberToIdele] using
      ((mem_fiberIdeles.mp (Additive.toMul zz).2) w (hdisj w h)).symm
  · rw [supportedProjHom_apply, supportedProj_apply_of_notMem h]

/-- **Exactness in the middle**: a `T'`-idèle which is trivial at the places above `v₀` is a
`T`-idèle. -/
theorem supportedIdeles_exact (T T' : Set (Place L)) (v₀ : Place K)
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hT' : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T' → σ • w ∈ T')
    (hsub : T ⊆ T')
    (hdisj : ∀ w, w ∈ T → ¬ Place.LiesOver w v₀)
    (hcomp : ∀ w, w ∈ T' → w ∈ T ∨ Place.LiesOver w v₀)
    {x : (supportedIdelesRep (L := L) T' hT').V}
    (hx : (supportedToFiberRep T T' v₀ hT hT' hdisj hcomp).hom x = 0) :
    ∃ y : (supportedIdelesRep (L := L) T hT).V,
      (supportedIdelesInclRep T T' hT hT' hsub).hom y = x := by
  classical
  have h1 : supportedToFiberHom T T' v₀ hdisj hcomp (Additive.toMul x) = 1 := by
    have h2 : Additive.ofMul (supportedToFiberHom T T' v₀ hdisj hcomp (Additive.toMul x)) =
        (0 : Additive (fiberIdeles (K := K) (L := L) v₀)) := hx
    exact Additive.ofMul.injective (by simpa using h2)
  have hx' : supportedProj T ((Additive.toMul x : supportedIdeles (L := L) T') : Idele L) = 1 := by
    have h3 : ((supportedToFiberHom T T' v₀ hdisj hcomp (Additive.toMul x) :
        fiberIdeles (K := K) (L := L) v₀) : Idele L) = 1 := by
      rw [h1]
      rfl
    exact h3
  refine ⟨Additive.ofMul ⟨((Additive.toMul x : supportedIdeles (L := L) T') : Idele L), ?_⟩,
    ?_⟩
  · intro w hw
    have h := congrArg (fun f : Idele L => f w) hx'
    rw [supportedProj_apply_of_notMem hw] at h
    exact h
  · apply Additive.ofMul.injective
    apply Subtype.ext
    rfl

/-- **The short exact sequence** `0 ⟶ 𝕀_{L,T} ⟶ 𝕀_{L,T'} ⟶ ∏_{w | v₀} L_wˣ ⟶ 0` of
`ℤ[Gal(L/K)]`-modules. -/
abbrev supportedIdelesSES (T T' : Set (Place L)) (v₀ : Place K)
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hT' : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T' → σ • w ∈ T')
    (hsub : T ⊆ T')
    (hdisj : ∀ w, w ∈ T → ¬ Place.LiesOver w v₀)
    (hcomp : ∀ w, w ∈ T' → w ∈ T ∨ Place.LiesOver w v₀) :
    ShortComplex (Rep ℤ (L ≃ₐ[K] L)) where
  X₁ := supportedIdelesRep (L := L) T hT
  X₂ := supportedIdelesRep (L := L) T' hT'
  X₃ := fiberIdelesRep (K := K) (L := L) v₀
  f := supportedIdelesInclRep T T' hT hT' hsub
  g := supportedToFiberRep T T' v₀ hT hT' hdisj hcomp
  zero := supportedIdelesIncl_comp_supportedToFiber T T' v₀ hT hT' hsub hdisj hcomp

theorem supportedIdelesSES_shortExact (T T' : Set (Place L)) (v₀ : Place K)
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hT' : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T' → σ • w ∈ T')
    (hsub : T ⊆ T')
    (hdisj : ∀ w, w ∈ T → ¬ Place.LiesOver w v₀)
    (hcomp : ∀ w, w ∈ T' → w ∈ T ∨ Place.LiesOver w v₀)
    (hfiberT' : ∀ w, Place.LiesOver w v₀ → w ∈ T') :
    (supportedIdelesSES T T' v₀ hT hT' hsub hdisj hcomp).ShortExact :=
  Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise _
    ((Rep.mono_iff_injective _).2 (supportedIdelesInclRep_injective T T' hT hT' hsub))
    ((Rep.epi_iff_surjective _).2
      (supportedToFiberRep_surjective T T' v₀ hT hT' hdisj hcomp hfiberT'))
    (fun x hx => supportedIdeles_exact T T' v₀ hT hT' hsub hdisj hcomp hx)

/-- **Multiplicativity of the Herbrand quotient over the decomposition
`𝕀_{L,T'} = 𝕀_{L,T} · ∏_{w | v₀} L_wˣ`.**  If the Herbrand quotient of the idèles supported on
`T` is `m` and that of the fibre of `v₀` is `n`, then the Herbrand quotient of the idèles
supported on `T'` is `m · n`. -/
theorem herbrandEq_supportedIdeles_of_shortExact {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [Fintype (L ≃ₐ[K] L)]
    [IsCyclic (L ≃ₐ[K] L)] (T T' : Set (Place L)) (v₀ : Place K)
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hT' : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T' → σ • w ∈ T')
    (hsub : T ⊆ T')
    (hdisj : ∀ w, w ∈ T → ¬ Place.LiesOver w v₀)
    (hcomp : ∀ w, w ∈ T' → w ∈ T ∨ Place.LiesOver w v₀)
    (hfiberT' : ∀ w, Place.LiesOver w v₀ → w ∈ T')
    (n m : ℕ)
    (hfib : HerbrandEq (fiberIdelesRep (K := K) (L := L) v₀) n)
    (hT_herb : HerbrandEq (supportedIdelesRep (L := L) T hT) m)
    (hf1 : FiniteTate (fiberIdelesRep (K := K) (L := L) v₀))
    (hf2 : FiniteTate (supportedIdelesRep (L := L) T hT))
    (hf3 : FiniteTate (supportedIdelesRep (L := L) T' hT')) :
    HerbrandEq (supportedIdelesRep (L := L) T' hT') (m * n) := by
  haveI h1z : Finite ↥(tateCohomology ((supportedIdelesSES T T' v₀ hT hT' hsub hdisj hcomp).X₁) 0) :=
    hf2.zero
  haveI h1o : Finite ↥(tateCohomology ((supportedIdelesSES T T' v₀ hT hT' hsub hdisj hcomp).X₁) 1) :=
    hf2.one
  haveI h2z : Finite ↥(tateCohomology ((supportedIdelesSES T T' v₀ hT hT' hsub hdisj hcomp).X₂) 0) :=
    hf3.zero
  haveI h2o : Finite ↥(tateCohomology ((supportedIdelesSES T T' v₀ hT hT' hsub hdisj hcomp).X₂) 1) :=
    hf3.one
  haveI h3z : Finite ↥(tateCohomology ((supportedIdelesSES T T' v₀ hT hT' hsub hdisj hcomp).X₃) 0) :=
    hf1.zero
  haveI h3o : Finite ↥(tateCohomology ((supportedIdelesSES T T' v₀ hT hT' hsub hdisj hcomp).X₃) 1) :=
    hf1.one
  exact herbrandEq_of_shortExact (supportedIdelesSES T T' v₀ hT hT' hsub hdisj hcomp)
    (supportedIdelesSES_shortExact T T' v₀ hT hT' hsub hdisj hcomp hfiberT') m n hT_herb hfib

end NK.GlobalCFTdeep.Herbrand
