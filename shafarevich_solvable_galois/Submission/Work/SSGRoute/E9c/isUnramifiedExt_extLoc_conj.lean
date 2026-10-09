import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.e9c_localUnits_conj
import Submission.Work.SSGRoute.e9c_extLoc_conj_zero
import Submission.Work.SSGRoute.E7cOmega.extLoc_conj_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.SSGRoute.E9c

open CategoryTheory SSGRoute.PTExt
open NK.GlobalCFT (Idele Place IdeleClassGroup)

/-- The integral local units `𝒪_wˣ` as a `Coeff`-representation, with the coefficient universe
pinned (the bare `NK.HassePrinciple.localUnitsSubRep` leaves it free). -/
noncomputable abbrev localUnitsSubConjP (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : Place K) :
    Rep.{0, 0, 0} SSGRoute.PTExt.Coeff (decompK (k := k) w) :=
  NK.HassePrinciple.localUnitsSubRep k K w

/-- The inclusion `𝒪_wˣ ↪ K_wˣ`, with the coefficient universe pinned. -/
noncomputable abbrev localUnitsInclConjP (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : Place K) :
    localUnitsSubConjP k K w ⟶ SSGRoute.PTExt.localUnitsK (k := k) (K := K) w :=
  NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w

/-! ## The integral units under conjugation -/

/-- **The conjugation isomorphism of local units carries the integral units into the integral
units.**  Let `σ : K ≃ₐ[k] K`, `v` a place of `K`, and `Θ : K_vˣ ⟶ res (conjStabHom σ v) K_{σ v}ˣ`
a morphism of `D_v`-modules whose underlying map on units is `actVal σ v`.  Then there is a morphism
`Θ' : 𝒪_vˣ ⟶ res (conjStabHom σ v) 𝒪_{σ v}ˣ` of `D_v`-modules whose underlying map is given by
`actVal σ v` (restricted along `Place.localRingEquiv_mem_localUnits`, a genuine iff), and the square
`incl_v ≫ Θ = Θ' ≫ resMap (conjStabHom σ v) (incl_{σ v})` commutes. -/
theorem exists_factor_localUnitsIncl_conj {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (σ : K ≃ₐ[k] K) (v : NK.GlobalCFT.Place K)
    (Θ : SSGRoute.PTExt.localUnitsK (k := k) (K := K) v ⟶
      Rep.res (conjStabHom k K σ v) (SSGRoute.PTExt.localUnitsK (k := k) (K := K) (σ • v)))
    (hΘ : ∀ u : (Place.localField K v)ˣ,
      (Additive.toMul (Θ (Additive.ofMul u)) : (Place.localField K (σ • v))ˣ)
        = NK.HassePrinciple.actVal σ v u) :
    ∃ Θ' : NK.HassePrinciple.localUnitsSubRep k K v ⟶
        Rep.res (conjStabHom k K σ v) (NK.HassePrinciple.localUnitsSubRep k K (σ • v)),
      (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) v) ≫ Θ
        = Θ' ≫ Rep.resMap (conjStabHom k K σ v)
            (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) (σ • v)) := by
  classical
  -- the pointwise formula for the composite `incl_v ≫ Θ`
  have hψ : ∀ u : ↥(Place.localUnits K v),
      ((localUnitsInclConjP k K v) ≫ Θ).hom (Additive.ofMul u)
        = Additive.ofMul (NK.HassePrinciple.actVal σ v (u : (Place.localField K v)ˣ)) := by
    intro u
    rw [Rep.comp_apply]
    exact hΘ (u : (Place.localField K v)ˣ)
  -- the would-be restriction of `Θ` to the integral units
  let gfun : Additive ↥(Place.localUnits K v) → Additive ↥(Place.localUnits K (σ • v)) :=
    fun a => Additive.ofMul ⟨NK.HassePrinciple.actVal σ v (Additive.toMul a).1,
      (NK.HassePrinciple.actVal_mem_localUnits_iff σ v (Additive.toMul a).1).mp
        (Additive.toMul a).2⟩
  have hgf : ∀ a : Additive ↥(Place.localUnits K v),
      (Rep.resMap (conjStabHom k K σ v)
          (localUnitsInclConjP k K (σ • v))).hom (gfun a)
        = ((localUnitsInclConjP k K v) ≫ Θ).hom a := by
    intro a
    have h1 : ((localUnitsInclConjP k K v) ≫ Θ).hom a
        = Additive.ofMul (NK.HassePrinciple.actVal σ v (Additive.toMul a).1) := by
      rw [show a = Additive.ofMul (Additive.toMul a) from (ofMul_toMul a).symm]
      exact hψ (Additive.toMul a)
    have h2 : (Rep.resMap (conjStabHom k K σ v)
        (localUnitsInclConjP k K (σ • v))).hom (gfun a)
        = Additive.ofMul (NK.HassePrinciple.actVal σ v (Additive.toMul a).1) := by
      rw [Rep.resMap_hom_apply]
      rfl
    exact h2.trans h1.symm
  have hinj : ∀ {a b : Additive ↥(Place.localUnits K (σ • v))},
      (localUnitsInclConjP k K (σ • v)).hom a
        = (localUnitsInclConjP k K (σ • v)).hom b → a = b := by
    intro a b h
    apply Additive.toMul.injective
    apply Subtype.ext
    exact Additive.toMul.injective h
  have hinjR : ∀ {a b : Additive ↥(Place.localUnits K (σ • v))},
      (Rep.resMap (conjStabHom k K σ v)
          (localUnitsInclConjP k K (σ • v))).hom a
        = (Rep.resMap (conjStabHom k K σ v)
          (localUnitsInclConjP k K (σ • v))).hom b → a = b := by
    intro a b h
    rw [Rep.resMap_hom_apply] at h
    rw [Rep.resMap_hom_apply] at h
    exact hinj h
  have hadd : ∀ a b : Additive ↥(Place.localUnits K v), gfun (a + b) = gfun a + gfun b := by
    intro a b
    refine hinjR ?_
    calc (Rep.resMap (conjStabHom k K σ v)
            (localUnitsInclConjP k K (σ • v))).hom (gfun (a + b))
        = ((localUnitsInclConjP k K v) ≫ Θ).hom (a + b) := hgf (a + b)
      _ = ((localUnitsInclConjP k K v) ≫ Θ).hom a
            + ((localUnitsInclConjP k K v) ≫ Θ).hom b :=
          map_add _ a b
      _ = (Rep.resMap (conjStabHom k K σ v)
            (localUnitsInclConjP k K (σ • v))).hom (gfun a)
            + (Rep.resMap (conjStabHom k K σ v)
              (localUnitsInclConjP k K (σ • v))).hom (gfun b) := by
          rw [← hgf a, ← hgf b]
      _ = (Rep.resMap (conjStabHom k K σ v)
            (localUnitsInclConjP k K (σ • v))).hom
            (gfun a + gfun b) := (map_add _ _ _).symm
  have hsmul : ∀ (n : SSGRoute.PTExt.Coeff) (a : Additive ↥(Place.localUnits K v)),
      gfun (n • a) = n • gfun a := by
    intro n a
    refine hinjR ?_
    calc (Rep.resMap (conjStabHom k K σ v)
            (localUnitsInclConjP k K (σ • v))).hom (gfun (n • a))
        = ((localUnitsInclConjP k K v) ≫ Θ).hom (n • a) :=
          hgf (n • a)
      _ = n • ((localUnitsInclConjP k K v) ≫ Θ).hom a :=
          map_smul _ n a
      _ = n • (Rep.resMap (conjStabHom k K σ v)
            (localUnitsInclConjP k K (σ • v))).hom (gfun a) := by
          rw [← hgf a]
      _ = (Rep.resMap (conjStabHom k K σ v)
            (localUnitsInclConjP k K (σ • v))).hom
            (n • gfun a) := (map_smul _ n _).symm
  have hintw : ∀ (h : decompK (k := k) v) (a : Additive ↥(Place.localUnits K v)),
      gfun (((localUnitsSubConjP k K v).ρ h) a)
        = (((Rep.res (conjStabHom k K σ v) (localUnitsSubConjP k K (σ • v))).ρ h) (gfun a)) := by
    intro h a
    refine hinjR ?_
    calc (Rep.resMap (conjStabHom k K σ v)
            (localUnitsInclConjP k K (σ • v))).hom
            (gfun (((localUnitsSubConjP k K v).ρ h) a))
        = ((localUnitsInclConjP k K v) ≫ Θ).hom
            (((localUnitsSubConjP k K v).ρ h) a) :=
          hgf (((localUnitsSubConjP k K v).ρ h) a)
      _ = (Rep.res (conjStabHom k K σ v)
            (SSGRoute.PTExt.localUnitsK (k := k) (K := K) (σ • v))).ρ h
            (((localUnitsInclConjP k K v) ≫ Θ).hom a) :=
          Rep.hom_comm_apply
            ((localUnitsInclConjP k K v) ≫ Θ) h a
      _ = (Rep.res (conjStabHom k K σ v)
            (SSGRoute.PTExt.localUnitsK (k := k) (K := K) (σ • v))).ρ h
            ((Rep.resMap (conjStabHom k K σ v)
              (localUnitsInclConjP k K (σ • v))).hom (gfun a)) := by
          rw [hgf a]
      _ = (Rep.resMap (conjStabHom k K σ v)
            (localUnitsInclConjP k K (σ • v))).hom
            (((Rep.res (conjStabHom k K σ v) (localUnitsSubConjP k K (σ • v))).ρ h) (gfun a)) :=
          (Rep.hom_comm_apply (Rep.resMap (conjStabHom k K σ v)
            (localUnitsInclConjP k K (σ • v))) h (gfun a)).symm
  let Θ' : NK.HassePrinciple.localUnitsSubRep k K v ⟶
      Rep.res (conjStabHom k K σ v) (NK.HassePrinciple.localUnitsSubRep k K (σ • v)) :=
    Rep.ofHom
      { toFun := gfun
        map_add' := hadd
        map_smul' := hsmul
        isIntertwining' := fun h => LinearMap.ext (hintw h) }
  have hΘ'_hom : ∀ a, (Rep.Hom.hom Θ') a = gfun a := fun a => rfl
  refine ⟨Θ', ?_⟩
  apply Rep.hom_ext
  ext a
  change (Rep.Hom.hom ((localUnitsInclConjP k K v) ≫ Θ)) a
      = (Rep.Hom.hom (Θ' ≫ Rep.resMap (conjStabHom k K σ v)
          (localUnitsInclConjP k K (σ • v)))) a
  conv_rhs => rw [Rep.comp_apply]
  rw [hΘ'_hom a]
  exact (hgf a).symm

/-! ## The conjugation relation between the local components -/

/-- **The conjugation relation between the local components of a global class at conjugate
places.**  With `φ = resMap (decompK v).subtype ((conjTwistInv σ).app M)` one has
`extRes (conjStabHom σ v) (extLoc (σ • v) z) = (mk₀ φ).comp (extLoc v z ≫ mk₀ Θ)`. -/
theorem extRes_conjStab_extLoc {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (z : CategoryTheory.Abelian.Ext M (SSGRoute.PTExt.idelesK k K) r)
    (σ : K ≃ₐ[k] K) (v : NK.GlobalCFT.Place K)
    (Θ : SSGRoute.PTExt.localUnitsK (k := k) (K := K) v ⟶
      Rep.res (conjStabHom k K σ v) (SSGRoute.PTExt.localUnitsK (k := k) (K := K) (σ • v)))
    (hΘsq : CategoryTheory.CategoryStruct.comp
          (Rep.resMap (decompK (k := k) v).subtype
            ((conjTwist σ).app (idelesRepP k K)))
          (Rep.resMap (conjStabHom k K σ v) (NK.HassePrinciple.ideleToLocalUnits k K (σ • v)))
      = CategoryTheory.CategoryStruct.comp
          (NK.HassePrinciple.ideleToLocalUnits k K v) Θ) :
    SSGRoute.PTExt.extRes (conjStabHom k K σ v)
        (SSGRoute.PTExt.extLoc (k := k) (K := K) (σ • v) z)
      = (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
            ((conjTwistInv σ).app M))).comp
          ((SSGRoute.PTExt.extLoc (k := k) (K := K) v z).comp
            (CategoryTheory.Abelian.Ext.mk₀ Θ) (add_zero r)) (zero_add r) := by
  classical
  -- the commuting square of coefficient maps, transported to `Ext`
  have hBC : (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
        ((conjTwist σ).app (idelesRepP k K)))).comp
      (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (conjStabHom k K σ v)
        (NK.HassePrinciple.ideleToLocalUnits k K (σ • v)))) (zero_add 0)
      = (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.ideleToLocalUnits k K v)).comp
          (CategoryTheory.Abelian.Ext.mk₀ Θ) (zero_add 0) := by
    have h1 := CategoryTheory.Abelian.Ext.mk₀_comp_mk₀
      (Rep.resMap (decompK (k := k) v).subtype ((conjTwist σ).app (idelesRepP k K)))
      (Rep.resMap (conjStabHom k K σ v) (NK.HassePrinciple.ideleToLocalUnits k K (σ • v)))
    have h2 := CategoryTheory.Abelian.Ext.mk₀_comp_mk₀
      (NK.HassePrinciple.ideleToLocalUnits k K v) Θ
    rw [h1, h2, hΘsq]
  -- Step 1: the restriction of the `(σ • v)`-component to `D_v`
  have hstep1 : SSGRoute.PTExt.extRes (conjStabHom k K σ v)
        (SSGRoute.PTExt.extLoc (k := k) (K := K) (σ • v) z)
      = (SSGRoute.PTExt.extRes (decompK (k := k) v).subtype
            (SSGRoute.PTExt.extRes ((MulAut.conj σ).toMonoidHom) z)).comp
          (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (conjStabHom k K σ v)
            (NK.HassePrinciple.ideleToLocalUnits k K (σ • v)))) (add_zero r) := by
    rw [SSGRoute.PTExt.extLoc, extRes_comp_mk₀]
    rw [show SSGRoute.PTExt.extRes (conjStabHom k K σ v)
          (SSGRoute.PTExt.extRes (decompK (k := k) (σ • v)).subtype z)
        = SSGRoute.PTExt.extRes (decompK (k := k) v).subtype
            (SSGRoute.PTExt.extRes ((MulAut.conj σ).toMonoidHom) z)
        from (SylowDesc.extRes_comp_aux
            (decompK (k := k) (σ • v)).subtype (conjStabHom k K σ v) z).symm.trans
          (SylowDesc.extRes_comp_aux
            ((MulAut.conj σ).toMonoidHom) (decompK (k := k) v).subtype z)]
    try rfl
  -- Step 2: apply the conjugation twist to `z` and distribute `extRes`
  have hstep2 : SSGRoute.PTExt.extRes (decompK (k := k) v).subtype
        (SSGRoute.PTExt.extRes ((MulAut.conj σ).toMonoidHom) z)
      = (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
            ((conjTwistInv σ).app M))).comp
          ((SSGRoute.PTExt.extRes (decompK (k := k) v).subtype z).comp
            (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
              ((conjTwist σ).app (idelesRepP k K)))) (add_zero r))
          (zero_add r) := by
    rw [Work.SSGRoute.extRes_conjTwist (σ := σ) (x := z), extRes_mk₀_comp, extRes_comp_mk₀]
  -- Step 3: reassociate and use the commuting square
  calc SSGRoute.PTExt.extRes (conjStabHom k K σ v)
        (SSGRoute.PTExt.extLoc (k := k) (K := K) (σ • v) z)
      = (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
            ((conjTwistInv σ).app M))).comp
          ((SSGRoute.PTExt.extLoc (k := k) (K := K) v z).comp
            (CategoryTheory.Abelian.Ext.mk₀ Θ) (add_zero r)) (zero_add r) := by
        rw [hstep1, hstep2]
        rw [CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero
          (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
            ((conjTwistInv σ).app M)))
          ((SSGRoute.PTExt.extRes (decompK (k := k) v).subtype z).comp
            (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
              ((conjTwist σ).app (idelesRepP k K)))) (add_zero r))
          (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (conjStabHom k K σ v)
            (NK.HassePrinciple.ideleToLocalUnits k K (σ • v)))) (zero_add r)]
        rw [CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero
          (SSGRoute.PTExt.extRes (decompK (k := k) v).subtype z)
          (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
            ((conjTwist σ).app (idelesRepP k K))))
          (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (conjStabHom k K σ v)
            (NK.HassePrinciple.ideleToLocalUnits k K (σ • v)))) (add_zero r)]
        rw [hBC]
        rw [(CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero
          (SSGRoute.PTExt.extRes (decompK (k := k) v).subtype z)
          (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.ideleToLocalUnits k K v))
          (CategoryTheory.Abelian.Ext.mk₀ Θ) (add_zero r)).symm]
        rfl

/-! ## The main theorem -/

/-- **Unramifiedness of the local component of a global class is invariant under conjugation of
the place.**  If `z ∈ Ext¹_{Gal(K/k)}(M, 𝕀_K)` localises at the place `v` of `K` to an unramified class
(one coming from the integral units `𝒪_vˣ`), then its localisation at `σ • v` is unramified.

This is the `isUnramifiedExt` companion of `Work.SSGRoute.e9c_extLoc_conj_zero` (the vanishing form),
which proves `extLoc v z = 0 → extLoc (σ • v) z = 0` by showing that `extRes (conjStabHom σ v) (extLoc (σ • v) z)`
is the conjugation twist of `extLoc v z`.  Here one needs in addition that the conjugation isomorphism
`Θ : K_vˣ ⟶ K_{σ v}ˣ` of `e9c_localUnits_conj` carries the integral units `𝒪_vˣ` into `𝒪_{σ v}ˣ`
(a factorisation `incl_v ≫ Θ = Θ' ≫ incl_{σ v}`, obtained from `Place.localRingEquiv_mem_localUnits`
— this is a genuine *iff*, so it is a bijection of unit groups), so that a factorisation of `extLoc v z`
through `localUnitsIncl v` transports to one of `extRes (conjStabHom σ v) (extLoc (σ • v) z)` through
`resMap (conjStabHom σ v) (localUnitsIncl (σ v))`; `extRes_injective_of_mulEquiv (conjStabEquiv σ v)`
then descends this to `extLoc (σ • v) z`.  (Archimedean places are harmless: the integral-unit
inclusion is an isomorphism there.) -/
theorem isUnramifiedExt_extLoc_conj {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (z : CategoryTheory.Abelian.Ext M (SSGRoute.PTExt.idelesK k K) r)
    (v : NK.GlobalCFT.Place K) (σ : K ≃ₐ[k] K)
    (hz : SSGRoute.PTExt.IsUnramifiedExt (k := k) (K := K) v
      (SSGRoute.PTExt.extLoc (k := k) (K := K) v z)) :
    SSGRoute.PTExt.IsUnramifiedExt (k := k) (K := K) (σ • v)
      (SSGRoute.PTExt.extLoc (k := k) (K := K) (σ • v) z) := by
  classical
  -- the conjugation isomorphism of local units, and its restriction to the integral units
  obtain ⟨Θ, hΘu, hΘsq⟩ := e9c_localUnits_conj (k := k) (K := K) σ v
  obtain ⟨Θ', hΘ'fac⟩ := exists_factor_localUnitsIncl_conj (k := k) (K := K) σ v Θ hΘu
  -- the local unramifiedness hypothesis, unfolded
  obtain ⟨z', hz'⟩ := hz
  -- the chain identity relating the two local components
  have hchain := extRes_conjStab_extLoc (k := k) (K := K) z σ v Θ hΘsq
  -- reassociation of the `Ext`-products through the factorisation of `extLoc v z`
  have hKEY : (z'.comp (CategoryTheory.Abelian.Ext.mk₀
          (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) v)) (add_zero r)).comp
        (CategoryTheory.Abelian.Ext.mk₀ Θ) (add_zero r)
      = (z'.comp (CategoryTheory.Abelian.Ext.mk₀ Θ') (add_zero r)).comp
        (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (conjStabHom k K σ v)
          (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) (σ • v)))) (add_zero r) := by
    calc (z'.comp (CategoryTheory.Abelian.Ext.mk₀
            (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) v)) (add_zero r)).comp
          (CategoryTheory.Abelian.Ext.mk₀ Θ) (add_zero r)
        = z'.comp ((CategoryTheory.Abelian.Ext.mk₀
              (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) v)).comp
            (CategoryTheory.Abelian.Ext.mk₀ Θ) (zero_add 0)) (add_zero r) :=
          CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero z'
            (CategoryTheory.Abelian.Ext.mk₀
              (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) v))
            (CategoryTheory.Abelian.Ext.mk₀ Θ) (add_zero r)
      _ = z'.comp (CategoryTheory.Abelian.Ext.mk₀
            ((NK.HassePrinciple.localUnitsIncl (K := k) (L := K) v) ≫ Θ)) (add_zero r) := by
          rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
      _ = z'.comp (CategoryTheory.Abelian.Ext.mk₀
            (Θ' ≫ Rep.resMap (conjStabHom k K σ v)
              (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) (σ • v)))) (add_zero r) := by
          rw [hΘ'fac]
      _ = z'.comp ((CategoryTheory.Abelian.Ext.mk₀ Θ').comp
            (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (conjStabHom k K σ v)
              (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) (σ • v)))) (zero_add 0))
            (add_zero r) := by
          rw [← CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
      _ = (z'.comp (CategoryTheory.Abelian.Ext.mk₀ Θ') (add_zero r)).comp
            (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (conjStabHom k K σ v)
              (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) (σ • v)))) (add_zero r) :=
          (CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero z'
            (CategoryTheory.Abelian.Ext.mk₀ Θ')
            (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (conjStabHom k K σ v)
              (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) (σ • v)))) (add_zero r)).symm
  -- the chain, rewritten through the factorisation of `extLoc v z`
  have hmain : SSGRoute.PTExt.extRes (conjStabHom k K σ v)
        (SSGRoute.PTExt.extLoc (k := k) (K := K) (σ • v) z)
      = ((CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
            ((conjTwistInv σ).app M))).comp
          (z'.comp (CategoryTheory.Abelian.Ext.mk₀ Θ') (add_zero r)) (zero_add r)).comp
        (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (conjStabHom k K σ v)
          (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) (σ • v)))) (add_zero r) := by
    calc SSGRoute.PTExt.extRes (conjStabHom k K σ v)
          (SSGRoute.PTExt.extLoc (k := k) (K := K) (σ • v) z)
        = (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
              ((conjTwistInv σ).app M))).comp
            ((SSGRoute.PTExt.extLoc (k := k) (K := K) v z).comp
              (CategoryTheory.Abelian.Ext.mk₀ Θ) (add_zero r)) (zero_add r) := hchain
      _ = (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
              ((conjTwistInv σ).app M))).comp
            ((z'.comp (CategoryTheory.Abelian.Ext.mk₀
                (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) v)) (add_zero r)).comp
              (CategoryTheory.Abelian.Ext.mk₀ Θ) (add_zero r)) (zero_add r) := by rw [hz']
      _ = (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
              ((conjTwistInv σ).app M))).comp
            ((z'.comp (CategoryTheory.Abelian.Ext.mk₀ Θ') (add_zero r)).comp
              (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (conjStabHom k K σ v)
                (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) (σ • v)))) (add_zero r))
            (zero_add r) := by rw [hKEY]
      _ = ((CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
              ((conjTwistInv σ).app M))).comp
            (z'.comp (CategoryTheory.Abelian.Ext.mk₀ Θ') (add_zero r)) (zero_add r)).comp
          (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (conjStabHom k K σ v)
            (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) (σ • v)))) (add_zero r) := by
        rw [← CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero
          (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
            ((conjTwistInv σ).app M)))
          (z'.comp (CategoryTheory.Abelian.Ext.mk₀ Θ') (add_zero r))
          (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (conjStabHom k K σ v)
            (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) (σ • v)))) (zero_add r)]
  -- `extRes` is onto, so the chain value has a preimage
  have hsurj : Function.Surjective (fun w' : CategoryTheory.Abelian.Ext
        (Rep.res (decompK (k := k) (σ • v)).subtype M)
        (NK.HassePrinciple.localUnitsSubRep k K (σ • v)) r =>
      SSGRoute.PTExt.extRes (conjStabHom k K σ v) w') := by
    haveI : (Rep.resFunctor (k := SSGRoute.PTExt.Coeff)
        (conjStabEquiv k K σ v).toMonoidHom).IsEquivalence := by
      simpa using resFunctor_isEquivalence (k := SSGRoute.PTExt.Coeff)
        (e := (conjStabEquiv k K σ v).symm)
    have hbij := Functor.mapExt_bijective_of_preservesProjectiveObjects
      (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (conjStabEquiv k K σ v).toMonoidHom)
      (Rep.res (decompK (k := k) (σ • v)).subtype M)
      (NK.HassePrinciple.localUnitsSubRep k K (σ • v)) r
    exact hbij.2
  obtain ⟨w', hw'⟩ := hsurj ((CategoryTheory.Abelian.Ext.mk₀
      (Rep.resMap (decompK (k := k) v).subtype ((conjTwistInv σ).app M))).comp
        (z'.comp (CategoryTheory.Abelian.Ext.mk₀ Θ') (add_zero r)) (zero_add r))
  have hw'' : SSGRoute.PTExt.extRes (conjStabHom k K σ v) w'
      = ((CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
            ((conjTwistInv σ).app M))).comp
          (z'.comp (CategoryTheory.Abelian.Ext.mk₀ Θ') (add_zero r)) (zero_add r)) := hw'
  -- the two classes have the same `extRes`-image, so they are equal
  have hfinal : SSGRoute.PTExt.extRes (conjStabHom k K σ v)
        (w'.comp (CategoryTheory.Abelian.Ext.mk₀
          (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) (σ • v))) (add_zero r))
      = SSGRoute.PTExt.extRes (conjStabHom k K σ v)
        (SSGRoute.PTExt.extLoc (k := k) (K := K) (σ • v) z) := by
    rw [extRes_comp_mk₀ (conjStabHom k K σ v) w'
      (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) (σ • v)), hw'']
    exact hmain.symm
  refine ⟨w', ?_⟩
  exact (extRes_injective_of_mulEquiv (conjStabEquiv k K σ v)
    (Rep.res (decompK (k := k) (σ • v)).subtype M)
    (SSGRoute.PTExt.localUnitsK (k := k) (K := K) (σ • v)) r hfinal).symm

end Work.SSGRoute.E9c
