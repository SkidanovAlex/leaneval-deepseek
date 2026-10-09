import Mathlib
import Submission.Work.SSGRoute.E1cGeneric.Canonical
import Submission.Work.SSGRoute.PT.PhiEgen_compat
import Submission.Work.SSGRoute.PT.e1aBetaCan_localAPI
import Submission.Work.SSGRoute.PT.exists_localField_place_data
import Submission.Work.SSGRoute.E1aClean.PhiERules
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local transport of the E1a comparison square

The comparison square of the E1a node (`Work.SSGRoute.E1aClean.comparisonSquareFin`) compares the
global `E1c` dictionary `PT.e1cEquiv` on the restriction of a class to the decomposition group
`D_A` with the *local* dictionary at the field data `(k_v, Ω_v, K')`.  The bridge between the two
sides is the canonical transport of the local `Ext`-group

  `Ext¹_{D_w}(E1cR1 N|, K_wˣ) ≅ Ext¹_{Gal(K'/k_v)}(res K'', (K')ˣ)`

of the coefficient `K_wˣ ≅ (K')ˣ` and the group `D_w ≅ Gal(K'/k_v)`.

Every ingredient is a *named* additive map (`coeffStep`, `groupStep`, `finalStep`, and the composite
`localExtTransport`), so that the computation rules of the `PhiE`-generators can be stated with the
named map in head position.  This matters: the terms of this development are large (`PhiEgen` of
`freeCover`/`freeCoverSES`/`Rep.res`), and a rewrite that has to unfold those definitions does not
terminate in any reasonable number of heartbeats.
-/

namespace Work.SSGRoute.E1aClean

set_option maxHeartbeats 4000000

open CategoryTheory SSGRoute.PTExt

section Basic

/-- **Postcomposition with an isomorphism of coefficient representations**, as a named additive map:
`x ↦ x ∘ mk₀ e.hom`. -/
noncomputable def extPostIsoHom {G : Type} [Group G] {N N' : Rep.{0} Coeff G} (e : N ≅ N')
    (M : Rep.{0} Coeff G) (n : ℕ) : Abelian.Ext M N n →+ Abelian.Ext M N' n :=
  (Abelian.Ext.mk₀ e.hom).postcomp M (add_zero n)

@[simp] theorem extPostIsoHom_apply {G : Type} [Group G] {N N' : Rep.{0} Coeff G} (e : N ≅ N')
    (M : Rep.{0} Coeff G) (n : ℕ) (x : Abelian.Ext M N n) :
    extPostIsoHom e M n x = Abelian.Ext.comp x (Abelian.Ext.mk₀ e.hom) (add_zero n) := rfl

/-- `extPostIsoHom` is injective (postcomposition with the inverse is a left inverse). -/
theorem extPostIsoHom_injective {G : Type} [Group G] {N N' : Rep.{0} Coeff G} (e : N ≅ N')
    (M : Rep.{0} Coeff G) (n : ℕ) : Function.Injective (extPostIsoHom e M n) := by
  intro x y h
  rw [extPostIsoHom_apply, extPostIsoHom_apply] at h
  have h2 := congrArg (fun z => Abelian.Ext.comp z (Abelian.Ext.mk₀ e.inv) (add_zero n)) h
  simpa only [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, e.hom_inv_id,
    Abelian.Ext.comp_mk₀_id] using h2

/-- **`PhiEgen` commutes with postcomposition in the coefficient.** -/
theorem extPostIsoHom_PhiEgen {G : Type} [Group G] [Fintype G] (X Z Z' : Rep.{0} Coeff G)
    (e : Z ≅ Z') (w : Abelian.Ext (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)) Z 0) :
    extPostIsoHom e X 1 (Work.SSGRoute.PT.PhiEgen X Z w)
      = Work.SSGRoute.PT.PhiEgen X Z'
          (CategoryTheory.Abelian.Ext.comp w (CategoryTheory.Abelian.Ext.mk₀ e.hom) (zero_add 0)) :=
  (extPostIsoHom_apply e X 1 _).trans
    (Work.SSGRoute.E1aClean.PhiEgen_postcomp X Z Z' e.hom w).symm

end Basic

section LocalData

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField K] [Fintype (K ≃ₐ[k] K)] {A : ValuationSubring Ω} {hA : SSGRoute.IsFinPlace k A}
  {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}

variable (K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA)
  (Work.SSGRoute.localClosureAt k A hA))
variable [FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) K']
variable [IsGalois (Work.SSGRoute.localFieldAt k A hA) K']
variable (eG : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
  (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K'))
variable [Fintype ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))]
variable [Fintype (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K')]

/-- The coefficient of the local level. -/
noncomputable abbrev localCoeff : Rep.{0} Coeff (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') :=
  SSGRoute.PTExt.modRep (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') (Additive (Units ↥K'))

/-- **The first variable of the local dictionary**. -/
noncomputable abbrev localFirst (X : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    Rep.{0} Coeff (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') :=
  Rep.res eG.symm.toMonoidHom (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)

/-- The canonical identification `Rep.res eG.symm (Rep.res eG Y) ≅ Y`. -/
noncomputable def resResIsoIso (Y : Rep.{0} Coeff (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K')) :
    Rep.res eG.symm.toMonoidHom (Rep.res eG.toMonoidHom Y) ≅ Y :=
  eqToIso (by
    change Rep.res (eG.toMonoidHom.comp eG.symm.toMonoidHom) Y = Y
    rw [show eG.toMonoidHom.comp eG.symm.toMonoidHom = MonoidHom.id _ from by ext x; simp,
      Rep.res_id])

/-- The comparison of the two canonical covers along `eG.symm`. -/
noncomputable def localCoverCompat (X : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    CategoryTheory.ShortComplex.Hom
      (Work.SSGRoute.freeCoverSES (localFirst K' eG X))
      ((Work.SSGRoute.freeCoverSES (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)).map
        (Rep.resFunctor (k := Coeff) eG.symm.toMonoidHom)) :=
  Classical.choose (Work.SSGRoute.PT.PhiEgen_res_compat
    (φ := eG.symm.toMonoidHom) (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)
    (Rep.res eG.toMonoidHom (localCoeff K')))

/-- **Step 1 of the local transport: the coefficient change** `K_wˣ → (K')ˣ`. -/
noncomputable def coeffStep (X : Rep.{0} Coeff (K ≃ₐ[k] K))
    (hiso : SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q) ≅ Rep.res eG.toMonoidHom (localCoeff K')) (n : ℕ) :
    Abelian.Ext (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X) (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q)) n →+
      Abelian.Ext (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X) (Rep.res eG.toMonoidHom (localCoeff K')) n :=
  extPostIsoHom hiso _ n

/-- **Step 2 of the local transport: the group change** along `eG`. -/
noncomputable def groupStep (X : Rep.{0} Coeff (K ≃ₐ[k] K)) (n : ℕ) :
    Abelian.Ext (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X) (Rep.res eG.toMonoidHom (localCoeff K')) n →+
      Abelian.Ext (localFirst K' eG X)
        (Rep.res eG.symm.toMonoidHom (Rep.res eG.toMonoidHom (localCoeff K'))) n :=
  (Rep.resFunctor eG.symm.toMonoidHom).mapExtAddHom
    (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X) (Rep.res eG.toMonoidHom (localCoeff K')) n

/-- **Step 3 of the local transport: the coefficient congruence**. -/
noncomputable def finalStep (X : Rep.{0} Coeff (K ≃ₐ[k] K)) (n : ℕ) :
    Abelian.Ext (localFirst K' eG X)
        (Rep.res eG.symm.toMonoidHom (Rep.res eG.toMonoidHom (localCoeff K'))) n →+
      Abelian.Ext (localFirst K' eG X) (localCoeff K') n :=
  extPostIsoHom (resResIsoIso K' eG (localCoeff K')) _ n

/-- **The local transport** of the E1a comparison square. -/
noncomputable def localExtTransport (X : Rep.{0} Coeff (K ≃ₐ[k] K))
    (hiso : SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q) ≅ Rep.res eG.toMonoidHom (localCoeff K')) (n : ℕ) :
    Abelian.Ext (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X) (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q)) n →+
      Abelian.Ext (localFirst K' eG X) (localCoeff K') n :=
  (finalStep K' eG X n).comp ((groupStep K' eG X n).comp (coeffStep K' eG X hiso n))

/-- The first half of the transported generator: the comparison of the covers composed with the
coefficient-changed and group-changed generator. -/
noncomputable def localGen₁ (X : Rep.{0} Coeff (K ≃ₐ[k] K))
    (hiso : SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q) ≅ Rep.res eG.toMonoidHom (localCoeff K'))
    (θ : Abelian.Ext (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)))
      (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q)) 0) :
    Abelian.Ext (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (localFirst K' eG X)))
      (Rep.res eG.symm.toMonoidHom (Rep.res eG.toMonoidHom (localCoeff K'))) 0 :=
  CategoryTheory.Abelian.Ext.comp
    (CategoryTheory.Abelian.Ext.mk₀ (localCoverCompat K' eG X).τ₁)
    ((Rep.resFunctor (k := Coeff) eG.symm.toMonoidHom).mapExtAddHom
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)))
      (Rep.res eG.toMonoidHom (localCoeff K')) 0
      (CategoryTheory.Abelian.Ext.comp θ (CategoryTheory.Abelian.Ext.mk₀ hiso.hom)
        (zero_add 0)))
    (zero_add 0)

/-- **The transported generator** of the local `PhiE`-generators. -/
noncomputable def localGen (X : Rep.{0} Coeff (K ≃ₐ[k] K))
    (hiso : SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q) ≅ Rep.res eG.toMonoidHom (localCoeff K'))
    (θ : Abelian.Ext (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)))
      (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q)) 0) :
    Abelian.Ext (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (localFirst K' eG X)))
      (localCoeff K') 0 :=
  CategoryTheory.Abelian.Ext.comp (localGen₁ K' eG X hiso θ)
    (CategoryTheory.Abelian.Ext.mk₀ (resResIsoIso K' eG (localCoeff K')).hom) (zero_add 0)

/-- **The rule of step 1 on the generators.** -/
theorem coeffStep_PhiEgen (X : Rep.{0} Coeff (K ≃ₐ[k] K))
    (hiso : SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q) ≅ Rep.res eG.toMonoidHom (localCoeff K'))
    (θ : Abelian.Ext (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)))
      (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q)) 0) :
    coeffStep K' eG X hiso 1 (Work.SSGRoute.PT.PhiEgen (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X) (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q)) θ)
      = Work.SSGRoute.PT.PhiEgen (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)
          (Rep.res eG.toMonoidHom (localCoeff K'))
          (CategoryTheory.Abelian.Ext.comp θ (CategoryTheory.Abelian.Ext.mk₀ hiso.hom)
            (zero_add 0)) :=
  extPostIsoHom_PhiEgen _ _ _ hiso θ

/-- **The rule of step 2 on the generators.** -/
theorem groupStep_PhiEgen (X : Rep.{0} Coeff (K ≃ₐ[k] K))
    (θ : Abelian.Ext (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)))
      (Rep.res eG.toMonoidHom (localCoeff K')) 0) :
    groupStep K' eG X 1
        (Work.SSGRoute.PT.PhiEgen (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)
          (Rep.res eG.toMonoidHom (localCoeff K')) θ)
      = Work.SSGRoute.PT.PhiEgen (localFirst K' eG X)
          (Rep.res eG.symm.toMonoidHom (Rep.res eG.toMonoidHom (localCoeff K')))
          (CategoryTheory.Abelian.Ext.comp
            (CategoryTheory.Abelian.Ext.mk₀ (localCoverCompat K' eG X).τ₁)
            ((Rep.resFunctor (k := Coeff) eG.symm.toMonoidHom).mapExtAddHom
              (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)))
              (Rep.res eG.toMonoidHom (localCoeff K')) 0 θ)
            (zero_add 0)) :=
  (Classical.choose_spec (Work.SSGRoute.PT.PhiEgen_res_compat
    (φ := eG.symm.toMonoidHom) (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)
    (Rep.res eG.toMonoidHom (localCoeff K')))).2.2 θ

/-- **The rule of step 3 on the generators.** -/
theorem finalStep_PhiEgen (X : Rep.{0} Coeff (K ≃ₐ[k] K))
    (θ : Abelian.Ext (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (localFirst K' eG X)))
      (Rep.res eG.symm.toMonoidHom (Rep.res eG.toMonoidHom (localCoeff K'))) 0) :
    finalStep K' eG X 1
        (Work.SSGRoute.PT.PhiEgen (localFirst K' eG X)
          (Rep.res eG.symm.toMonoidHom (Rep.res eG.toMonoidHom (localCoeff K'))) θ)
      = Work.SSGRoute.PT.PhiEgen (localFirst K' eG X) (localCoeff K')
          (CategoryTheory.Abelian.Ext.comp θ
            (CategoryTheory.Abelian.Ext.mk₀ (resResIsoIso K' eG (localCoeff K')).hom)
            (zero_add 0)) :=
  extPostIsoHom_PhiEgen _ _ _ (resResIsoIso K' eG (localCoeff K')) θ

/-- **The local transport is injective** — all of its factors are. -/
theorem localExtTransport_injective (X : Rep.{0} Coeff (K ≃ₐ[k] K))
    (hiso : SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q) ≅ Rep.res eG.toMonoidHom (localCoeff K')) (n : ℕ) :
    Function.Injective (localExtTransport K' eG X hiso n) := by
  haveI hE : (Rep.resFunctor (k := Coeff) eG.symm.toMonoidHom).IsEquivalence :=
    resFunctor_isEquivalence eG
  have hbij : Function.Bijective (groupStep K' eG X n) :=
    Functor.mapExt_bijective_of_preservesProjectiveObjects _ _ _ _
  exact (extPostIsoHom_injective _ _ n).comp
    (hbij.injective.comp (extPostIsoHom_injective _ _ n))


end LocalData

end Work.SSGRoute.E1aClean
