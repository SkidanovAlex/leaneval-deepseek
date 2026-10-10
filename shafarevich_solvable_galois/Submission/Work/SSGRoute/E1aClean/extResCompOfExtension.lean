import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.E1aClean.PhiERules
import Submission.Work.SSGRoute.PT.delta_restrictSES
import Submission.Work.SSGRoute.PT.e1cDelta_beta_relation_gen
import Submission.Work.SSGRoute.finite_openKernel_homs_decomp_kernel
import Submission.Work.SSGRoute.localGaloisEquiv_coInAdjoin_compat_general
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The localisation of a `PhiE`-generator, after a coefficient extension

`extResCompOfExtension` is the abstract form of the *finite-place criterion* of the E1a landing
clause, in the `PhiE`-generator language: if a class `w : Ext⁰_G(ker (freeCover N), Kˣ)` is such
that its image `w ∘ mk₀ (unitsToLocalUnits)` at a decomposition group `D ≤ Gal(K/k)` factors
through the canonical cover `F → N` (`hφ`), then the *localisation* of the `PhiE`-generator of `w`
at `D` — `extRes_D (PhiE w) ∘ mk₀ (unitsToLocalUnits)` — vanishes.

The proof is the three standard rules of the canonical presentation:

* `PT.PhiEgen_res_compat` — `PhiE` commutes with restriction along `D.subtype`, up to the
  comparison `Φ` of the two canonical presentations;
* `E1aClean.PhiEgen_postcomp` — `PhiE` commutes with postcomposition in the coefficient;
* `ShortComplex.ShortExact.extClass_comp_assoc` — the connecting class of the canonical
  presentation is killed by `mk₀` of its own first differential,

together with the hypothesis `hφ`, which says precisely that the coefficient-changed class
`w ∘ mk₀ (unitsToLocalUnits)` lies in the range of `precomp (mk₀ (kernel.ι))`.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

-- Needed so that the extensionality tactics can see through the `Rep.of`-wrapped objects that
-- `Rep.resMap`/`Rep.res` produce (compare `CohomologicallyTrivial/coker_iso_quotRep.lean`).
attribute [local instance 10000] Rep.hV2 Rep.hV1

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000

noncomputable section

/-- **Localisation of a `PhiE`-generator which factors through the canonical cover, at a subgroup.**

Let `f : H →* G` be a group homomorphism, `M R : Rep Coeff G`, `Z : Rep Coeff H` and
`ι : Rep.res f R ⟶ Z`.  If `w : Ext⁰_G(ker (freeCover M), R)` becomes, after restriction and the
coefficient map `ι`, the image of an `H`-equivariant map `φ : Rep.res f ((freeCoverSES M).X₂) ⟶ Z`
under precomposition with `ker (freeCover M) ↪ freeCoverSES M`, then the localisation
`extRes f (PhiE w) ∘ mk₀ ι ∈ Ext¹_H(ker (freeCoverSES (Rep.res f M)), Z)` vanishes. -/
theorem extRes_PhiEgen_comp_mk₀_eq_zero {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]
    (f : H →* G) (M R : Rep.{0} SSGRoute.PTExt.Coeff G) (Z : Rep.{0} SSGRoute.PTExt.Coeff H)
    (ι : Rep.res f R ⟶ Z)
    (w : CategoryTheory.Abelian.Ext (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover M)) R 0)
    (φ : Rep.res f (Work.SSGRoute.freeCoverSES M).X₂ ⟶ Z)
    (hφ : ∀ r : (Work.SSGRoute.freeCoverSES M).X₁,
        Rep.Hom.hom φ ((Work.SSGRoute.freeCoverSES M).f r)
          = Rep.Hom.hom ι (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ w) r)) :
    (SSGRoute.PTExt.extRes f (Work.SSGRoute.PT.PhiEgen M R w)).comp
      (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1) = 0 := by
  obtain ⟨Φ, hτ2, hτ3, hmain⟩ := Work.SSGRoute.PT.PhiEgen_res_compat f M R
  -- Re-type the comparison of the canonical presentations into the `Rep.res`-flavour, so that
  -- every rewriting step below happens at a syntactic match (the two flavours are only
  -- definitionally equal: `((freeCoverSES M).map F).Xᵢ` vs `Rep.res f ((freeCoverSES M).Xᵢ)`).
  let τ₁ : (Work.SSGRoute.freeCoverSES (Rep.res f M)).X₁
      ⟶ Rep.res f (Work.SSGRoute.freeCoverSES M).X₁ := Φ.τ₁
  let τ₂ : (Work.SSGRoute.freeCoverSES (Rep.res f M)).X₂
      ⟶ Rep.res f (Work.SSGRoute.freeCoverSES M).X₂ := Φ.τ₂
  have hcomm : τ₁ ≫ Rep.resMap f (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover M))
      = (Work.SSGRoute.freeCoverSES (Rep.res f M)).f ≫ τ₂ := Φ.comm₁₂
  have hE : SSGRoute.PTExt.extRes f w
      = CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap f (CategoryTheory.Abelian.Ext.addEquiv₀ w)) := by
    conv_lhs => rw [← CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply w]
    simp only [SSGRoute.PTExt.extRes, CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
  have hφ' : Rep.resMap f (CategoryTheory.Abelian.Ext.addEquiv₀ w) ≫ ι
      = Rep.resMap f (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover M)) ≫ φ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro r
    simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
      Rep.resMap_hom_toLinearMap]
    exact (hφ r).symm
  have hgrp : SSGRoute.PTExt.extRes f (Work.SSGRoute.PT.PhiEgen M R w)
      = Work.SSGRoute.PT.PhiEgen (Rep.res f M) (Rep.res f R)
          ((CategoryTheory.Abelian.Ext.mk₀ τ₁).comp (SSGRoute.PTExt.extRes f w) (zero_add 0)) := by
    rw [show SSGRoute.PTExt.extRes f (Work.SSGRoute.PT.PhiEgen M R w)
        = (Rep.resFunctor f).mapExtAddHom M R 1 (Work.SSGRoute.PT.PhiEgen M R w) from rfl]
    exact hmain w
  have hpost : (Work.SSGRoute.PT.PhiEgen (Rep.res f M) (Rep.res f R)
          ((CategoryTheory.Abelian.Ext.mk₀ τ₁).comp (SSGRoute.PTExt.extRes f w) (zero_add 0))).comp
        (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)
      = Work.SSGRoute.PT.PhiEgen (Rep.res f M) Z
        (((CategoryTheory.Abelian.Ext.mk₀ τ₁).comp (SSGRoute.PTExt.extRes f w) (zero_add 0)).comp
          (CategoryTheory.Abelian.Ext.mk₀ ι) (zero_add 0)) :=
    (Work.SSGRoute.E1aClean.PhiEgen_postcomp (Rep.res f M) (Rep.res f R) Z ι
      ((CategoryTheory.Abelian.Ext.mk₀ τ₁).comp (SSGRoute.PTExt.extRes f w) (zero_add 0))).symm
  have hZ : (SSGRoute.PTExt.extRes f w).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (zero_add 0)
      = CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap f (CategoryTheory.Abelian.Ext.addEquiv₀ w) ≫ ι) := by
    rw [hE, CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
  have hcomp : (((CategoryTheory.Abelian.Ext.mk₀ τ₁).comp (SSGRoute.PTExt.extRes f w) (zero_add 0)).comp
        (CategoryTheory.Abelian.Ext.mk₀ ι) (zero_add 0))
      = CategoryTheory.Abelian.Ext.mk₀
          ((Work.SSGRoute.freeCoverSES (Rep.res f M)).f ≫ (τ₂ ≫ φ)) := by
    refine (CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero _ _ _ _).trans ?_
    refine (congrArg (fun x => (CategoryTheory.Abelian.Ext.mk₀ τ₁).comp x (zero_add 0)) hZ).trans ?_
    refine (CategoryTheory.Abelian.Ext.mk₀_comp_mk₀ _ _).trans ?_
    refine congrArg CategoryTheory.Abelian.Ext.mk₀ ?_
    rw [hφ']
    rw [← Category.assoc]
    rw [hcomm]
    rw [Category.assoc]
  have hzero : Work.SSGRoute.PT.PhiEgen (Rep.res f M) Z
      (CategoryTheory.Abelian.Ext.mk₀
        ((Work.SSGRoute.freeCoverSES (Rep.res f M)).f ≫ (τ₂ ≫ φ))) = 0 := by
    rw [Work.SSGRoute.PT.PhiEgen_apply]
    rw [← CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
    exact CategoryTheory.ShortComplex.ShortExact.extClass_comp_assoc
      (Work.SSGRoute.freeCoverSES_shortExact (Rep.res f M))
      (CategoryTheory.Abelian.Ext.mk₀ (τ₂ ≫ φ))
  rw [hgrp, hpost, hcomp, hzero]

theorem extResCompOfExtension
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    (q : NK.GlobalCFT.Place K)
    (w : CategoryTheory.Abelian.Ext.{0}
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k:=k) (Ω:=Ω) (K:=K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
        (SSGRoute.PTExt.unitsK k K) 0)
    (φ : Rep.res (SSGRoute.PTExt.decompK (k:=k) q).subtype
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k:=k) (Ω:=Ω) (K:=K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
        ⟶ SSGRoute.PTExt.localUnitsK (k:=k) q)
    (hφ : ∀ r : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k:=k) (Ω:=Ω) (K:=K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))).V,
      Rep.Hom.hom φ (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k:=k) (Ω:=Ω) (K:=K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) r)
        = (NK.HassePrinciple.unitsToLocalUnitsHom q).toAdditive
            (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ w) r)) :
    (SSGRoute.PTExt.extRes (SSGRoute.PTExt.decompK (k:=k) q).subtype
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k:=k) (Ω:=Ω) (K:=K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) w)).comp
      (CategoryTheory.Abelian.Ext.mk₀
        (NK.HassePrinciple.unitsToLocalUnits k K q)) (add_zero 1) = 0 := by
  haveI hGfin : Fintype (K ≃ₐ[k] K) := inferInstance
  haveI hHfin : Fintype ↥(SSGRoute.PTExt.decompK (k:=k) q) := Fintype.ofFinite _
  exact extRes_PhiEgen_comp_mk₀_eq_zero (SSGRoute.PTExt.decompK (k:=k) q).subtype
    (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))
    (SSGRoute.PTExt.unitsK k K) (SSGRoute.PTExt.localUnitsK (k:=k) q)
    (NK.HassePrinciple.unitsToLocalUnits k K q) w φ hφ

end

end Work.SSGRoute.E1aClean
