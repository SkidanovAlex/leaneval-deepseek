import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.sylow_in_defs
import Submission.Work.SSGRoute.phiAt_level_infl
import Submission.Work.SSGRoute.nonempty_extH_addEquiv_mulEquiv
import Submission.Work.SSGRoute.classFormation_ext
import Submission.Work.SSGRoute.ext_res_mulEquiv
import Submission.Work.SSGRoute.extH_congr
import Submission.Work.SSGRoute.extCor_yoneda_comp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


/-!
# E6Ω: the Sylow descent, level by level

This file develops the level bookkeeping of the Sylow descent `Work.SSGRoute.phi1_mono_sylow_in`
(E6Ω) for a tower `k ⊆ k' ⊆ K ⊆ L` of number fields with `k'/k` of degree prime to `p`,
`K/k` and `K/k'` Galois, and `L/k` and `L/k'` Galois.

The descent compares the `k`-level pairing `Φ¹_k(x)` with the `k'`-level pairing `Φ¹_{k'}(x'')` at
the level `L`:

* `S := (resBaseHom k k' L).range ≤ L ≃ₐ[k] L` is the image of `Gal(L/k')`, so that `Gal(L/k')` is
  isomorphic to a *subgroup* `S` of `Gal(L/k)`;
* the projection formula (`Work.SSGRoute.extCor_yoneda_comp`) and the injectivity of corestriction
  on the class formation (`Work.SSGRoute.ClassFormation.extCor_injective_classesK`) show that the
  `S`-world value of the pairing of the base-changed class vanishes (this is
  `extCor_level_value_eq_zero` below) — this is the only place where the hypothesis over `k` is
  used;
* the transport between the `S`-world and the `k'`-world along the group isomorphism is the content
  of `level_value_eq_transport`.
-/

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute
namespace SylowLevel

open SSGRoute.PTExt CategoryTheory
open Work.SSGRoute.SylowIn

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

section Setup

variable {k k' K L : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] [Field K]
  [NumberField K] [Field L] [NumberField L]
  [Algebra k K] [Algebra k' K] [Algebra k k'] [IsScalarTower k k' K]
  [Algebra k L] [Algebra K L] [IsScalarTower k K L] [Algebra k' L] [IsScalarTower k' K L]
  [IsScalarTower k k' L]
  [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k' K] [IsGalois k' K]
  [FiniteDimensional k L] [IsGalois k L] [IsGalois k' L]

/-- **The `S`-world vanishing at a level.**  For a `k`-Galois level `L`, the value of the
`k'`-level pairing of the base-changed class `baseChangeExt M x`, computed in the subgroup
`S = range (resBaseHom k k' L) ≤ Gal(L/k)` of the level `L`, vanishes, provided the `k`-level
value at `L` of `x` vanishes.  The proof is the projection formula
`Work.SSGRoute.extCor_yoneda_comp` (giving `cor (b ∘ res x_L') = (cor b) ∘ x_L' = Φ¹_k(x)(cor b)`)
together with the injectivity of corestriction on the class formation. -/
theorem extCor_level_value_eq_zero
    (M : Rep Coeff (K ≃ₐ[k] K)) (x : Abelian.Ext M (classesK k K) 1)
    (hxL : ∀ h : extH (Rep.res (galRes k K L) M) 1,
      phiAt (k := k) (K := K) (L := L) x h = 0)
    (b : extH (Rep.res ((resBaseHom k k' L).range).subtype (Rep.res (galRes k K L) M)) 1) :
    b.comp (extRes ((resBaseHom k k' L).range).subtype
        ((extRes (galRes k K L) x).comp (Abelian.Ext.mk₀ (classIncl k K L)) (add_zero 1)))
      rfl = 0 := by
  classical
  letI : Fintype (L ≃ₐ[k] L) := Fintype.ofFinite _
  letI : DecidableRel (QuotientGroup.rightRel ((resBaseHom k k' L).range)) := Classical.decRel _
  have hproj := extCor_yoneda_comp ((resBaseHom k k' L).range)
    ((extRes (galRes k K L) x).comp (Abelian.Ext.mk₀ (classIncl k K L)) (add_zero 1)) b
  have hval : (extCor ((resBaseHom k k' L).range) (unitRep (L ≃ₐ[k] L))
        (Rep.res (galRes k K L) M) 1 b).comp
        ((extRes (galRes k K L) x).comp (Abelian.Ext.mk₀ (classIncl k K L)) (add_zero 1)) rfl
      = phiAt (k := k) (K := K) (L := L) x
          (extCor ((resBaseHom k k' L).range) (unitRep (L ≃ₐ[k] L))
            (Rep.res (galRes k K L) M) 1 b) := rfl
  have h1 : extCor ((resBaseHom k k' L).range) (unitRep (L ≃ₐ[k] L)) (classesK k L) (1 + 1)
        (b.comp (extRes ((resBaseHom k k' L).range).subtype
          ((extRes (galRes k K L) x).comp (Abelian.Ext.mk₀ (classIncl k K L)) (add_zero 1)))
          rfl)
      = extCor ((resBaseHom k k' L).range) (unitRep (L ≃ₐ[k] L)) (classesK k L) (1 + 1) 0 := by
    rw [map_zero]
    exact hproj.trans (hval.trans (hxL _))
  exact ClassFormation.extCor_injective_classesK (k := k) (L := L)
    ((resBaseHom k k' L).range) h1


/-- **The level class is the transport of the `S`-world class.**  The `k'`-level class
`xq = (extRes (galRes k' K L) (baseChangeExt M x)).comp (mk₀ (classIncl k' K L))` is the image of
the `S`-world class `extRes S.subtype ((extRes (galRes k K L) x).comp (mk₀ (classIncl k K L)))`
under the group isomorphism `Gal(L/k') ≅ S` and the base change of the coefficient modules.
This is the "keystone" of the case (i) transfer: it uses `SylowIn.baseChangeExt_lift` (the class
`baseChangeExt M x` at the level `L`), the composition of restrictions
`SylowDesc.extRes_comp_aux` and the comparison of the two coefficient maps
`SylowIn.mk₀_classIncl_baseChange`. -/
theorem level_class_transport
    (M : Rep Coeff (K ≃ₐ[k] K)) (x : Abelian.Ext M (classesK k K) 1) :
    (extRes ((resBaseHom k k' L).rangeRestrict)
        (extRes ((resBaseHom k k' L).range).subtype
          ((extRes (galRes k K L) x).comp (Abelian.Ext.mk₀ (classIncl k K L)) (add_zero 1)))).comp
      (Abelian.Ext.mk₀ (SylowDesc.classesK_baseChangeIso k k' L).hom) rfl
    = (extRes (galRes k' K L) (baseChangeExt M x)).comp
        (Abelian.Ext.mk₀ (classIncl k' K L)) (add_zero 1) := by
  rw [baseChangeExt_lift]
  have h1 : extRes ((resBaseHom k k' L).rangeRestrict)
      (extRes ((resBaseHom k k' L).range).subtype
        ((extRes (galRes k K L) x).comp (Abelian.Ext.mk₀ (classIncl k K L)) (add_zero 1)))
      = extRes (resBaseHom k k' L)
        ((extRes (galRes k K L) x).comp (Abelian.Ext.mk₀ (classIncl k K L)) (add_zero 1)) := by
    rw [← SylowDesc.extRes_comp_aux (((resBaseHom k k' L).range).subtype)
      ((resBaseHom k k' L).rangeRestrict)
      ((extRes (galRes k K L) x).comp (Abelian.Ext.mk₀ (classIncl k K L)) (add_zero 1))]
    rfl
  rw [h1]
  have hcomp : Abelian.Ext.mapExactFunctor (Rep.resFunctor (resBaseHom k k' L))
      (Abelian.Ext.mapExactFunctor (Rep.resFunctor (galRes k K L)) x)
      = Abelian.Ext.mapExactFunctor
          (Rep.resFunctor ((galRes k K L).comp (resBaseHom k k' L))) x := by
    simpa only [extRes] using
      (SylowDesc.extRes_comp_aux (galRes k K L) (resBaseHom k k' L) x).symm
  have h2 : extRes (resBaseHom k k' L)
        ((extRes (galRes k K L) x).comp (Abelian.Ext.mk₀ (classIncl k K L)) (add_zero 1))
      = (extRes ((galRes k K L).comp (resBaseHom k k' L)) x).comp
          (Abelian.Ext.mk₀ (Rep.resMap (resBaseHom k k' L) (classIncl k K L))) (add_zero 1) := by
    simp only [extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀, hcomp]
  rw [h2]
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero
    (extRes ((galRes k K L).comp (resBaseHom k k' L)) x)
    (Abelian.Ext.mk₀ (Rep.resMap (resBaseHom k k' L) (classIncl k K L)))
    (Abelian.Ext.mk₀ (SylowDesc.classesK_baseChangeIso k k' L).hom) (add_zero 1)]
  rw [Abelian.Ext.mk₀_comp_mk₀]
  have hδ1 : (baseChangeDomainIso (k := k) (k' := k') (K := K) (L := L)).hom = 𝟙 _ := by
    show eqToHom (baseChangeDomain_eq (k := k) (k' := k') (K := K) (L := L)) = 𝟙 _
    rw [show baseChangeDomain_eq (k := k) (k' := k') (K := K) (L := L) = rfl from
      Subsingleton.elim _ _]
    exact eqToHom_refl _ _
  rw [mk₀_classIncl_baseChange, hδ1, Category.id_comp]
  rfl


/-! ## The transport along the group isomorphism `Gal(L/k') ≅ S ≤ Gal(L/k)` -/

/-- The restriction of scalars homomorphism `Gal(L/k') →* Gal(L/k)` is injective. -/
theorem resBaseHom_injective (k k' K : Type) [Field k] [Field k'] [Field K] [Algebra k K]
    [Algebra k' K] [Algebra k k'] [IsScalarTower k k' K] :
    Function.Injective (resBaseHom k k' K) := by
  intro σ τ h
  ext x
  exact congrArg (fun (φ : K ≃ₐ[k] K) => φ x) h

/-- **Change of groups along a bijective homomorphism** is bijective on `Ext`-cohomology: the
underlying function `x ↦ x.mapExactFunctor (Rep.resFunctor f)` identifies `Hⁿ(G, A)` with
`Hⁿ(H, Rep.res f A)`.  This is `Work.SSGRoute.nonempty_extH_addEquiv_mulEquiv` (the change of
groups along a group isomorphism) transported along the equality
`(MulEquiv.ofBijective f _).toMonoidHom = f`. -/
theorem mapExactFunctor_bijective_of_mulEquiv {H G : Type} [Group H] [Group G] (e : H ≃* G)
    (A : Rep Coeff G) (n : ℕ) :
    Function.Bijective (fun x : extH A n =>
      x.mapExactFunctor (Rep.resFunctor (k := Coeff) e.toMonoidHom)) := by
  haveI : (Rep.resFunctor (k := Coeff) e.toMonoidHom).IsEquivalence :=
    resFunctor_isEquivalence e.symm
  exact Functor.mapExt_bijective_of_preservesProjectiveObjects _ (unitRep G) A n

/-- **Change of groups along a bijective homomorphism** is bijective on `Ext`-cohomology: the
underlying function `x ↦ x.mapExactFunctor (Rep.resFunctor f)` identifies `Hⁿ(G, A)` with
`Hⁿ(H, Rep.res f A)`. -/
theorem mapExactFunctor_bijective_of_bijective {H G : Type} [Group H] [Group G] (f : H →* G)
    (hf : Function.Bijective f) (A : Rep Coeff G) (n : ℕ) :
    Function.Bijective (fun x : extH A n =>
      x.mapExactFunctor (Rep.resFunctor (k := Coeff) f)) := by
  have key := mapExactFunctor_bijective_of_mulEquiv (MulEquiv.ofBijective f hf) A n
  have hh : (MulEquiv.ofBijective f hf).toMonoidHom = f := by
    ext x
    exact MulEquiv.ofBijective_apply f hf x
  rw [← hh]
  exact key

/-- The range restriction `Gal(L/k') →* S` is bijective. -/
theorem rangeRestrict_bijective :
    Function.Bijective (resBaseHom k k' L).rangeRestrict :=
  ⟨fun a b hab => resBaseHom_injective k k' L (congrArg Subtype.val hab),
    MonoidHom.rangeRestrict_surjective _⟩

/-- **The `S`-world to `k'`-world transport is bijective on the level cohomology.** -/
theorem transport_bijective (A : Rep Coeff ↥((resBaseHom k k' L).range)) (n : ℕ) :
    Function.Bijective (fun x : extH A n =>
      x.mapExactFunctor (Rep.resFunctor (k := Coeff) ((resBaseHom k k' L).rangeRestrict))) :=
  mapExactFunctor_bijective_of_bijective _ rangeRestrict_bijective A n

/-- **The value at a `k`-Galois level is the transport of the `S`-world value.**  This is the
naturality of the pairing under the change of groups `Gal(L/k') ≅ S ≤ Gal(L/k)`: for every
`b ∈ H¹(S, M_L)`, the `k'`-level pairing value of `baseChangeExt M x` at the transported class is
the transported `S`-world value.  It follows from `level_class_transport` (the transported class is
the `k'`-level class) and the functoriality of `Abelian.Ext.mapExactFunctor`. -/
theorem level_value_eq_transport
    (M : Rep Coeff (K ≃ₐ[k] K)) (x : Abelian.Ext M (classesK k K) 1)
    (b : extH (Rep.res ((resBaseHom k k' L).range).subtype (Rep.res (galRes k K L) M)) 1) :
    (b.mapExactFunctor (Rep.resFunctor (k := Coeff) ((resBaseHom k k' L).rangeRestrict))).comp
        ((extRes (galRes k' K L) (baseChangeExt M x)).comp
          (Abelian.Ext.mk₀ (classIncl k' K L)) (add_zero 1)) rfl
      = ((b.comp (extRes ((resBaseHom k k' L).range).subtype
            ((extRes (galRes k K L) x).comp (Abelian.Ext.mk₀ (classIncl k K L)) (add_zero 1)))
              rfl).mapExactFunctor (Rep.resFunctor (k := Coeff) ((resBaseHom k k' L).rangeRestrict))).comp
          (Abelian.Ext.mk₀ (SylowDesc.classesK_baseChangeIso k k' L).hom) rfl := by
  rw [Abelian.Ext.mapExactFunctor_comp]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero
    (b.mapExactFunctor (Rep.resFunctor (k := Coeff) ((resBaseHom k k' L).rangeRestrict)))
    ((extRes ((resBaseHom k k' L).range).subtype
      ((extRes (galRes k K L) x).comp (Abelian.Ext.mk₀ (classIncl k K L)) (add_zero 1))).mapExactFunctor
        (Rep.resFunctor (k := Coeff) ((resBaseHom k k' L).rangeRestrict)))
    (Abelian.Ext.mk₀ (SylowDesc.classesK_baseChangeIso k k' L).hom) rfl]
  refine congrArg (fun z => (b.mapExactFunctor (Rep.resFunctor (k := Coeff)
    ((resBaseHom k k' L).rangeRestrict))).comp z rfl) ?_
  simpa only [extRes] using
    (level_class_transport (k := k) (k' := k') (K := K) (L := L) M x).symm

theorem phi1_value_kprime_zero_of_galoisLevel
    (M : Rep Coeff (K ≃ₐ[k] K)) (x : Abelian.Ext M (classesK k K) 1)
    (hxL : ∀ h : extH (Rep.res (galRes k K L) M) 1,
      phiAt (k := k) (K := K) (L := L) x h = 0)
    (h : extH (Rep.res (galRes k' K L) (Rep.res (resBaseHom k k' K) M)) 1) :
    phiAt (k := k') (K := K) (L := L) (baseChangeExt M x) h = 0 := by
  let MS : Rep Coeff ↥((resBaseHom k k' L).range) :=
    Rep.res ((resBaseHom k k' L).range).subtype (Rep.res (galRes k K L) M)
  have hsurj : Function.Surjective (fun (b : extH MS 1) =>
      b.mapExactFunctor (Rep.resFunctor (k := Coeff) ((resBaseHom k k' L).rangeRestrict))) :=
    (transport_bijective (k := k) (k' := k') (L := L) MS 1).surjective
  obtain ⟨b, hb⟩ := hsurj h
  rw [← hb]
  show (b.mapExactFunctor (Rep.resFunctor (k := Coeff)
        ((resBaseHom k k' L).rangeRestrict))).comp
      ((extRes (galRes k' K L) (baseChangeExt M x)).comp
        (Abelian.Ext.mk₀ (classIncl k' K L)) (add_zero 1)) rfl = 0
  rw [level_value_eq_transport (k := k) (k' := k') (K := K) (L := L) M x b]
  rw [extCor_level_value_eq_zero (k := k) (k' := k') (K := K) (L := L) M x hxL b]
  simp only [Abelian.Ext.mapExactFunctor_zero, Abelian.Ext.zero_comp, Abelian.Ext.comp_zero]

end Setup

/-! ## Case (ii): levels over `k'` that are not Galois over `k` -/

section CaseTwo

variable {k k' K Ω : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] [Field K]
  [NumberField K] [Algebra k K] [Algebra k' K] [Algebra k k'] [IsScalarTower k k' K]
  [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [Algebra k' Ω]
  [IsScalarTower k K Ω] [IsScalarTower k' K Ω] [IsScalarTower k k' Ω]
  [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k' K] [IsGalois k' K]

/-- **Change of groups along an isomorphism is bijective on `Ext`.**  For a group isomorphism
`e : H ≃* G` and arbitrary coefficient modules `M A : Rep Coeff G`, the underlying function
`x ↦ extRes e.toMonoidHom x` is a bijection
`Ext_G(M,A) ≃ Ext_H(res M, res A)`.  (This is Mathlib's
`Functor.mapExt_bijective_of_preservesProjectiveObjects` for the equivalence of categories
`Rep.resFunctor e.toMonoidHom`.) -/
theorem extRes_bijective_of_mulEquiv {G H : Type} [Group G] [Group H] (e : H ≃* G)
    (M A : Rep Coeff G) (n : ℕ) :
    Function.Bijective (fun x : Abelian.Ext M A n => extRes e.toMonoidHom x) := by
  haveI : (Rep.resFunctor (k := Coeff) e.toMonoidHom).IsEquivalence :=
    Work.SSGRoute.resFunctor_isEquivalence_toMonoidHom e
  have h1 : (fun x : Abelian.Ext M A n =>
        x.mapExactFunctor (Rep.resFunctor (k := Coeff) e.toMonoidHom))
      = ⇑((Rep.resFunctor (k := Coeff) e.toMonoidHom).mapExtAddHom M A n) := by
    funext x
    exact (Functor.mapExtAddHom_apply (F := Rep.resFunctor (k := Coeff) e.toMonoidHom)
      (X := M) (Y := A) (n := n) x).symm
  rw [show (fun x : Abelian.Ext M A n => extRes e.toMonoidHom x)
      = (fun x : Abelian.Ext M A n =>
        x.mapExactFunctor (Rep.resFunctor (k := Coeff) e.toMonoidHom)) from rfl, h1]
  exact Functor.mapExt_bijective_of_preservesProjectiveObjects
    (Rep.resFunctor (k := Coeff) e.toMonoidHom) M A n

/-- **Case (ii) of the Sylow transfer.**  At a level `L` that is Galois over `k'` (but possibly not
over `k`), the `(k', K)`-value of the base-changed class vanishes as soon as it vanishes at every
larger level that is Galois over both `k` and `k'` (the hypothesis `hGal`) and the level inflation
`H²(Gal(L/k'), C_L) → H²(Gal(L'/k'), C_{L'})` is injective (`hinj`, proved in
`Submission/Work/SSGRoute/sylow_infl_injective.lean` from
`Work.SSGRoute.classIncl_inflation_injective` and the `E0b` bridge).

Proof: pass to the normal closure `L'` of `L` over `k` inside `Ω` (constructed as an
`IntermediateField K Ω` with the same carrier as `IntermediateField.normalClosure k ↥L Ω`), which is
finite Galois over both `k` and `k'`; apply `hGal` there, use the level-inflation compatibility
`Work.SSGRoute.phiAt_level_infl` and `hinj`. -/
theorem phi1_value_kprime_zero_of_level
    (M : Rep Coeff (K ≃ₐ[k] K)) (x : Abelian.Ext M (classesK k K) 1)
    (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k' L] [FiniteDimensional k L]
    [IsGalois k' L]
    (hGal : ∀ (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L']
        [FiniteDimensional k' L'] [IsGalois k L'] [IsGalois k' L'] (hLL : L ≤ L')
        (h' : extH (Rep.res (galRes k' K L') (Rep.res (resBaseHom k k' K) M)) 1),
        phiAt (k := k') (K := K) (L := L') (baseChangeExt M x) h' = 0)
    (hinj : ∀ (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k' L']
        [IsGalois k' L'] (hLL : L ≤ L'),
        Function.Injective (fun y : extH (classesK k' L) 2 => inflCIn (k := k') hLL y))
    (h : extH (Rep.res (galRes k' K L) (Rep.res (resBaseHom k k' K) M)) 1) :
    phiAt (k := k') (K := K) (L := L) (baseChangeExt M x) h = 0 := by
  classical
  let M0 : IntermediateField k Ω := L.restrictScalars k
  haveI hM0fin : FiniteDimensional k ↥M0 := inferInstanceAs (FiniteDimensional k ↥L)
  haveI hM0alg : Algebra.IsAlgebraic k ↥M0 := Algebra.IsAlgebraic.of_finite k ↥M0
  let N : IntermediateField k Ω := IntermediateField.normalClosure k ↥M0 Ω
  haveI hNfin : FiniteDimensional k ↥N := normalClosure.is_finiteDimensional k ↥M0 Ω
  have hM0N : M0 ≤ N := IntermediateField.le_normalClosure M0
  have hIN : IsNormalClosure k ↥M0 ↥N :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (fun z => IsAlgClosed.splits _)
  haveI hNnorm : Normal k ↥N := hIN.normal
  haveI hNint : Algebra.IsIntegral k ↥N := Algebra.IsIntegral.of_finite k ↥N
  haveI hNsep : Algebra.IsSeparable k ↥N := Algebra.IsSeparable.of_integral k ↥N
  have hNgal : IsGalois k ↥N := isGalois_iff.mpr ⟨hNsep, hNnorm⟩
  have hKN : (⊥ : IntermediateField K Ω).restrictScalars k ≤ N := by
    have h1 : (⊥ : IntermediateField K Ω).restrictScalars k ≤ L.restrictScalars k := by
      rw [IntermediateField.restrictScalars_le_iff]; exact bot_le
    exact h1.trans hM0N
  have hmemL' : ∀ t : K, algebraMap K Ω t ∈ (N : Set Ω) := fun t =>
    hKN (by rw [IntermediateField.mem_restrictScalars]; exact IntermediateField.mem_bot.mpr ⟨t, rfl⟩)
  let L' : IntermediateField K Ω := { N.toSubfield with algebraMap_mem' := hmemL' }
  haveI hL'fin : FiniteDimensional k L' := inferInstanceAs (FiniteDimensional k ↥N)
  haveI hL'gal : IsGalois k L' := inferInstanceAs (IsGalois k ↥N)
  haveI hL'cz : CharZero L' := inferInstanceAs (CharZero ↥N)
  haveI hL'fdq : FiniteDimensional ℚ L' := FiniteDimensional.trans ℚ k L'
  haveI hL'NF : NumberField L' := NumberField.mk
  haveI hSTkk' : IsScalarTower k k' L' := IsScalarTower.of_algebraMap_eq (fun y => by
    apply Subtype.ext
    rw [IsScalarTower.algebraMap_apply k K L', IsScalarTower.algebraMap_apply k' K L',
      IsScalarTower.algebraMap_apply k k' K])
  haveI hL'fdk' : FiniteDimensional k' L' := Module.Finite.of_restrictScalars_finite k k' L'
  haveI hL'gal' : IsGalois k' L' := IsGalois.tower_top_of_isGalois k k' L'
  have hLL : L ≤ L' := fun z hz => hM0N hz
  have hval : ∀ h' : extH (Rep.res (galRes k' K L') (Rep.res (resBaseHom k k' K) M)) 1,
      phiAt (k := k') (K := K) (L := L') (baseChangeExt M x) h' = 0 := hGal L' hLL
  have hcomp := phiAt_level_infl (k := k') L L' hLL (Rep.res (resBaseHom k k' K) M)
    (baseChangeExt M x) h
  have hzero : inflCIn (k := k') hLL
      (phiAt (k := k') (K := K) (L := L) (baseChangeExt M x) h) = 0 := by
    rw [hcomp]; exact hval _
  have hinflzero : inflCIn (k := k') hLL (0 : extH (classesK k' L) 2) = 0 := by
    simp only [inflCIn, inflC, extHMap, E6Util.extRes_zero, Abelian.Ext.zero_comp,
      Abelian.Ext.comp_zero]
  refine hinj L' hLL ?_
  change inflCIn (k := k') hLL (phiAt (k := k') (K := K) (L := L) (baseChangeExt M x) h)
      = inflCIn (k := k') hLL (0 : extH (classesK k' L) 2)
  rw [hzero, hinflzero]

/-- **The transfer of the vanishing to the base field `k'`.**  If the `(k, K)`-level values of the
class `x` vanish at every `k`-Galois level of `Ω` (`hx`), then the `(k', K)`-level values of the
base-changed class `baseChangeExt M x` vanish at every `k'`-Galois level: at levels that are Galois
over `k` as well this is case (i) (`phi1_value_kprime_zero_of_galoisLevel`), otherwise case (ii)
(`phi1_value_kprime_zero_of_level`), which uses the level-inflation injectivity `hinj`. -/
theorem phiOneVanishesIn_baseChangeExt
    [FiniteDimensional k k']
    (M : Rep Coeff (K ≃ₐ[k] K)) (x : Abelian.Ext M (classesK k K) 1)
    (hx : ∀ (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
        (h : extH (Rep.res (galRes k K L') M) 1), phiAt (k := k) (K := K) (L := L') x h = 0)
    (hinj : ∀ (L L' : IntermediateField K Ω) [NumberField L] [NumberField L']
        [FiniteDimensional k' L] [IsGalois k' L] [FiniteDimensional k' L'] [IsGalois k' L']
        (hLL : L ≤ L'), Function.Injective (fun y : extH (classesK k' L) 2 => inflCIn (k := k') hLL y)) :
    PhiOneVanishesIn (k := k') (K := K) Ω (baseChangeExt M x) := by
  intro L hNF hfd hgal h
  haveI : NumberField L := hNF
  haveI : FiniteDimensional k' L := hfd
  haveI : IsGalois k' L := hgal
  haveI hST : IsScalarTower k k' ↥L := IsScalarTower.of_algebraMap_eq (fun y => by
    apply Subtype.ext
    rw [IsScalarTower.algebraMap_apply k K ↥L, IsScalarTower.algebraMap_apply k' K ↥L,
      IsScalarTower.algebraMap_apply k k' K])
  by_cases hgalK : IsGalois k L
  · haveI : IsGalois k L := hgalK
    haveI : FiniteDimensional k L := Module.Finite.trans k' L
    exact phi1_value_kprime_zero_of_galoisLevel (k := k) (k' := k') (K := K) (L := L) M x
      (fun h' => hx L h') h
  · refine phi1_value_kprime_zero_of_level (k := k) (k' := k') (K := K) (Ω := Ω) M x L ?_ ?_ h
    · intro L' hNF' hFd hFd' hGalK' hGalK'' hLL h'
      haveI : NumberField L' := hNF'
      haveI : FiniteDimensional k L' := hFd
      haveI : FiniteDimensional k' L' := hFd'
      haveI : IsGalois k L' := hGalK'
      haveI : IsGalois k' L' := hGalK''
      haveI hST' : IsScalarTower k k' ↥L' := IsScalarTower.of_algebraMap_eq (fun y => by
        apply Subtype.ext
        rw [IsScalarTower.algebraMap_apply k K ↥L', IsScalarTower.algebraMap_apply k' K ↥L',
          IsScalarTower.algebraMap_apply k k' K])
      exact phi1_value_kprime_zero_of_galoisLevel (k := k) (k' := k') (K := K) (L := L') M x
        (fun h'' => hx L' h'') h'
    · intro L' hNF' hFd' hGalK'' hLL
      haveI : NumberField L' := hNF'
      haveI : FiniteDimensional k' L' := hFd'
      haveI : IsGalois k' L' := hGalK''
      exact hinj L L' hLL

end CaseTwo

end SylowLevel
end Work.SSGRoute
