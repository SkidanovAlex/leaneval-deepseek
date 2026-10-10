import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.E1aClean.unitsPushTarget
import Submission.Work.SSGRoute.ExtChain.exists_khLift_of_extToIdeles_eq_zero
import Submission.Work.SSGRoute.ExtChain.himgLeafCore
import Submission.Work.SSGRoute.ExtChain.resH2_zpowers_e1aChainH_eq_zero_of_extRes_zpowers_eq_zero
import Submission.Work.SSGRoute.ExtChain.shift_symm_extToIdeles_eq_zero_gen
import Submission.Work.SSGRoute.PTdualControl.exists_invariant_extension_of_resH1_e1cMap_eq_zero_inf
import Submission.Work.SSGRoute.extToIdeles_eq_zero_iff_extLoc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lifting a degree-`0` `Ext`-map through the canonical cover

Let `R` be a representation of `G = Gal(K/k)`, `0 → R₁ → F → R → 0` the canonical presentation
of `R` by a free representation `F` (`Work.SSGRoute.freeCoverSES`), and let
`ΦE : Ext⁰_G(R₁, Kˣ) → Ext¹_G(R, Kˣ)` be the connecting map of that presentation
(`Work.SSGRoute.ExtChain.PhiE`).

The main lemma `exists_lift_of_extRes_comp_eq_zero` is the following statement.  Let `D ≤ G`,
let `M` be a `D`-representation and `c : Kˣ|_D ⟶ M` a morphism of `D`-representations.  If the
obstruction

`extRes_D (ΦE w) ∘ c ∈ Ext¹_D(R, M)`

vanishes, then the `D`-map `c ∘ addEquiv₀ w : R₁|_D ⟶ M` extends to a `D`-map `F|_D ⟶ M`.

This is exactly the "splitting criterion" for the extension class of the canonical presentation:
`Ext¹_D(R, M)` carries the extension `0 → M → F|_D ⊗_{R₁} M → R → 0`, and its vanishing is
equivalent to the existence of a lift of `c ∘ addEquiv₀ w` through the syzygy inclusion.  The proof
uses the contravariant long exact sequence of `0 → R₁ → F → R → 0`
(`CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁`) over the group `D`, together with the
compatibility of the connecting map `ΦE` with restriction (`mapExactFunctor_extClass`).

## Main statements

* `ssg_ext_addEquiv₀_comp_zero` — `addEquiv₀` of a degree-`0` composite is the composite of the
  corresponding morphisms;
* `ssg_addEquiv₀_mk₀` — `addEquiv₀ (mk₀ f) = f`;
* `ssg_ext_addEquiv₀_mapExt` — `addEquiv₀` commutes with an exact functor;
* `exists_lift_of_extRes_comp_eq_zero` — the requested lifting statement.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

noncomputable section

/-- `addEquiv₀` of a degree-`0` composite of `Ext`-classes is the composite of the corresponding
morphisms. -/
theorem ssg_ext_addEquiv₀_comp_zero {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y Z : C} (α : Abelian.Ext X Y 0) (β : Abelian.Ext Y Z 0) :
    Abelian.Ext.addEquiv₀ (α.comp β (zero_add 0))
      = Abelian.Ext.addEquiv₀ α ≫ Abelian.Ext.addEquiv₀ β := by
  apply (Abelian.Ext.mk₀_bijective X Z).1
  rw [Abelian.Ext.mk₀_addEquiv₀_apply]
  conv_lhs => rw [← Abelian.Ext.mk₀_addEquiv₀_apply α, ← Abelian.Ext.mk₀_addEquiv₀_apply β]
  rw [Abelian.Ext.mk₀_comp_mk₀]

/-- `addEquiv₀` sends the Yoneda class of a morphism to that morphism. -/
theorem ssg_addEquiv₀_mk₀ {C : Type*} [Category C] [Abelian C] [HasExt C] {X Y : C} (f : X ⟶ Y) :
    Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ f) = f := by
  have h : Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ f)) = Abelian.Ext.mk₀ f := by
    rw [Abelian.Ext.mk₀_addEquiv₀_apply]
  exact (Abelian.Ext.mk₀_bijective X Y).1 h

/-- `addEquiv₀` commutes with an exact functor: the bijection `Ext⁰(X,Y) ≃ (X ⟶ Y)` is natural. -/
theorem ssg_ext_addEquiv₀_mapExt {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] [HasExt C] [HasExt D] (F : C ⥤ D) [F.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F] {X Y : C}
    (e : Abelian.Ext X Y 0) :
    Abelian.Ext.addEquiv₀ (F.mapExtAddHom X Y 0 e) = F.map (Abelian.Ext.addEquiv₀ e) := by
  rw [show F.mapExtAddHom X Y 0 e = Abelian.Ext.mapExactFunctor F e from rfl]
  rw [Abelian.Ext.mapExactFunctor₀]
  simp only [Function.comp_apply]
  rw [Abelian.Ext.homEquiv₀_symm_apply]
  have hmk : Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ (F.map (Abelian.Ext.homEquiv₀ e)))
      = F.map (Abelian.Ext.homEquiv₀ e) := by
    have h : Abelian.Ext.mk₀
        (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ (F.map (Abelian.Ext.homEquiv₀ e))))
        = Abelian.Ext.mk₀ (F.map (Abelian.Ext.homEquiv₀ e)) := by
      rw [Abelian.Ext.mk₀_addEquiv₀_apply]
    exact (Abelian.Ext.mk₀_bijective (F.obj X) (F.obj Y)).1 h
  rw [hmk]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem exists_lift_of_extRes_comp_eq_zero {k : Type} [Field k] [NumberField k] {Ω : Type}
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [NumberField K]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (D : Subgroup (K ≃ₐ[k] K)) (M : Rep.{0} SSGRoute.PTExt.Coeff ↥D)
    (c : Rep.res D.subtype (SSGRoute.PTExt.unitsK k K) ⟶ M)
    (w : CategoryTheory.Abelian.Ext.{0} (Work.SSGRoute.ExtChain.E1cR1 R)
      (SSGRoute.PTExt.unitsK k K) 0)
    (h : (SSGRoute.PTExt.extRes D.subtype
        (Work.SSGRoute.ExtChain.PhiE (k := k) (Ω := Ω) (K := K) R w)).comp
        (CategoryTheory.Abelian.Ext.mk₀ c) (add_zero 1) = 0) :
    ∃ Φ : Rep.res D.subtype (Work.SSGRoute.ExtChain.E1cF R) ⟶ M,
      ∀ x : (Work.SSGRoute.ExtChain.E1cR1 R).V,
        Rep.Hom.hom Φ (Work.SSGRoute.ExtChain.kappa R x)
          = Rep.Hom.hom c (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ w) x) := by
  -- the restriction functor and the canonical presentation of `R`
  let F : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ⥤ Rep.{0} SSGRoute.PTExt.Coeff ↥D :=
    Rep.resFunctor D.subtype
  have hS : (Work.SSGRoute.freeCoverSES R).ShortExact := Work.SSGRoute.freeCoverSES_shortExact R
  have hS' : ((Work.SSGRoute.freeCoverSES R).map F).ShortExact := hS.map_of_exact F
  -- the class `c ∘ addEquiv₀ w` at the level `D`, written through the canonical cover
  let x₁ : CategoryTheory.Abelian.Ext (F.obj (Work.SSGRoute.ExtChain.E1cR1 R)) M 0 :=
    (w.mapExactFunctor F).comp (CategoryTheory.Abelian.Ext.mk₀ c) (zero_add 0)
  -- its image under the connecting map of the presentation vanishes by hypothesis `h`
  have hx1 : hS'.extClass.comp x₁ (add_zero 1) = 0 := by
    change ((Work.SSGRoute.freeCoverSES_shortExact R).map_of_exact F).extClass.comp
      (((w.mapExactFunctor F).comp (CategoryTheory.Abelian.Ext.mk₀ c) (zero_add 0)))
      (add_zero 1) = 0
    rw [← Abelian.Ext.mapExactFunctor_extClass F (Work.SSGRoute.freeCoverSES_shortExact R)]
    rw [← Abelian.Ext.comp_assoc
        (Abelian.Ext.mapExactFunctor F (Work.SSGRoute.freeCoverSES_shortExact R).extClass)
        (Abelian.Ext.mapExactFunctor F w)
        (CategoryTheory.Abelian.Ext.mk₀ c) (add_zero 1) (zero_add 0)
        (by norm_num : 1 + 0 + 0 = 1)]
    rw [← Abelian.Ext.mapExactFunctor_comp F
        (Work.SSGRoute.freeCoverSES_shortExact R).extClass w (add_zero 1)]
    exact h
  -- the long exact sequence splits the map `c ∘ addEquiv₀ w` over the free cover
  obtain ⟨x₂, hx₂⟩ :=
    CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁ hS' M x₁ (add_zero 1) hx1
  refine ⟨CategoryTheory.Abelian.Ext.addEquiv₀ x₂, ?_⟩
  have hx1eq : CategoryTheory.Abelian.Ext.addEquiv₀ x₁
      = Rep.resMap D.subtype (CategoryTheory.Abelian.Ext.addEquiv₀ w) ≫ c := by
    change CategoryTheory.Abelian.Ext.addEquiv₀
      ((w.mapExactFunctor F).comp (CategoryTheory.Abelian.Ext.mk₀ c) (zero_add 0))
      = Rep.resMap D.subtype (CategoryTheory.Abelian.Ext.addEquiv₀ w) ≫ c
    rw [ssg_ext_addEquiv₀_comp_zero]
    rw [show w.mapExactFunctor F = F.mapExtAddHom (Work.SSGRoute.ExtChain.E1cR1 R)
      (SSGRoute.PTExt.unitsK k K) 0 w from rfl]
    rw [ssg_ext_addEquiv₀_mapExt, ssg_addEquiv₀_mk₀]
  -- the defining relation of `x₂`
  have hkey : ((Work.SSGRoute.freeCoverSES R).map F).f ≫
      CategoryTheory.Abelian.Ext.addEquiv₀ x₂ = CategoryTheory.Abelian.Ext.addEquiv₀ x₁ := by
    have hh := hx₂
    rw [← CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply x₂,
      CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
      ← CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply x₁] at hh
    exact (CategoryTheory.Abelian.Ext.mk₀_bijective _ _).1 hh
  intro x
  have h1 := congrArg
    (fun (m : ((Work.SSGRoute.freeCoverSES R).map F).X₁ ⟶ M) => Rep.Hom.hom m x) hkey
  rw [hx1eq] at h1
  simp only [Rep.comp_apply, ShortComplex.map_f] at h1 ⊢
  exact h1

end

end Work.SSGRoute.ExtChain
