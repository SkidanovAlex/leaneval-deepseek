import Mathlib
import Submission.Work.SSGRoute.ext_corestriction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory Limits

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

universe u₁ v₁

/-- **Naturality of a natural transformation `θ : 𝟭 C ⟶ F` on `Ext`.**

This is the mirror image of `Work.SSGRoute.ext_mapExactFunctor_naturality_aux` (which handles a
natural transformation `F ⟶ 𝟭`): for an additive endofunctor `F` of an abelian category with
enough projectives which preserves finite limits and finite colimits, and any natural
transformation `θ : 𝟭 C ⟶ F`, one has
`x.comp (mk₀ (θ.app Y)) (add_zero n) = (mk₀ (θ.app X)).comp (x.mapExactFunctor F) (zero_add n)`.
It is the naturality of the adjunction unit `η : 𝟭 ⟶ Res ⋙ Coind` on `Ext`. -/
theorem ext_mapExactFunctor_naturality_unit_aux
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{0} C] [EnoughProjectives C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (θ : NatTrans (𝟭 C) F) :
    ∀ (n : ℕ) (X Y : C) (x : Abelian.Ext X Y n),
      x.comp (Abelian.Ext.mk₀ (θ.app Y)) (add_zero n) =
        (Abelian.Ext.mk₀ (θ.app X)).comp (x.mapExactFunctor F) (zero_add n) := by
  intro n
  induction n with
  | zero =>
      intro X Y x
      obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective X Y).2 x
      simp only [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
      rw [← θ.naturality f]
      rfl
  | succ n ih =>
      intro X Y x
      obtain ⟨P⟩ := EnoughProjectives.presentation X
      let S : ShortComplex C := ShortComplex.mk (kernel.ι P.f) P.f (kernel.condition P.f)
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel P.f }
      haveI : Projective S.X₂ := P.projective
      haveI : Subsingleton (Abelian.Ext S.X₂ Y (n + 1)) :=
        Abelian.Ext.subsingleton_of_projective S.X₂ Y n
      have hn₀ : 1 + n = n + 1 := Nat.add_comm 1 n
      have hx0 : (Abelian.Ext.mk₀ S.g).comp x (zero_add (n + 1)) = 0 := Subsingleton.elim _ _
      obtain ⟨w, hw⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS Y x hx0 (hn₀)
      rw [← hw]
      have hcomp := Abelian.Ext.mapExactFunctor_comp F hS.extClass w (hn₀)
      refine Eq.trans (b := hS.extClass.comp
        (w.comp (Abelian.Ext.mk₀ (θ.app Y)) (add_zero n)) hn₀) ?_ ?_
      · exact Abelian.Ext.comp_assoc_of_third_deg_zero hS.extClass w
          (Abelian.Ext.mk₀ (θ.app Y)) hn₀
      refine Eq.trans (b := hS.extClass.comp
        ((Abelian.Ext.mk₀ (θ.app S.X₁)).comp (Abelian.Ext.mapExactFunctor F w) (zero_add n))
        hn₀) ?_ ?_
      · exact congrArg (fun z => hS.extClass.comp z hn₀) (ih S.X₁ Y w)
      refine Eq.trans (b := (hS.extClass.comp (Abelian.Ext.mk₀ (θ.app S.X₁)) (add_zero 1)).comp
        (Abelian.Ext.mapExactFunctor F w) hn₀) ?_ ?_
      · exact (Abelian.Ext.comp_assoc hS.extClass (Abelian.Ext.mk₀ (θ.app S.X₁))
          (Abelian.Ext.mapExactFunctor F w) (add_zero 1) (zero_add n) (by omega)).symm
      refine Eq.trans (b := ((Abelian.Ext.mk₀ (θ.app X)).comp
        ((hS.map_of_exact F).extClass) (zero_add 1)).comp
        (Abelian.Ext.mapExactFunctor F w) hn₀) ?_ ?_
      · exact congrArg (fun z => z.comp (Abelian.Ext.mapExactFunctor F w) hn₀)
          (ShortComplex.ShortExact.extClass_naturality (hS.map_of_exact (𝟭 C))
            (hS.map_of_exact F) (S.mapNatTrans θ))
      refine Eq.trans (b := ((Abelian.Ext.mk₀ (θ.app X)).comp
        (hS.extClass.mapExactFunctor F) (zero_add 1)).comp
        (Abelian.Ext.mapExactFunctor F w) hn₀) ?_ ?_
      · exact congrArg (fun z => ((Abelian.Ext.mk₀ (θ.app X)).comp z (zero_add 1)).comp
          (Abelian.Ext.mapExactFunctor F w) hn₀)
          (Abelian.Ext.mapExactFunctor_extClass F hS).symm
      refine Eq.trans (b := (Abelian.Ext.mk₀ (θ.app X)).comp
        ((hS.extClass.mapExactFunctor F).comp (Abelian.Ext.mapExactFunctor F w) hn₀)
        (zero_add (n + 1))) ?_ ?_
      · exact Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (θ.app X))
          (hS.extClass.mapExactFunctor F) (Abelian.Ext.mapExactFunctor F w)
          (zero_add 1) hn₀ (by omega)
      · exact congrArg (fun z => (Abelian.Ext.mk₀ (θ.app X)).comp z (zero_add (n + 1)))
          hcomp.symm

/-- **Mirror projection formula** for corestriction: `x ∘ cor u = cor (res x ∘ u)`.

Route: with `Work.SSGRoute.extCor_apply`, `cor u = mk₀(unit) ∘ Coind(u) ∘ mk₀(coindTrace)`.
The key input is naturality of the adjunction unit `η : 𝟭 ⟶ Rep.resFunctor S.subtype ⋙
Rep.coindFunctor Coeff S.subtype` on `Ext`: `x.comp (mk₀ (η.app X)) = (mk₀ (η.app (unitRep G))).comp
((x.mapExactFunctor (Rep.resFunctor S.subtype ⋙ Rep.coindFunctor Coeff S.subtype)))`.
This is the general-natural-transformation version of `Work.SSGRoute.ext_mapExactFunctor_naturality_aux`
(same induction on `n`, using `ShortComplex.ShortExact.extClass_naturality` for `S.mapNatTrans θ`);
`Abelian.Ext.mapExactFunctor_comp` then distributes `Coind` over the composite `res x ≫ u`, and the
composites re-associate with `Abelian.Ext.comp_assoc`.  Note `Abelian.Ext.mapExactFunctor_mk₀` gives
`extRes S.subtype (mk₀ x) = mk₀ (Rep.resMap S.subtype x)`. -/
theorem comp_extCor {G : Type} [Group G] [Fintype G] (S : Subgroup G)
    [DecidableRel (QuotientGroup.rightRel S)] [Fintype (G ⧸ S)]
    {X Y : Rep SSGRoute.PTExt.Coeff G} {s n : Nat} (x : SSGRoute.PTExt.extH X s)
    (u : CategoryTheory.Abelian.Ext (Rep.res S.subtype X) (Rep.res S.subtype Y) n) :
    x.comp (Work.SSGRoute.extCor S X Y n u) rfl =
      Work.SSGRoute.extCor S (SSGRoute.PTExt.unitRep G) Y (s + n)
        ((SSGRoute.PTExt.extRes S.subtype x).comp u rfl) := by
  -- Naturality of the adjunction unit `η : 𝟭 ⟶ Res ⋙ Coind` on `Ext`.
  have hnat : x.comp
        (Abelian.Ext.mk₀ ((Rep.resCoindAdjunction Coeff S.subtype).unit.app X)) (add_zero s)
      = (Abelian.Ext.mk₀ ((Rep.resCoindAdjunction Coeff S.subtype).unit.app (unitRep G))).comp
        (x.mapExactFunctor (Rep.resFunctor S.subtype ⋙ Rep.coindFunctor Coeff S.subtype))
        (zero_add s) :=
    ext_mapExactFunctor_naturality_unit_aux (C := Rep Coeff G)
      (Rep.resFunctor S.subtype ⋙ Rep.coindFunctor Coeff S.subtype)
      (Rep.resCoindAdjunction Coeff S.subtype).unit s (unitRep G) X x
  -- `Coind ∘ Res` is the composite functor.
  have hres : (SSGRoute.PTExt.extRes S.subtype x).mapExactFunctor
        (Rep.coindFunctor Coeff S.subtype)
      = x.mapExactFunctor (Rep.resFunctor S.subtype ⋙ Rep.coindFunctor Coeff S.subtype) :=
    ext_mapExactFunctor_comp_functor_aux (C := Rep Coeff G) (D := Rep Coeff S)
      (E := Rep Coeff G) (Rep.resFunctor S.subtype) (Rep.coindFunctor Coeff S.subtype)
      s (unitRep G) X x
  -- Unfold both corestrictions: `cor u = mk₀(unit) ∘ Coind(u) ∘ mk₀(coindTrace)`.
  rw [Work.SSGRoute.extCor_apply]
  rw [Work.SSGRoute.extCor_apply]
  -- `Coind` distributes over the composite `res x ∘ u`.
  rw [Abelian.Ext.mapExactFunctor_comp]
  rw [hres]
  -- Left hand side: re-associate and apply the naturality of the unit.
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero
    (Abelian.Ext.mk₀ ((Rep.resCoindAdjunction Coeff S.subtype).unit.app X))
    (u.mapExactFunctor (Rep.coindFunctor Coeff S.subtype))
    (Abelian.Ext.mk₀ (coindTrace S Y)) (zero_add n)]
  rw [← Abelian.Ext.comp_assoc_of_second_deg_zero x
    (Abelian.Ext.mk₀ ((Rep.resCoindAdjunction Coeff S.subtype).unit.app X))
    ((u.mapExactFunctor (Rep.coindFunctor Coeff S.subtype)).comp
      (Abelian.Ext.mk₀ (coindTrace S Y)) (add_zero n)) rfl]
  rw [hnat]
  rw [Abelian.Ext.comp_assoc
    (Abelian.Ext.mk₀ ((Rep.resCoindAdjunction Coeff S.subtype).unit.app (unitRep G)))
    (x.mapExactFunctor (Rep.resFunctor S.subtype ⋙ Rep.coindFunctor Coeff S.subtype))
    ((u.mapExactFunctor (Rep.coindFunctor Coeff S.subtype)).comp
      (Abelian.Ext.mk₀ (coindTrace S Y)) (add_zero n))
    (zero_add s) rfl (by omega)]
  -- Right hand side: re-associate to the same normal form.
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero
    (Abelian.Ext.mk₀ ((Rep.resCoindAdjunction Coeff S.subtype).unit.app (unitRep G)))
    ((x.mapExactFunctor (Rep.resFunctor S.subtype ⋙ Rep.coindFunctor Coeff S.subtype)).comp
      (u.mapExactFunctor (Rep.coindFunctor Coeff S.subtype)) rfl)
    (Abelian.Ext.mk₀ (coindTrace S Y)) (zero_add (s + n))]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero
    (x.mapExactFunctor (Rep.resFunctor S.subtype ⋙ Rep.coindFunctor Coeff S.subtype))
    (u.mapExactFunctor (Rep.coindFunctor Coeff S.subtype))
    (Abelian.Ext.mk₀ (coindTrace S Y)) rfl]

end Work.SSGRoute
