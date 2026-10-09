import Mathlib
import Submission.Work.SSGRoute.ext_corestriction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of `Ext.mapExactFunctor` in a natural transformation of exact functors

`Work.SSGRoute.ext_mapExactFunctor_naturality_aux`
(`Submission/Work/SSGRoute/ext_corestriction.lean`) proves the naturality of
`CategoryTheory.Abelian.Ext.mapExactFunctor F` with respect to a natural transformation `θ : F ⟹ 𝟭`
of an endofunctor.  The Sylow step `X4`/`X5` of E7b needs the general form, for a natural
transformation `θ : F ⟹ G` between two exact functors `F G : C ⥤ D`:

`(x.mapExactFunctor F) ≫ mk₀ (θ.app Y) = mk₀ (θ.app X) ≫ (x.mapExactFunctor G)`.

Instances: `θ = η` (the unit `𝟭 ⟹ Coind ⋙ Res` of the restriction/coinduction adjunction) gives the
"projection formula" `x ∘ cor y = cor (res x ∘ y)`; `θ` = the Mackey isomorphism
`Coind_S ⋙ Res_f ≅ Res_g ⋙ Coind_{S'}` of `Submission/Work/SSGRoute/coind_res_mackey.lean` gives
the Mackey formula `res_f (cor_S z) = cor_{S'} (res_g z)`.

The proof is the same induction on the degree as `ext_mapExactFunctor_naturality_aux`; the successor
step uses `ShortComplex.ShortExact.extClass_naturality` for `S.mapNatTrans θ`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Work.SSGRoute

open CategoryTheory Limits

universe u₁ u₂ v₁ v₂

/-- **Naturality of `Ext.mapExactFunctor` in a natural transformation `F ⟹ G` of exact
functors.** -/
theorem mapExactFunctor_natTrans_naturality
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{0} C] [EnoughProjectives C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{0} D]
    (F G : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (θ : F ⟶ G) :
    ∀ (n : ℕ) (X Y : C) (x : Abelian.Ext X Y n),
      (x.mapExactFunctor F).comp (Abelian.Ext.mk₀ (θ.app Y)) (add_zero n) =
        (Abelian.Ext.mk₀ (θ.app X)).comp (x.mapExactFunctor G) (zero_add n) := by
  intro n
  induction n with
  | zero =>
      intro X Y x
      obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective X Y).2 x
      simp only [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
      rw [θ.naturality f]
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
      rw [← hw, Abelian.Ext.mapExactFunctor_comp F hS.extClass w hn₀,
        Abelian.Ext.mapExactFunctor_comp G hS.extClass w hn₀]
      have hassoc1 := Abelian.Ext.comp_assoc_of_third_deg_zero
        (Abelian.Ext.mapExactFunctor F hS.extClass) (Abelian.Ext.mapExactFunctor F w)
        (Abelian.Ext.mk₀ (θ.app Y)) hn₀
      have hih := ih S.X₁ Y w
      have hA : (Abelian.Ext.mapExactFunctor F hS.extClass) = (hS.map_of_exact F).extClass :=
        Abelian.Ext.mapExactFunctor_extClass F hS
      have hB : (Abelian.Ext.mapExactFunctor G hS.extClass) = (hS.map_of_exact G).extClass :=
        Abelian.Ext.mapExactFunctor_extClass G hS
      have hnat : ((hS.map_of_exact F).extClass).comp
            (Abelian.Ext.mk₀ (θ.app S.X₁)) (add_zero 1)
          = (Abelian.Ext.mk₀ (θ.app X)).comp
            ((hS.map_of_exact G).extClass) (zero_add 1) :=
        ShortComplex.ShortExact.extClass_naturality (hS.map_of_exact F)
          (hS.map_of_exact G) (S.mapNatTrans θ)
      have hassoc2 : (hS.map_of_exact F).extClass.comp
            ((Abelian.Ext.mk₀ (θ.app S.X₁)).comp
              (Abelian.Ext.mapExactFunctor G w) (zero_add n)) hn₀
          = ((hS.map_of_exact F).extClass.comp
              (Abelian.Ext.mk₀ (θ.app S.X₁)) (add_zero 1)).comp
              (Abelian.Ext.mapExactFunctor G w) hn₀ :=
        (Abelian.Ext.comp_assoc_of_second_deg_zero (hS.map_of_exact F).extClass
          (Abelian.Ext.mk₀ (θ.app S.X₁)) (Abelian.Ext.mapExactFunctor G w) hn₀).symm
      have hassoc3 : ((Abelian.Ext.mk₀ (θ.app X)).comp
            (Abelian.Ext.mapExactFunctor G hS.extClass) (zero_add 1)).comp
            (Abelian.Ext.mapExactFunctor G w) hn₀
          = (Abelian.Ext.mk₀ (θ.app X)).comp
            ((Abelian.Ext.mapExactFunctor G hS.extClass).comp
              (Abelian.Ext.mapExactFunctor G w) hn₀) (zero_add (n + 1)) :=
        Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (θ.app X))
          (Abelian.Ext.mapExactFunctor G hS.extClass) (Abelian.Ext.mapExactFunctor G w)
          (zero_add 1) hn₀ (by omega)
      have step1 : ((Abelian.Ext.mapExactFunctor F hS.extClass).comp
              (Abelian.Ext.mapExactFunctor F w) hn₀).comp
            (Abelian.Ext.mk₀ (θ.app Y)) (add_zero (n + 1))
          = (Abelian.Ext.mapExactFunctor F hS.extClass).comp
              ((Abelian.Ext.mapExactFunctor F w).comp
                (Abelian.Ext.mk₀ (θ.app Y)) (add_zero n)) hn₀ := hassoc1
      have step2 : (Abelian.Ext.mapExactFunctor F hS.extClass).comp
              ((Abelian.Ext.mapExactFunctor F w).comp
                (Abelian.Ext.mk₀ (θ.app Y)) (add_zero n)) hn₀
          = (Abelian.Ext.mapExactFunctor F hS.extClass).comp
              ((Abelian.Ext.mk₀ (θ.app S.X₁)).comp
                (Abelian.Ext.mapExactFunctor G w) (zero_add n)) hn₀ := by rw [hih]
      have step3 : (Abelian.Ext.mapExactFunctor F hS.extClass).comp
              ((Abelian.Ext.mk₀ (θ.app S.X₁)).comp
                (Abelian.Ext.mapExactFunctor G w) (zero_add n)) hn₀
          = (hS.map_of_exact F).extClass.comp
              ((Abelian.Ext.mk₀ (θ.app S.X₁)).comp
                (Abelian.Ext.mapExactFunctor G w) (zero_add n)) hn₀ := by rw [hA]
      have step5 : ((hS.map_of_exact F).extClass.comp
              (Abelian.Ext.mk₀ (θ.app S.X₁)) (add_zero 1)).comp
              (Abelian.Ext.mapExactFunctor G w) hn₀
          = ((Abelian.Ext.mk₀ (θ.app X)).comp
              ((hS.map_of_exact G).extClass) (zero_add 1)).comp
              (Abelian.Ext.mapExactFunctor G w) hn₀ := by rw [hnat]
      have step6 : ((Abelian.Ext.mk₀ (θ.app X)).comp
              ((hS.map_of_exact G).extClass) (zero_add 1)).comp
              (Abelian.Ext.mapExactFunctor G w) hn₀
          = ((Abelian.Ext.mk₀ (θ.app X)).comp
              (Abelian.Ext.mapExactFunctor G hS.extClass) (zero_add 1)).comp
              (Abelian.Ext.mapExactFunctor G w) hn₀ := by rw [← hB]
      exact step1.trans (step2.trans (step3.trans (hassoc2.trans (step5.trans
        (step6.trans hassoc3)))))

end Work.SSGRoute
