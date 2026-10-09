import Mathlib
import Submission.Work.SSGRoute.PT.e1a_localComparison_bricks
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# (i) `PhiE`-compat: the connecting class of the canonical presentation commutes with restriction

`Work.SSGRoute.freeCoverSES X` is the canonical presentation of a representation `X`.  Applied to
the *third* term it gives the connecting class `PhiE`, the `Ext`-side map of the `E1c` dictionary:
`PhiE_X : Ext⁰(kernel (freeCover X), Z) → Ext¹(X, Z)`, `w ↦ extClass_X.comp w`.

For a group homomorphism `φ : H →* G` and `F := Rep.resFunctor φ`, the two presentations
`freeCoverSES (F X)` and `(freeCoverSES X).map F` of the same restricted module are compared by
`Work.SSGRoute.PT.freeCoverSES_res_comparison` (and
`Work.SSGRoute.SSGStage.extClass_freeCoverSES_res_comparison`, which records that the connecting
classes agree).  The present module upgrades that statement to the `PhiE`-level, which is the "only
genuinely new rule" of `PT/NOTE_e1aChainC_localComparison.md` §10.2:

    F.mapExtAddHom (PhiE_X w) = PhiE_{F X} (mk₀ Φ.τ₁ ∘ F.mapExtAddHom w).

Indeed both sides are the *same* element: the transported connecting class, composed with the
transported degree-zero class.  The mathematical content is exactly the compatibility of the two
canonical covers; the proof is the two rules of `Ext.mapExactFunctor`
(`mapExactFunctor_comp`, `mapExactFunctor_mk₀`) together with
`extClass_freeCoverSES_res_comparison`.

**Typing trap (recorded).**  `ShortComplex.map` produces a *new* short complex whose first object is
`F.obj S.X₁`; the two `Ext`-objects `((freeCoverSES X).map F).X₁` and
`F.obj (kernel (freeCover X))` are definitionally equal but **not** syntactically, and the `rw`
tactic re-elaborates its goal at `implicit` transparency, where the two do *not* match.  The proof
below therefore avoids `rw` at the two places where the comparison `Φ.τ₁` meets the transported
degree-zero class, using `congrArg` (elaborated at default transparency) instead.
-/

set_option maxHeartbeats 800000

namespace Work.SSGRoute.PT

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt

noncomputable section

variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]

/-- **The `Ext`-side map of the canonical presentation**, with an arbitrary coefficient `Z`:
`PhiE_X = extClass_X.precomp Z`, the general form of `E1cGeneric.PhiE` (which is the case
`Z = unitsK`). -/
noncomputable def PhiEgen (R Z : Rep.{0} SSGRoute.PTExt.Coeff G) :
    CategoryTheory.Abelian.Ext (Limits.kernel (Work.SSGRoute.freeCover R)) Z 0 →+
      CategoryTheory.Abelian.Ext R Z 1 :=
  (Work.SSGRoute.freeCoverSES_shortExact R).extClass.precomp Z (by norm_num : 1 + 0 = 1)

@[simp] theorem PhiEgen_apply (R Z : Rep.{0} SSGRoute.PTExt.Coeff G)
    (w : CategoryTheory.Abelian.Ext (Limits.kernel (Work.SSGRoute.freeCover R)) Z 0) :
    PhiEgen R Z w =
      (Work.SSGRoute.freeCoverSES_shortExact R).extClass.comp w (by norm_num : 1 + 0 = 1) :=
  rfl

/-- **(i) `PhiE`-compat.**  For `φ : H →* G`, `F = Rep.resFunctor φ` and representations
`X Z : Rep Coeff G`, there is a comparison `Φ` of the two canonical presentations of `F X` (given
by `freeCoverSES_res_comparison`: `Φ.τ₂ = freeCoverCompat φ X`, `Φ.τ₃ = 𝟙`) such that the
transported `PhiE`-map is the `PhiE`-map of the transported degree-zero class:

    F.mapExtAddHom (PhiE_X w) = PhiE_{F X} (mk₀ Φ.τ₁ ∘ F.mapExtAddHom w).

This is the `PhiE`-generator step of the localisation comparison
(`PT/NOTE_e1aChainC_localComparison.md` §11.1 (i), §10.2). -/
theorem PhiEgen_res_compat (φ : H →* G) (X Z : Rep.{0} SSGRoute.PTExt.Coeff G) :
    ∃ Φ : CategoryTheory.ShortComplex.Hom (Work.SSGRoute.freeCoverSES (Rep.res φ X))
        ((Work.SSGRoute.freeCoverSES X).map (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ)),
      Φ.τ₂ = Work.SSGRoute.PT.freeCoverCompat φ X ∧
        Φ.τ₃ = CategoryTheory.CategoryStruct.id (Rep.res φ X) ∧
        ∀ w : CategoryTheory.Abelian.Ext (Limits.kernel (Work.SSGRoute.freeCover X)) Z 0,
          (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom X Z 1 (PhiEgen X Z w) =
            PhiEgen (Rep.res φ X)
              ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).obj Z)
              (CategoryTheory.Abelian.Ext.comp
                (CategoryTheory.Abelian.Ext.mk₀ Φ.τ₁)
                ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom
                  (Limits.kernel (Work.SSGRoute.freeCover X)) Z 0 w)
                (zero_add 0)) := by
  classical
  obtain ⟨Φ, h2, h3, hclass⟩ :=
    Work.SSGRoute.SSGStage.extClass_freeCoverSES_res_comparison φ X
  refine ⟨Φ, h2, h3, fun w => ?_⟩
  have h1c : 1 + 0 = 1 := by norm_num
  have h0c : 0 + 0 = 0 := by norm_num
  have h2c : 0 + 1 = 1 := by norm_num
  have hA : (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom X
        (Limits.kernel (Work.SSGRoute.freeCover X)) 1
        (Work.SSGRoute.freeCoverSES_shortExact X).extClass
      = (Work.SSGRoute.freeCoverSES_shortExact (Rep.res φ X)).extClass.comp
          (CategoryTheory.Abelian.Ext.mk₀ Φ.τ₁) h2c := by
    rw [CategoryTheory.Functor.mapExtAddHom_apply]
    exact hclass.symm
  have hmain :
      (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom X Z 1
          ((Work.SSGRoute.freeCoverSES_shortExact X).extClass.comp w h1c)
        = (Work.SSGRoute.freeCoverSES_shortExact (Rep.res φ X)).extClass.comp
            ((CategoryTheory.Abelian.Ext.mk₀ Φ.τ₁).comp
              ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom
                (Limits.kernel (Work.SSGRoute.freeCover X)) Z 0 w) h0c) h1c := by
    calc
      (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom X Z 1
          ((Work.SSGRoute.freeCoverSES_shortExact X).extClass.comp w h1c)
          = ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom X
                (Limits.kernel (Work.SSGRoute.freeCover X)) 1
                (Work.SSGRoute.freeCoverSES_shortExact X).extClass).comp
              ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom
                (Limits.kernel (Work.SSGRoute.freeCover X)) Z 0 w) h1c := by
            rw [CategoryTheory.Functor.mapExtAddHom_apply,
              CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
              CategoryTheory.Functor.mapExtAddHom_apply]
            rfl
        _ = ((Work.SSGRoute.freeCoverSES_shortExact (Rep.res φ X)).extClass.comp
                (CategoryTheory.Abelian.Ext.mk₀ Φ.τ₁) h2c).comp
              ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom
                (Limits.kernel (Work.SSGRoute.freeCover X)) Z 0 w) h1c := by
            exact congrArg (fun z => z.comp
              ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom
                (Limits.kernel (Work.SSGRoute.freeCover X)) Z 0 w) h1c) hA
        _ = (Work.SSGRoute.freeCoverSES_shortExact (Rep.res φ X)).extClass.comp
              ((CategoryTheory.Abelian.Ext.mk₀ Φ.τ₁).comp
                ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom
                  (Limits.kernel (Work.SSGRoute.freeCover X)) Z 0 w) h0c) h1c :=
            CategoryTheory.Abelian.Ext.comp_assoc
              ((Work.SSGRoute.freeCoverSES_shortExact (Rep.res φ X)).extClass)
              (CategoryTheory.Abelian.Ext.mk₀ Φ.τ₁)
              ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ).mapExtAddHom
                (Limits.kernel (Work.SSGRoute.freeCover X)) Z 0 w)
              h2c h0c (by norm_num : 1 + 0 + 0 = 1)
  exact hmain

end

end Work.SSGRoute.PT
