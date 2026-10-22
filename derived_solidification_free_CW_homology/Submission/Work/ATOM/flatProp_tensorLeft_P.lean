import Mathlib
import Submission.Work.ATOM.Defs

namespace Work.ATOM

open CategoryTheory Limits

universe w w' u₁ u₂ v₁ v₂

/-!
# Retracts of limit-preserving functors

`PreservesLimit` (hence `PreservesFiniteLimits`) is closed under retracts of functors: if
`G : C ⥤ D` is a retract of `F : C ⥤ D` (natural transformations `i : G ⟶ F`, `r : F ⟶ G`
with `i ≫ r = 𝟙 G`) and `F` preserves limits of shape `J`, then so does `G`.

The proof is the standard one: for a limit cone `c` over `K : J ⥤ C`, any cone `s` over
`K ⋙ G` is pushed forward along `i` to a cone `s'` over `K ⋙ F`, the lift of `s'` in
`F.mapCone c` is pulled back along `r`, and `i ≫ r = 𝟙` gives both the factorization and
the uniqueness.  This is the categorical form of "a retract of a flat module is flat".
-/

/-- A retract of a functor that preserves limits of a given shape also preserves them. -/
lemma preservesLimit_of_retract {J : Type w} [Category.{w'} J] {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {K : J ⥤ C} {F G : C ⥤ D} (h : Retract G F)
    [PreservesLimit K F] : PreservesLimit K G where
  preserves {c} hc := by
    have hF : IsLimit (F.mapCone c) := isLimitOfPreserves F hc
    have hi : ∀ X : C, h.i.app X ≫ h.r.app X = 𝟙 (G.obj X) := fun X => by
      rw [← NatTrans.comp_app, h.retract, NatTrans.id_app]
    have hπ : ∀ (s : Cone (K ⋙ G)) (j : J),
        ((Cone.postcompose (Functor.whiskerLeft K h.i)).obj s).π.app j
          = s.π.app j ≫ h.i.app (K.obj j) := fun s j => by
      rw [Cone.postcompose_obj_π, NatTrans.comp_app, Functor.whiskerLeft_app]
    let L : (s : Cone (K ⋙ G)) → (s.pt ⟶ (G.mapCone c).pt) :=
      fun s => hF.lift ((Cone.postcompose (Functor.whiskerLeft K h.i)).obj s) ≫ h.r.app c.pt
    refine ⟨{ lift := L, fac := fun s j => ?_, uniq := fun s m hm => ?_ }⟩
    · have hrj : F.map (c.π.app j) ≫ h.r.app (K.obj j) = h.r.app c.pt ≫ G.map (c.π.app j) :=
        h.r.naturality (c.π.app j)
      have hFfac : hF.lift ((Cone.postcompose (Functor.whiskerLeft K h.i)).obj s) ≫ F.map (c.π.app j)
          = s.π.app j ≫ h.i.app (K.obj j) := by
        have hh := hF.fac ((Cone.postcompose (Functor.whiskerLeft K h.i)).obj s) j
        rwa [Functor.mapCone_π_app, hπ s j] at hh
      rw [Functor.mapCone_π_app, Category.assoc, ← hrj, ← Category.assoc, hFfac, Category.assoc]
      simp [hi]
    · have key : m ≫ h.i.app c.pt
          = hF.lift ((Cone.postcompose (Functor.whiskerLeft K h.i)).obj s) := by
        refine hF.uniq ((Cone.postcompose (Functor.whiskerLeft K h.i)).obj s) (m ≫ h.i.app c.pt) ?_
        intro j
        have hij : G.map (c.π.app j) ≫ h.i.app (K.obj j) = h.i.app c.pt ≫ F.map (c.π.app j) :=
          h.i.naturality (c.π.app j)
        have hmj : m ≫ G.map (c.π.app j) = s.π.app j := by
          rw [← Functor.mapCone_π_app G c j]; exact hm j
        rw [Functor.mapCone_π_app, Category.assoc, ← hij, ← Category.assoc, hmj, hπ s j]
      change m = hF.lift ((Cone.postcompose (Functor.whiskerLeft K h.i)).obj s) ≫ h.r.app c.pt
      rw [← key, Category.assoc, hi c.pt]
      exact (Category.comp_id m).symm

/-- A retract of a left exact functor (in the sense of preserving finite limits)
is left exact. -/
lemma preservesFiniteLimits_of_retract {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F G : C ⥤ D} (h : Retract G F) [hinst : PreservesFiniteLimits F] :
    PreservesFiniteLimits G where
  preservesFiniteLimits _ _ _ :=
    { preservesLimit := fun {K} => preservesLimit_of_retract (K := K) h }

open Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed in
/-- `FlatProp` for the free module on `ℕ∪∞` implies that `tensorLeft P` is left exact:
`P` is a retract of `ℤ[ℕ∪∞]`. -/
theorem flatProp_tensorLeft_P (h : Submission.Blueprint.FlatProp) :
    CategoryTheory.Limits.PreservesFiniteLimits
      (CategoryTheory.MonoidalCategory.tensorLeft LightCondensed.P) := by
  have hF : PreservesFiniteLimits
      (tensorLeft ((LightCondensed.free ℤ).obj (LightProfinite.toCondensed (ℕ∪{∞})))) := h _
  exact preservesFiniteLimits_of_retract
    (Retract.map LightCondensed.P_retract (curriedTensor LightCondAb)) (hinst := hF)

end Work.ATOM
