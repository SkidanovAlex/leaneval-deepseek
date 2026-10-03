import Mathlib
import Submission.Work.OROneRel.Interface

/-!
# Injectivity of the canonical map `F(T) →* ⟨α | r⟩` is monotone in `T`

If `T ⊆ T'` and the canonical map `presentedGroupMap r T' : F(T') →* ⟨α | r⟩` is injective, then so
is `presentedGroupMap r T`.  The reason is that the inclusion of generating sets induces a
homomorphism `incl : F(T) →* F(T')`, which is injective because the map `F(T') →* F(T)` that sends
each generator of `T'` back to itself when it lies in `T` and to `1` otherwise is a left inverse of
it, and which makes the triangle

`presentedGroupMap r T = presentedGroupMap r T' ∘ incl`

commute (both sides are homomorphisms out of a free group agreeing on generators).
-/

universe u

namespace Work.OROneRel

theorem presentedGroupMap_injective_mono {α : Type u} {r : FreeGroup α} {T T' : Set α}
    (h : T ⊆ T')
    (hinj : Function.Injective (Work.OROneRel.presentedGroupMap r T')) :
    Function.Injective (Work.OROneRel.presentedGroupMap r T) := by
  classical
  -- The homomorphism of free groups induced by the inclusion `T ⊆ T'`.
  let incl : FreeGroup T →* FreeGroup T' :=
    FreeGroup.lift (fun t : T => FreeGroup.of ⟨(t : α), h t.property⟩)
  -- The retraction killing every generator of `T'` lying outside `T`.
  let retr : FreeGroup T' →* FreeGroup T :=
    FreeGroup.lift (fun t : T' => if ht : (t : α) ∈ T then FreeGroup.of ⟨(t : α), ht⟩ else 1)
  have hretr : retr.comp incl = MonoidHom.id (FreeGroup T) := by
    apply FreeGroup.ext_hom
    intro t
    show retr (incl (FreeGroup.of t)) = FreeGroup.of t
    have h1 : incl (FreeGroup.of t) = FreeGroup.of ⟨(t : α), h t.property⟩ :=
      FreeGroup.lift_apply_of
    have h2 : retr (FreeGroup.of ⟨(t : α), h t.property⟩) =
        (if ht : ((⟨(t : α), h t.property⟩ : T') : α) ∈ T then
          FreeGroup.of ⟨_, ht⟩ else 1) := FreeGroup.lift_apply_of
    rw [h1, h2, dif_pos t.property]
  have hincl : Function.Injective incl :=
    Function.LeftInverse.injective (g := ⇑retr) fun y => by
      have := DFunLike.congr_fun hretr y
      rwa [MonoidHom.comp_apply, MonoidHom.id_apply] at this
  -- The triangle `presentedGroupMap r T = presentedGroupMap r T' ∘ incl`.
  have hfac : presentedGroupMap r T = (presentedGroupMap r T').comp incl := by
    apply FreeGroup.ext_hom
    intro t
    show presentedGroupMap r T (FreeGroup.of t) = presentedGroupMap r T' (incl (FreeGroup.of t))
    have h1 : presentedGroupMap r T (FreeGroup.of t) = PresentedGroup.of (t : α) := rfl
    have h2 : incl (FreeGroup.of t) = FreeGroup.of ⟨(t : α), h t.property⟩ := FreeGroup.lift_apply_of
    have h3 : presentedGroupMap r T' (FreeGroup.of ⟨(t : α), h t.property⟩) =
        PresentedGroup.of ((⟨(t : α), h t.property⟩ : T') : α) := rfl
    rw [h1, h2, h3]
  rw [hfac]
  exact hinj.comp hincl

end Work.OROneRel
