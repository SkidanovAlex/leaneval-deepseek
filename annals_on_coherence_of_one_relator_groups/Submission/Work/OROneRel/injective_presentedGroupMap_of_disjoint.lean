import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

/-- If the relator `r` involves none of the generators in `T`, then the canonical map
`F(T) →* ⟨α | r⟩` is injective.

This is proved by exhibiting a retraction: sending every generator outside `T` to `1` defines a
homomorphism `ψ : F(α) →* F(T)` which kills `r` (all letters of the reduced word of `r` avoid `T`),
so it factors through the presentation `⟨α | r⟩`.  The resulting map `⟨α | r⟩ →* F(T)` is a left
inverse of `presentedGroupMap r T`. -/
theorem injective_presentedGroupMap_of_disjoint {α : Type u} (r : FreeGroup α) (T : Set α)
    (h : ∀ a ∈ Work.OROneRel.relatorLetters r, a ∉ T) :
    Function.Injective (Work.OROneRel.presentedGroupMap r T) := by
  classical
  -- The projection `F(α) →* F(T)` killing every generator outside `T`.
  let f : α → FreeGroup T := fun a => if ha : a ∈ T then FreeGroup.of ⟨a, ha⟩ else 1
  -- It kills `r`, since every letter of the reduced word of `r` lies outside `T`.
  have hψr : FreeGroup.lift f r = 1 := by
    have hletters : ∀ p ∈ FreeGroup.toWord r, p.1 ∉ T := by
      intro p hp
      exact h p.1 ⟨p.2, hp⟩
    rw [← FreeGroup.mk_toWord (x := r), FreeGroup.lift_mk]
    apply List.prod_eq_one
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxT : x.1 ∉ T := hletters x hx
    simp [f, dif_neg hxT]
  -- Hence it factors through the presentation `⟨α | r⟩`.
  let φ : PresentedGroup ({r} : Set (FreeGroup α)) →* FreeGroup T :=
    PresentedGroup.toGroup (f := f) (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hψr)
  -- `φ` is a left inverse of `presentedGroupMap r T`.
  have hleft : φ.comp (Work.OROneRel.presentedGroupMap r T) = MonoidHom.id (FreeGroup T) := by
    apply FreeGroup.ext_hom
    intro t
    have h1 : Work.OROneRel.presentedGroupMap r T (FreeGroup.of t) = PresentedGroup.of (t : α) := by
      rw [Work.OROneRel.presentedGroupMap, MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      rfl
    have h2 : φ (PresentedGroup.of (t : α)) = f (t : α) := by
      change (PresentedGroup.toGroup _) (PresentedGroup.of (t : α)) = f (t : α)
      exact PresentedGroup.toGroup.of _
    have h3 : f (t : α) = FreeGroup.of t := by
      simp only [f, dif_pos t.2]
    rw [MonoidHom.comp_apply, h1, h2, h3]
    rfl
  intro x y hxy
  have hx := DFunLike.congr_fun hleft x
  have hy := DFunLike.congr_fun hleft y
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at hx hy
  rw [← hx, hxy, hy]

end Work.OROneRel
