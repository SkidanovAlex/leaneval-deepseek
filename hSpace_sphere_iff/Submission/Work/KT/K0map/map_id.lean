import Mathlib
import Submission.Work.KT.Defs

namespace Work.KT.K0map

open Work.KT

/-- `K₀.map` on the class of a matrix, at the level of the defining `QuotientAddGroup.lift`. -/
private lemma map_cls_eq {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (p : Mat R) :
    K0.map φ (cls p) = mapCls φ p := by
  rw [show K0.map φ = QuotientAddGroup.lift (K0Rel R) (FreeAbelianGroup.lift (mapCls φ)) _
      from rfl]
  rw [show cls p = QuotientAddGroup.mk (FreeAbelianGroup.of p) from rfl]
  rw [QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]

/-- A homomorphism out of `K₀` is determined by its values on the classes `cls p`. -/
private lemma ext_cls {R S : Type} [Ring R] [Ring S] {F G : K0 R →+ K0 S}
    (h : ∀ p : Mat R, F (cls p) = G (cls p)) : F = G := by
  have key : ∀ z : FreeAbelianGroup (Mat R),
      F (QuotientAddGroup.mk' (K0Rel R) z) = G (QuotientAddGroup.mk' (K0Rel R) z) := by
    intro z
    refine FreeAbelianGroup.induction_on z ?_ ?_ ?_ ?_
    · simp
    · intro a; exact h a
    · intro a ha; simp only [map_neg]; rw [ha]
    · intro a b ha hb; simp only [map_add]; rw [ha, hb]
  apply AddMonoidHom.ext
  intro x
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (K0Rel R) x
  exact key z

/-- `K₀` is a functor: `K₀(id) = id`. -/
theorem map_id (A : Type) [Ring A] :
    Work.KT.K0.map (RingHom.id A) = AddMonoidHom.id (Work.KT.K0 A) := by
  apply ext_cls
  intro p
  rw [map_cls_eq, mapCls]
  by_cases hp : p.IsIdem
  · rw [if_pos hp]
    congr 1
  · rw [if_neg hp]
    show (0 : K0 A) = cls p
    symm
    rw [show cls p = QuotientAddGroup.mk (FreeAbelianGroup.of p) from rfl,
      QuotientAddGroup.eq_zero_iff]
    exact AddSubgroup.subset_closure (Or.inr ⟨p, hp, rfl⟩)

end Work.KT.K0map
