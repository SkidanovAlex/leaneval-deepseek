import Mathlib
import Submission.Work.ATOM.ZS.NullSeqMaps
import Submission.Work.ATOM.epi_zmap_of_surjective

/-!
# AREA ATOM / `ℤ[S]`: the null sequence `g` has zero augmentation

`Work.ATOM.gBig S : ℤ[ℕ∪{∞}] ⟶ ℤ[S]` is the descent of the section `ĝ = ℤ[pr₂] - ℤ[β]` of `ℤ[S]`
over `T'` along the surjection `tProj : T' ⟶ ℕ∪{∞}` (`Work.ATOM.zdesc`).  Its composite with the
augmentation `aug S = ℤ[toPt S] : ℤ[S] ⟶ ℤ[*]` is zero: `ℤ[tProj]` is an epimorphism (a surjection
of light profinite sets induces an epimorphism of free light condensed abelian groups), so it
suffices to check the identity after pulling back along `ℤ[tProj]`, where it becomes
`ĝ ≫ aug = ℤ[pr₂ ≫ toPt] - ℤ[β ≫ toPt] = 0` because any two maps of light profinite sets into the
point agree.
-/

namespace Work.ATOM.ZS

open CategoryTheory MonoidalCategory LightProfinite

/-- Any two morphisms of light profinite sets into the point `*` agree. -/
private lemma eq_toPt {X : LightProfinite.{0}} (f g : X ⟶ Work.ATOM.pt) : f = g := by
  apply ConcreteCategory.hom_ext
  intro x
  exact Subsingleton.elim _ _

/-- For any `q : T' S ⟶ S`, the composite `ℤ[q] ≫ aug S` is the canonical map
`ℤ[toPt (T' S)] : ℤ[T'] ⟶ ℤ[*]`. -/
private lemma zmap_aug_eq (S : LightProfinite.{0}) [Infinite S] (q : Work.ATOM.T' S ⟶ S) :
    Work.ATOM.zmap q ≫ Work.ATOM.aug S = Work.ATOM.zmap (Work.ATOM.toPt (Work.ATOM.T' S)) := by
  have h : q ≫ Work.ATOM.toPt S = Work.ATOM.toPt (Work.ATOM.T' S) := eq_toPt _ _
  rw [show Work.ATOM.aug S = Work.ATOM.zmap (Work.ATOM.toPt S) from rfl,
    ← Work.ATOM.zmap_comp_zfree q (Work.ATOM.toPt S), h]

open CategoryTheory MonoidalCategory in
theorem gBig_aug_zero (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.gBig S ≫ Work.ATOM.aug S = 0 := by
  haveI : Epi (Work.ATOM.zmap (Work.ATOM.tProj S)) :=
    Work.ATOM.epi_zmap_of_surjective (Work.ATOM.tProj S) (Work.ATOM.tProj_surjective S)
  refine (cancel_epi (Work.ATOM.zmap (Work.ATOM.tProj S))).mp ?_
  rw [← Category.assoc, Work.ATOM.gBig_spec S, Work.ATOM.gHat, Preadditive.sub_comp,
    zmap_aug_eq S (Work.ATOM.pr₂T S), zmap_aug_eq S (Work.ATOM.betaT S), sub_self,
    Limits.comp_zero]

end Work.ATOM.ZS
