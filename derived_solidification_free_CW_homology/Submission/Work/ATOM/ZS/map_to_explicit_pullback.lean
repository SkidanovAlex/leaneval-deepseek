import Mathlib
import Submission.Work.ATOM.ZS.Topo.TSpace

namespace Work.ATOM.ZS

theorem map_to_explicit_pullback (S : LightProfinite.{0}) [Infinite S] :
    ∃ e : CategoryTheory.Limits.pullback (Work.ATOM.tProj S) (Work.ATOM.tProj S) ⟶
          CompHausLike.pullback (Work.ATOM.tProj S) (Work.ATOM.tProj S),
      CategoryTheory.CategoryStruct.comp e
          (CompHausLike.pullback.fst (Work.ATOM.tProj S) (Work.ATOM.tProj S)) =
        CategoryTheory.Limits.pullback.fst (Work.ATOM.tProj S) (Work.ATOM.tProj S) ∧
      CategoryTheory.CategoryStruct.comp e
          (CompHausLike.pullback.snd (Work.ATOM.tProj S) (Work.ATOM.tProj S)) =
        CategoryTheory.Limits.pullback.snd (Work.ATOM.tProj S) (Work.ATOM.tProj S) := by
  -- The explicit pullback of `CompHausLike` is a limit cone, so the universal property gives a
  -- morphism from the abstract limit pullback; the two triangles hold by definition.
  refine ⟨CompHausLike.pullback.lift (Work.ATOM.tProj S) (Work.ATOM.tProj S)
      (CategoryTheory.Limits.pullback.fst (Work.ATOM.tProj S) (Work.ATOM.tProj S))
      (CategoryTheory.Limits.pullback.snd (Work.ATOM.tProj S) (Work.ATOM.tProj S))
      CategoryTheory.Limits.pullback.condition,
    rfl, rfl⟩

end Work.ATOM.ZS
