import Mathlib
import Submission.Work.SSS.iotaF_chainMap

namespace Work.SSS

/-- A point of `Δ[n] × F` is in `(boundary n).preimage (fst Δ[n] F)` as soon as its first
component is in the boundary.  This is the concrete computation performed by `ez` when the
pullback projection of `ez (x, y)` is forced to be `x`. -/
theorem ez_pair_mem_bdryAlong_of {Xf Yf F : SSet.{0}} (f : Xf ⟶ Yf) (P : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⟶ Yf)
    (ez : (CategoryTheory.MonoidalCategory.tensorObj
            (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) F) ⟶ Work.SSS.pullAlong f σ)
    (hez : CategoryTheory.CategoryStruct.comp ez (CategoryTheory.Limits.pullback.fst σ f)
      = CategoryTheory.SemiCartesianMonoidalCategory.fst
          (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) F)
    (x : (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}).obj (Opposite.op (SimplexCategory.mk P)))
    (hx : x ∈ (SSet.boundary (P+1)).obj (Opposite.op (SimplexCategory.mk P)))
    (y : F.obj (Opposite.op (SimplexCategory.mk P))) :
    (CategoryTheory.ConcreteCategory.hom (ez.app (Opposite.op (SimplexCategory.mk P)))) (x, y)
      ∈ (Work.SSS.bdryAlong f σ).obj (Opposite.op (SimplexCategory.mk P)) := by
  -- The composite `ez ≫ pullback.fst σ f` is the first projection, so the first component of
  -- `ez (x, y)` is `x`.
  have e1 : CategoryTheory.ConcreteCategory.hom ((CategoryTheory.Limits.pullback.fst σ f).app (Opposite.op (SimplexCategory.mk P)))
        ((CategoryTheory.ConcreteCategory.hom (ez.app (Opposite.op (SimplexCategory.mk P)))) (x,y))
      = CategoryTheory.ConcreteCategory.hom ((CategoryTheory.CategoryStruct.comp ez (CategoryTheory.Limits.pullback.fst σ f)).app (Opposite.op (SimplexCategory.mk P))) (x,y) := rfl
  have e2 : CategoryTheory.ConcreteCategory.hom ((CategoryTheory.CategoryStruct.comp ez (CategoryTheory.Limits.pullback.fst σ f)).app (Opposite.op (SimplexCategory.mk P))) (x,y)
      = CategoryTheory.ConcreteCategory.hom ((CategoryTheory.SemiCartesianMonoidalCategory.fst
          (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) F).app (Opposite.op (SimplexCategory.mk P))) (x,y) := by
    rw [hez]
  have e3 : CategoryTheory.ConcreteCategory.hom ((CategoryTheory.SemiCartesianMonoidalCategory.fst
          (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) F).app (Opposite.op (SimplexCategory.mk P))) (x,y) = x := rfl
  have key : CategoryTheory.ConcreteCategory.hom ((CategoryTheory.Limits.pullback.fst σ f).app (Opposite.op (SimplexCategory.mk P)))
        ((CategoryTheory.ConcreteCategory.hom (ez.app (Opposite.op (SimplexCategory.mk P)))) (x,y)) = x :=
    e1.trans (e2.trans e3)
  have hmem : CategoryTheory.ConcreteCategory.hom ((CategoryTheory.Limits.pullback.fst σ f).app (Opposite.op (SimplexCategory.mk P)))
        ((CategoryTheory.ConcreteCategory.hom (ez.app (Opposite.op (SimplexCategory.mk P)))) (x,y))
      ∈ (SSet.boundary (P+1)).obj (Opposite.op (SimplexCategory.mk P)) := by
    rw [key]; exact hx
  -- `bdryAlong f σ` is the preimage of the boundary under the pullback projection, so it
  -- suffices that the projection of `ez (x, y)` lies in the boundary.
  show CategoryTheory.ConcreteCategory.hom (ez.app (Opposite.op (SimplexCategory.mk P))) (x,y)
      ∈ (Work.SSS.bdryAlong f σ).obj (Opposite.op (SimplexCategory.mk P))
  exact hmem

end Work.SSS
