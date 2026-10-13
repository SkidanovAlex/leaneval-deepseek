import Mathlib
import Submission.Work.DSF1.Cech.UnitCaseSetup

namespace Work.DSF1.Cech

universe u

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

lemma InsIdxDelta {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (i₀ : ι)
    (n : ℕ) (i : Fin (n+2))
    (x : ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk (n+1)))).I) :
    ((Work.DSF1.Cech.E U).map (SimplexCategory.δ i.succ).op).f
        (Work.DSF1.Cech.insIdx U i₀ (n+1) x) =
      Work.DSF1.Cech.insIdx U i₀ n
        (((Work.DSF1.Cech.E U).map (SimplexCategory.δ i).op).f x) := by
  show (CategoryTheory.Limits.FormalCoproduct.mapPower
      (CategoryTheory.Limits.FormalCoproduct.mk ι U)
      (SimplexCategory.δ i.succ).toOrderHom.toFun).f (Fin.cons i₀ x) =
    Fin.cons i₀ ((CategoryTheory.Limits.FormalCoproduct.mapPower
      (CategoryTheory.Limits.FormalCoproduct.mk ι U)
      (SimplexCategory.δ i).toOrderHom.toFun).f x)
  funext a
  simp only [CategoryTheory.Limits.FormalCoproduct.mapPower, SimplexCategory.δ]
  exact congrFun (Fin.cons_comp_succ_succAbove i₀ x i) a

end Work.DSF1.Cech
