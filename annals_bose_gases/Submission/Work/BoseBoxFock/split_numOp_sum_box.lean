import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseBoxFock.KzOpC
import Submission.Work.BoseBoxFock.split_sandwiches
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem split_numOp_sum_box {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (B : Work.BoseB4.BoxData) {ℓ : ℝ} (kmom : Mode → EuclideanSpace ℝ (Fin 3))
    (hkmom : ∀ i : Mode, kmom (-i) = -kmom i) (f : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode, Work.BoseB4.gram (f i) (f j)
      = Work.BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))
    (hφ : ∀ k : Mode, f k 0 = 0) :
    ∀ y : Work.BoseB4.RealFock m,
      Work.BoseB4.split ((∑ k : Mode, (Work.BoseB4.boxFockData B kmom hkmom m f hf).nOp k) y)
        = Work.BoseB4.lift (∑ k : Mode, Work.BoseBoxFock.nOpC (f k)) (Work.BoseB4.split y) := by
  intro y
  -- Unfold the box mode operators `a_k = annOf (f k)`, `a_k† = creOf (f k)`.
  change Work.BoseB4.split
      ((∑ k : Mode, (Work.BoseB4.creOf m (f k)).comp (Work.BoseB4.annOf m (f k))) y)
    = Work.BoseB4.lift (∑ k : Mode, Work.BoseBoxFock.nOpC (f k)) (Work.BoseB4.split y)
  rw [LinearMap.sum_apply, map_sum]
  have hterm : ∀ k : Mode,
      Work.BoseB4.split ((Work.BoseB4.creOf m (f k)).comp (Work.BoseB4.annOf m (f k)) y)
        = (Work.BoseB4.lift (Work.BoseBoxFock.nOpC (f k))) (Work.BoseB4.split y) := by
    intro k
    rw [LinearMap.comp_apply]
    simp only [Work.BoseBoxFock.nOpC]
    rw [Work.BoseBoxFock.split_creOf_annOf (f k) (f k) (hφ k) (hφ k) y]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [← LinearMap.sum_apply, ← Work.BoseB4.lift_sum]

end Work.BoseBoxFock
