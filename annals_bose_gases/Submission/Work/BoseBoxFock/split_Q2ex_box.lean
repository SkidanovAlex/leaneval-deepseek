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

theorem split_Q2ex_box {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (B : Work.BoseB4.BoxData) {ℓ : ℝ} (kmom : Mode → EuclideanSpace ℝ (Fin 3))
    (hkmom : ∀ i : Mode, kmom (-i) = -kmom i) (f : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode, Work.BoseB4.gram (f i) (f j)
      = Work.BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))
    (hφ : ∀ k : Mode, f k 0 = 0) (E : Work.BoseB7.Q3Env Mode) :
    ∀ y : Work.BoseB4.RealFock m,
      Work.BoseB4.split ((Work.BoseB4.boxFockData B kmom hkmom m f hf).Q2ex E y)
        = Work.BoseB4.lift (Work.BoseBoxFock.Q2exC f E) (Work.BoseB4.split y) := by
  intro y
  -- Each single-mode number operator transports to its spectator form.
  have hAB : ∀ k ∈ Work.BoseB7.excited Mode, ∀ z : Work.BoseB4.RealFock m,
      Work.BoseB4.split ((Work.BoseB4.boxFockData B kmom hkmom m f hf).nOp k z)
        = Work.BoseB4.lift (Work.BoseBoxFock.nOpC (f k)) (Work.BoseB4.split z) := by
    intro k hk z
    change Work.BoseB4.split (Work.BoseB4.creOf m (f k) (Work.BoseB4.annOf m (f k) z))
      = Work.BoseB4.lift (Work.BoseBoxFock.nOpC (f k)) (Work.BoseB4.split z)
    rw [Work.BoseBoxFock.split_creOf_annOf (f k) (f k) (hφ k) (hφ k) z]
    rfl
  rw [Work.BoseB7.FockData.Q2ex, Work.BoseBoxFock.Q2exC]
  exact Work.BoseBoxFock.ss_lift_weighted (Work.BoseB7.excited Mode)
    (fun k => E.rho * (E.W1omega k + E.W1omega0))
    (fun k => (Work.BoseB4.boxFockData B kmom hkmom m f hf).nOp k)
    (fun k => Work.BoseBoxFock.nOpC (f k)) hAB y

end Work.BoseBoxFock
