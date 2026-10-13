import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
import Submission.Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.SlotA.cwPairBound
import Submission.Work.FTS.EllipticEst.remov.AeIPMemsSlim

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

theorem AeI1CSPiece : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
    - Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
        (fun z θ => (2 * (z - 1) / (1 + z)) * Work.Spaces.pthIter 2 u z θ)
      ≥ - 2 * (Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
              (Work.Spaces.pthIter 2 u))) := by
  intro α u G hA hGrad
  have huS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (Work.FTS.EllipticEst.H2W.Ae.AeData.smooth hA)
  have hBS : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 u) := (huS.pth).pth
  have hUS : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz u z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
      (Work.FTS.EllipticEst.SmoothOpen.pz huS)
  have hmB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u) :=
    Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 hA
  have hUB : Work.FTS.EllipticEst.AngSecond.IPMem
      (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.Spaces.pthIter 2 u) :=
    Work.FTS.EllipticEst.remov.ipMem_of_HkMem_agreeOnQ_ae hUS hBS
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) hGrad hmB
  have hUU : Work.FTS.EllipticEst.AngSecond.IPMem
      (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hGrad
  have hBB : Work.FTS.EllipticEst.AngSecond.IPMem
      (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u) :=
    Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmB
  have hle := Work.FTS.EllipticEst.H2W.SlotA.IP_cw_le (Work.FTS.EllipticEst.H2W.Ae.grad u)
    (Work.Spaces.pthIter 2 u) hUU hBB hUB
  have hswap : Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
        (fun z θ => (2 * (z - 1) / (1 + z)) * Work.Spaces.pthIter 2 u z θ)
      = Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
            * Work.FTS.EllipticEst.H2W.Ae.grad u z θ)
          (Work.Spaces.pthIter 2 u) := by
    rw [Work.FTS.EllipticEst.AngSecond.IP, Work.FTS.EllipticEst.AngSecond.IP]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    simp only [Work.FTS.EllipticEst.AngSecond.cw, Work.FTS.EllipticEst.H2W.Ae.grad]
    ring
  rw [hswap]
  linarith [hle]

end Work.FTS.EllipticEst.remov
