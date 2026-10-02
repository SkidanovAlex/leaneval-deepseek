import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.PontryaginThom.Frames
import Submission.Work.Thom.manifoldP1
import Submission.Work.ThomBordism.FrameSigns.Assembly

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

theorem tangentFrameSigns {V : Work.ThomBordism.Man8} :
    ∃ δ : (i : Fin (Work.Thom.chartCoverSize (H := Work.ThomBordism.PontryaginThom.Euc 8) (M := V.pt))) → V.pt → ℝ,
      (∀ (i : Fin (Work.Thom.chartCoverSize (H := Work.ThomBordism.PontryaginThom.Euc 8) (M := V.pt))) (x : V.pt),
        δ i x = 1 ∨ δ i x = -1) ∧
      (∀ i, ContinuousOn (δ i)
        (Work.Thom.chartCover (H := Work.ThomBordism.PontryaginThom.Euc 8) (M := V.pt) i).1.source) ∧
      (∀ (i j : Fin (Work.Thom.chartCoverSize (H := Work.ThomBordism.PontryaginThom.Euc 8) (M := V.pt)))
        (x : V.pt)
        (_hi : x ∈ (Work.Thom.chartCover (H := Work.ThomBordism.PontryaginThom.Euc 8) (M := V.pt) i).1.source)
        (_hj : x ∈ (Work.Thom.chartCover (H := Work.ThomBordism.PontryaginThom.Euc 8) (M := V.pt) j).1.source),
        δ i x * δ j x = Real.sign (LinearMap.det (ContinuousLinearMap.toLinearMap
          (fderiv ℝ
            (fun y => (Work.Thom.chartCover (H := Work.ThomBordism.PontryaginThom.Euc 8) (M := V.pt) j).1
              ((Work.Thom.chartCover (H := Work.ThomBordism.PontryaginThom.Euc 8) (M := V.pt) i).1.symm y))
            ((Work.Thom.chartCover (H := Work.ThomBordism.PontryaginThom.Euc 8) (M := V.pt) i).1 x))))) := by
  exact Work.ThomBordism.FrameSigns.tangentFrameSigns_aux V

end Work.ThomBordism
