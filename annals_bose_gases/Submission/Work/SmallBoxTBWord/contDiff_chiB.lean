import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxTBWord

open Submission.BoseGases

theorem contDiff_chiB {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)) : ContDiff ℝ (⊤ : ENat) (Submission.BoseGases.chiB ℓ d u) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hld : ℓ * d ≠ 0 := mul_ne_zero hℓne (ne_of_gt hd)
  unfold Submission.BoseGases.chiB
  exact (chiScale_contDiff hℓne).mul ((chiScale_contDiff hld).comp (by fun_prop))

end Work.SmallBoxTBWord
