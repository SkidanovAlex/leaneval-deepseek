import Submission.Work.Analysis.IonescuWainger.circleMulOp_comp

namespace Work.Analysis.IonescuWainger
open MeasureTheory

theorem lp_smul_smul (m m' : Lp ℂ ⊤ circleMeasure) (g : Lp ℂ 2 circleMeasure) :
    m • (m' • g) = (m • m') • g :=
  lp_smul_smul_assoc m m' g

theorem multiplier_comp (m m' : MeasureTheory.Lp ℂ ⊤ circleMeasure) (f : L2Z) :
    multiplier m (multiplier m' f) = multiplier (m • m') f := by
  have h : fourierZ (multiplier m (multiplier m' f))
      = fourierZ (multiplier (m • m') f) := by
    rw [fourierZ_multiplier, fourierZ_multiplier, fourierZ_multiplier]
    exact lp_smul_smul m m' (fourierZ f)
  calc multiplier m (multiplier m' f)
      = fourierZ.symm (fourierZ (multiplier m (multiplier m' f))) :=
        (fourierZ.symm_apply_apply _).symm
    _ = fourierZ.symm (fourierZ (multiplier (m • m') f)) := by rw [h]
    _ = multiplier (m • m') f := fourierZ.symm_apply_apply _

end Work.Analysis.IonescuWainger
