import Mathlib
import Submission.Work.KT.D2.mZero

namespace Work.KT.D2

/-- The winding invariant `mZero` of the zero matrix over `Kpair ℝ²` vanishes: the zero matrix is
idempotent, its boundary value is `0`, and the associated determinant loop of a trivialisation is
the constant loop `1`, which has winding `0`. -/
theorem mZero_zero (y0 : Work.KT.Ball (EuclideanSpace ℝ (Fin 2)))
    (hy0 : y0 ∈ Work.KT.bdry (EuclideanSpace ℝ (Fin 2))) (k : ℕ) :
    Work.KT.D2.mZero y0 hy0
      (⟨k, (0 : Matrix (Fin k) (Fin k) (Work.KT.Kpair (EuclideanSpace ℝ (Fin 2))))⟩ :
        Work.KT.Mat (Work.KT.Kpair (EuclideanSpace ℝ (Fin 2)))) = 0 := by
  have hP : Work.KT.Mat.IsIdem
      (⟨k, (0 : Matrix (Fin k) (Fin k) (Kpair (Euc 2)))⟩ : Mat (Kpair (Euc 2))) := by
    show (0 : Matrix (Fin k) (Fin k) (Kpair (Euc 2))) * 0 = 0
    simp
  rw [mZero_of_idem y0 hy0 _ hP]
  have hbval : bval k y0 (0 : Matrix (Fin k) (Fin k) (Kpair (Euc 2))) = 0 := by
    rw [bval]
    exact Matrix.map_zero _ (map_zero _)
  change degNZ (wlmDet k (bval k y0 0) ((trivU y0 _ hP).comp inBallCM)) _ = 0
  have hconst : wlmDet k (bval k y0 0) ((trivU y0 _ hP).comp inBallCM)
      = ContinuousMap.const (Sph (Euc 2)) (1 : ℂ) := by
    apply ContinuousMap.ext
    intro x
    rw [wlmDet_apply, hbval]
    simp
  calc degNZ (wlmDet k (bval k y0 0) ((trivU y0 _ hP).comp inBallCM)) _
      = degNZ (ContinuousMap.const (Sph (Euc 2)) (1 : ℂ)) (fun _ => one_ne_zero) :=
        wlmDegNZcongr hconst _ _
    _ = 0 := degNZ_const 1 one_ne_zero

end Work.KT.D2
