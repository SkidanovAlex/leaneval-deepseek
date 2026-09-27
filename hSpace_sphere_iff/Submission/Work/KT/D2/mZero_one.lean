import Mathlib
import Submission.Work.KT.D2.mZero

set_option maxHeartbeats 2000000

namespace Work.KT.D2

open Matrix

noncomputable section

/-- A loop of matrices which is pointwise the identity has winding zero at the identity: the
winding is the degree of the determinant of the loop, which is the constant loop `1`. -/
lemma windLoop_of_apply_eq_one_eq_zero {n : ℕ} (e : Matrix (Fin n) (Fin n) ℂ)
    (γ : C(Sph (Euc 2), Matrix (Fin n) (Fin n) ℂ))
    (h : ∀ x, Matrix.det (e * γ x * e + (1 - e)) ≠ 0)
    (hγ : ∀ x, γ x = 1) (he : e = 1) : windLoop n e γ h = 0 := by
  rw [windLoop_eq_degNZ]
  have hfun : wlmDet n e γ = 1 := by
    ext x
    rw [wlmDet_apply, ContinuousMap.one_apply, hγ x, he]
    simp
  rw [wlmDegNZcongr hfun h (fun _ => one_ne_zero)]
  exact degNZ_one

/-- The trivial rank `k` bundle over the disc `D²` has winding invariant zero: the identity
matrix is trivialised by the constant family of units `1`, so its boundary loop is constant. -/
theorem mZero_one (y0 : Work.KT.Ball (EuclideanSpace ℝ (Fin 2)))
    (hy0 : y0 ∈ Work.KT.bdry (EuclideanSpace ℝ (Fin 2))) (k : ℕ) :
    Work.KT.D2.mZero y0 hy0 (Work.KT.Mat.one (Work.KT.Kpair (EuclideanSpace ℝ (Fin 2))) k)
      = 0 := by
  have key : Work.KT.D2.mZero y0 hy0
      (⟨k, (1 : Matrix (Fin k) (Fin k) (Work.KT.Kpair (EuclideanSpace ℝ (Fin 2))))⟩ :
        Work.KT.Mat (Work.KT.Kpair (EuclideanSpace ℝ (Fin 2)))) = 0 := by
    have hP : Work.KT.Mat.IsIdem
        (⟨k, (1 : Matrix (Fin k) (Fin k) (Kpair (Euc 2)))⟩ : Mat (Kpair (Euc 2))) := by
      show (1 : Matrix (Fin k) (Fin k) (Kpair (Euc 2))) * 1 = 1
      simp
    have hbval : bval k y0 (1 : Matrix (Fin k) (Fin k) (Kpair (Euc 2))) = 1 := by
      rw [bval]
      exact Matrix.map_one (augPair (Euc 2) y0).toRingHom (map_zero _) (map_one _)
    have huv : ∀ x, (1 : C(Ball (Euc 2), Matrix (Fin k) (Fin k) ℂ)) x *
        (1 : C(Ball (Euc 2), Matrix (Fin k) (Fin k) ℂ)) x = 1 := by
      intro x; simp
    have hconj : ∀ x, (1 : C(Ball (Euc 2), Matrix (Fin k) (Fin k) ℂ)) x *
        toCM k (1 : Matrix (Fin k) (Fin k) (Kpair (Euc 2))) x =
        bval k y0 (1 : Matrix (Fin k) (Fin k) (Kpair (Euc 2))) *
        (1 : C(Ball (Euc 2), Matrix (Fin k) (Fin k) ℂ)) x := by
      intro x
      rw [hbval, toCM_one_apply]
      simp
    have hblk : ∀ x, Matrix.det (bval k y0 (1 : Matrix (Fin k) (Fin k) (Kpair (Euc 2))) *
        (1 : C(Ball (Euc 2), Matrix (Fin k) (Fin k) ℂ)) (inBall x) *
        bval k y0 (1 : Matrix (Fin k) (Fin k) (Kpair (Euc 2))) +
        (1 - bval k y0 (1 : Matrix (Fin k) (Fin k) (Kpair (Euc 2))))) ≠ 0 := by
      intro x
      rw [hbval]
      simp
    have hmz := mZero_eq y0 hy0
      (⟨k, (1 : Matrix (Fin k) (Fin k) (Kpair (Euc 2)))⟩ : Mat (Kpair (Euc 2))) hP
      (1 : C(Ball (Euc 2), Matrix (Fin k) (Fin k) ℂ))
      (1 : C(Ball (Euc 2), Matrix (Fin k) (Fin k) ℂ)) huv huv hconj hblk
    refine hmz.symm.trans ?_
    exact windLoop_of_apply_eq_one_eq_zero (n := k)
      (e := bval k y0 (1 : Matrix (Fin k) (Fin k) (Kpair (Euc 2))))
      (γ := ((1 : C(Ball (Euc 2), Matrix (Fin k) (Fin k) ℂ)).comp inBallCM))
      hblk (fun x => by simp) hbval
  simpa only [Work.KT.Mat.one] using key

end

end Work.KT.D2
