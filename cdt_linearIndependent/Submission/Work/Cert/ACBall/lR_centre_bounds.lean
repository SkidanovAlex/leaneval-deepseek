import Mathlib
import Submission.Work.Cert.ACBall.LuneChain

namespace Work.Cert.ACBall
open Work.Cert Complex

/-- Lower counterpart of `norm_cx_le_of_sq_le`: if the mantissa `m ≥ 0` is dominated by the
mantissa square sum of `(x, y)`, then `m/S ≤ ‖(x + y i)/S‖`. -/
lemma le_norm_cx_of_sq_le (x y m : ℤ) (hm : 0 ≤ m) (h : m * m ≤ x * x + y * y) :
    (m : ℝ) / (S : ℝ) ≤ ‖cx x y‖ := by
  have hcast : (m : ℝ) ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 := by
    have h' : ((m * m : ℤ) : ℝ) ≤ ((x * x + y * y : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    simpa [sq] using h'
  have hmR : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2 : ((m : ℝ) / (S : ℝ)) ^ 2 ≤ ‖cx x y‖ ^ 2 := by
    rw [norm_cx_sq, div_pow]
    exact div_le_div_of_nonneg_right hcast (sq_nonneg _)
  calc (m : ℝ) / (S : ℝ) = Real.sqrt (((m : ℝ) / (S : ℝ)) ^ 2) :=
        (Real.sqrt_sq (div_nonneg hmR S_posR.le)).symm
    _ ≤ Real.sqrt (‖cx x y‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖cx x y‖ := Real.sqrt_sq (norm_nonneg _)

/-- `BallMem` gives the upper bound `‖w‖ ≤ ‖centre‖ + r/S`. -/
lemma norm_le_of_ballMem {a : Bl} {u : ℂ} (h : BallMem a u) :
    ‖u‖ ≤ ‖cx a.x a.y‖ + (a.r : ℝ) / (S : ℝ) := by
  have hu : ‖u - cx a.x a.y‖ ≤ (a.r : ℝ) / (S : ℝ) := h
  have h1 : ‖u‖ = ‖(u - cx a.x a.y) + cx a.x a.y‖ := by rw [sub_add_cancel]
  rw [h1]
  linarith [norm_add_le (u - cx a.x a.y) (cx a.x a.y)]

/-- `BallMem` gives the lower bound `‖centre‖ - r/S ≤ ‖w‖`. -/
lemma le_norm_of_ballMem {a : Bl} {u : ℂ} (h : BallMem a u) :
    ‖cx a.x a.y‖ - (a.r : ℝ) / (S : ℝ) ≤ ‖u‖ := by
  have hu : ‖u - cx a.x a.y‖ ≤ (a.r : ℝ) / (S : ℝ) := h
  have h1 : ‖cx a.x a.y‖ = ‖u + (cx a.x a.y - u)‖ := by
    congr 1
    ring
  rw [h1]
  have h2 : ‖u + (cx a.x a.y - u)‖ ≤ ‖u‖ + ‖u - cx a.x a.y‖ := by
    simpa only [norm_sub_rev] using norm_add_le u (cx a.x a.y - u)
  linarith

theorem lR_centre_bounds (st : Work.Cert.St) (w : Work.Cert.LuneW)
    (hRU0 : 0 ≤ w.RU) (hRUsq : (Work.Cert.ACBall.lR st).x * (Work.Cert.ACBall.lR st).x + (Work.Cert.ACBall.lR st).y * (Work.Cert.ACBall.lR st).y ≤ w.RU * w.RU)
    (hRL0 : 0 ≤ w.RL) (hRLsq : w.RL * w.RL ≤ (Work.Cert.ACBall.lR st).x * (Work.Cert.ACBall.lR st).x + (Work.Cert.ACBall.lR st).y * (Work.Cert.ACBall.lR st).y)
    (hrpU0 : 0 ≤ w.rpU)
    (hrpUsq : (Work.Cert.ACBall.lRp st).x * (Work.Cert.ACBall.lRp st).x + (Work.Cert.ACBall.lRp st).y * (Work.Cert.ACBall.lRp st).y ≤ w.rpU * w.rpU) :
    ‖Work.APsi.luneR (36 / 5) (-(Work.Cert.ACBall.cIn st))‖ ≤ ((w.RU + (Work.Cert.ACBall.lR st).r : ℤ) : ℝ) / (Work.Cert.S : ℝ) ∧
      ((w.RL - (Work.Cert.ACBall.lR st).r : ℤ) : ℝ) / (Work.Cert.S : ℝ) ≤ ‖Work.APsi.luneR (36 / 5) (-(Work.Cert.ACBall.cIn st))‖ ∧
      ‖deriv (Work.APsi.luneR (36 / 5)) (-(Work.Cert.ACBall.cIn st))‖
        ≤ ((w.rpU + (Work.Cert.ACBall.lRp st).r : ℤ) : ℝ) / (Work.Cert.S : ℝ) := by
  have hmemR : BallMem (lR st) (Work.APsi.luneR (36 / 5) (-(cIn st))) := ballMem_lR st
  have hmemRp : BallMem (lRp st) (Work.ANum2.luneRd (36 / 5) (-(cIn st))) := ballMem_lRp st
  have hcxU : ‖cx (lR st).x (lR st).y‖ ≤ (w.RU : ℝ) / (S : ℝ) :=
    norm_cx_le_of_sq_le _ _ _ hRU0 hRUsq
  have hcxL : (w.RL : ℝ) / (S : ℝ) ≤ ‖cx (lR st).x (lR st).y‖ :=
    le_norm_cx_of_sq_le _ _ _ hRL0 hRLsq
  have hcxD : ‖cx (lRp st).x (lRp st).y‖ ≤ (w.rpU : ℝ) / (S : ℝ) :=
    norm_cx_le_of_sq_le _ _ _ hrpU0 hrpUsq
  have hcastR : ((w.RU + (lR st).r : ℤ) : ℝ) / (S : ℝ)
      = (w.RU : ℝ) / (S : ℝ) + ((lR st).r : ℝ) / (S : ℝ) := by push_cast; ring
  have hcastL : ((w.RL - (lR st).r : ℤ) : ℝ) / (S : ℝ)
      = (w.RL : ℝ) / (S : ℝ) - ((lR st).r : ℝ) / (S : ℝ) := by push_cast; ring
  have hcastD : ((w.rpU + (lRp st).r : ℤ) : ℝ) / (S : ℝ)
      = (w.rpU : ℝ) / (S : ℝ) + ((lRp st).r : ℝ) / (S : ℝ) := by push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · calc ‖Work.APsi.luneR (36 / 5) (-(cIn st))‖
        ≤ ‖cx (lR st).x (lR st).y‖ + ((lR st).r : ℝ) / (S : ℝ) := norm_le_of_ballMem hmemR
      _ ≤ (w.RU : ℝ) / (S : ℝ) + ((lR st).r : ℝ) / (S : ℝ) := add_le_add hcxU le_rfl
      _ = ((w.RU + (lR st).r : ℤ) : ℝ) / (S : ℝ) := hcastR.symm
  · calc ((w.RL - (lR st).r : ℤ) : ℝ) / (S : ℝ)
        = (w.RL : ℝ) / (S : ℝ) - ((lR st).r : ℝ) / (S : ℝ) := hcastL
      _ ≤ ‖cx (lR st).x (lR st).y‖ - ((lR st).r : ℝ) / (S : ℝ) := sub_le_sub_right hcxL _
      _ ≤ ‖Work.APsi.luneR (36 / 5) (-(cIn st))‖ := le_norm_of_ballMem hmemR
  · have hrd : deriv (Work.APsi.luneR (36 / 5)) (-(cIn st))
        = Work.ANum2.luneRd (36 / 5) (-(cIn st)) := Work.ANum2.deriv_luneR _ _
    rw [hrd]
    calc ‖Work.ANum2.luneRd (36 / 5) (-(cIn st))‖
        ≤ ‖cx (lRp st).x (lRp st).y‖ + ((lRp st).r : ℝ) / (S : ℝ) := norm_le_of_ballMem hmemRp
      _ ≤ (w.rpU : ℝ) / (S : ℝ) + ((lRp st).r : ℝ) / (S : ℝ) := add_le_add hcxD le_rfl
      _ = ((w.rpU + (lRp st).r : ℤ) : ℝ) / (S : ℝ) := hcastD.symm

end Work.Cert.ACBall
