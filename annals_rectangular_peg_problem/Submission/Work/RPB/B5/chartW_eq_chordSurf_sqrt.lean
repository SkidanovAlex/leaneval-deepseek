import Mathlib
import Submission.Work.RPB.B5.LagData

namespace Work.RPB.B5

theorem chartW_eq_chordSurf_sqrt (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ x ∈ Set.Ioo (-Real.sqrt 2) 0,
      D.W τ t (D.rho τ x t) = Work.RPB.chordSurf CI.c a τ t (Real.sqrt (D.rho τ x t)) := by
  intro τ hτ t x hx
  -- `x ∈ Ioo (-√2) 0 ⊂ Ioc (-√2) 0`, so `rho τ x t` is a positive chord parameter `≤ π²/4`
  obtain ⟨hpos, hle⟩ := D.hrhoval τ hτ x ⟨hx.1, hx.2.le⟩ t
  -- hence `r = √(rho τ x t)` lies in `(0, π/2]`, where the chart agrees with `chordSurf`
  have hrle : Real.sqrt (D.rho τ x t) ≤ Real.pi / 2 := by
    have hpi : Real.sqrt (Real.pi ^ 2 / 4) = Real.pi / 2 := by
      rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    have := Real.sqrt_le_sqrt hle
    rwa [hpi] at this
  have h := D.hWchord τ hτ t (Real.sqrt (D.rho τ x t))
    ⟨Real.sqrt_pos_of_pos hpos, hrle⟩
  rwa [Real.sq_sqrt hpos.le] at h

end Work.RPB.B5
