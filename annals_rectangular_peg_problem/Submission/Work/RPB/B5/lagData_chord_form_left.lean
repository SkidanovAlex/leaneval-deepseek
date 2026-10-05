import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.chartW_eq_chordSurf_sqrt

namespace Work.RPB.B5

/-- On the closed left interval `[-√2, 0]` the assembled family `ℓ` is the chord chart itself:
`lagPt τ x t = chordSurf CI.c a τ t (√(rho τ x t))`, with the radius `√(rho τ x t)` in `(0, π/2]`.

For `x ≤ 0` the definition of `lagPt` is the base half, and since `-√2 < x` the collar branch
(`x ≤ -√2`) is not taken, so `lagPt τ x t = W τ t (rho τ x t)`.  For `x < 0` this is
`chartW_eq_chordSurf_sqrt`; at `x = 0` we use `rho τ 0 t = π²/4` (so the radius is `π/2`) and
`hWchord` at `r = π/2 ∈ Ioc 0 (π/2)`.  The radius bound comes from `rhoval`
(`0 < rho τ x t ≤ π²/4` for `x ∈ Ioc (-√2) 0`). -/
theorem lagData_chord_form_left (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t : ℝ, -Real.sqrt 2 < x → x ≤ 0 →
      Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x t
        = Work.RPB.chordSurf CI.c a τ t (Real.sqrt (D.rho τ x t)) ∧
      Real.sqrt (D.rho τ x t) ∈ Set.Ioc (0 : ℝ) (Real.pi / 2) := by
  intro τ hτ x t hx hx0
  -- `lagPt` is the base half, and `x > -√2` rules out the collar branch
  have hnot : ¬ x ≤ -Real.sqrt 2 := by linarith
  have hlag : Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x t = D.W τ t (D.rho τ x t) := by
    simp only [Work.RPB.B5.lagPt, Work.RPB.B5.basePt, hx0, hnot, ite_true, ite_false]
  have hsqrt_pi2 : Real.sqrt (Real.pi ^ 2 / 4) = Real.pi / 2 := by
    rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rcases lt_or_eq_of_le hx0 with hxlt | hxeq
  · -- the strict interior case: the chart agrees with `chordSurf` (`chartW_eq_chordSurf_sqrt`)
    have hpos := (D.hrhoval τ hτ x ⟨hx, le_of_lt hxlt⟩ t).1
    have hle := (D.hrhoval τ hτ x ⟨hx, le_of_lt hxlt⟩ t).2
    have hrpos : 0 < Real.sqrt (D.rho τ x t) := Real.sqrt_pos_of_pos hpos
    have hrle : Real.sqrt (D.rho τ x t) ≤ Real.pi / 2 := by
      calc Real.sqrt (D.rho τ x t) ≤ Real.sqrt (Real.pi ^ 2 / 4) := Real.sqrt_le_sqrt hle
        _ = Real.pi / 2 := hsqrt_pi2
    refine ⟨?_, hrpos, hrle⟩
    rw [hlag]
    have h := D.hWchord τ hτ t (Real.sqrt (D.rho τ x t)) ⟨hrpos, hrle⟩
    rwa [Real.sq_sqrt hpos.le] at h
  · -- the junction `x = 0`: `rho = π²/4`, hence the radius is exactly `π/2`
    have hr : Real.sqrt (D.rho τ x t) = Real.pi / 2 := by
      rw [hxeq, D.hrho0 τ hτ t, hsqrt_pi2]
    refine ⟨?_, ?_⟩
    · rw [hlag, hr, hxeq, D.hrho0 τ hτ t,
        show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
      exact D.hWchord τ hτ t (Real.pi / 2) ⟨by linarith [Real.pi_pos], le_refl _⟩
    · rw [hr]
      exact ⟨by linarith [Real.pi_pos], le_refl _⟩

end Work.RPB.B5
