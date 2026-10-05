import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B2.chordSurf_period_swap

/-!
# B5: the chord form of `ℓ` on the right half plane (`Work.RPB.B5.lagData_chord_form_right`)

For `x > 0` the assembled family is `ℓ τ (x,t) = τ_π (basePt τ (-x) (t-π))`, and since
`x < √2` the reflected point `-x` lies in the chord-chart region `(-√2, 0)`, where
`basePt τ (-x) (t-π) = W τ (t-π) (ρ τ (-x) (t-π)) = chordSurf c a τ (t-π) r` with
`r = √(ρ τ (-x) (t-π)) ∈ (0, π/2]`.  The chord-swap identity
`Work.RPB.B2.chordSurf_period_swap` then rewrites `τ_π` of the chord at `(t-π, r)` as the chord
at `(t, π - r)`, giving the asserted form.  The same bound `r ≤ π/2` gives
`π - r ∈ (π/2, π) ⊂ (0, π)`.
-/

open RectangularPegProblem
open Manifold Complex Real

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

theorem lagData_chord_form_right (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t : ℝ, 0 < x → x < Real.sqrt 2 →
      Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x t
          = Work.RPB.chordSurf CI.c a τ t (Real.pi - Real.sqrt (D.rho τ (-x) (t - Real.pi))) ∧
        Real.pi - Real.sqrt (D.rho τ (-x) (t - Real.pi)) ∈ Set.Ioo (0 : ℝ) Real.pi := by
  intro τ hτ x t hxpos hxlt
  -- the chord-swap identity of the chord annulus
  have hsw := (Work.RPB.B2.chordSurf_period_swap CI a ha).2
  -- bounds for the chart parameter at the reflected point `-x ∈ (-√2, 0)`
  obtain ⟨hr0, hr1⟩ := D.hrhoval τ hτ (-x) ⟨by linarith, by linarith⟩ (t - Real.pi)
  have hrsq : Real.sqrt (D.rho τ (-x) (t - Real.pi)) ^ 2 = D.rho τ (-x) (t - Real.pi) :=
    Real.sq_sqrt hr0.le
  have hrpos : 0 < Real.sqrt (D.rho τ (-x) (t - Real.pi)) := Real.sqrt_pos.mpr hr0
  have hrle : Real.sqrt (D.rho τ (-x) (t - Real.pi)) ≤ Real.pi / 2 := by
    calc Real.sqrt (D.rho τ (-x) (t - Real.pi)) ≤ Real.sqrt (Real.pi ^ 2 / 4) :=
          Real.sqrt_le_sqrt hr1
      _ = Real.pi / 2 := by
          rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
          exact Real.sqrt_sq (by positivity)
  have hrpi : Real.sqrt (D.rho τ (-x) (t - Real.pi)) ∈ Set.Ioo (0 : ℝ) Real.pi :=
    ⟨hrpos, by linarith [Real.pi_pos, hrle]⟩
  refine ⟨?_, ⟨by linarith [Real.pi_pos, hrle], by linarith [Real.pi_pos, hrpos]⟩⟩
  -- the reflected base half is the chord chart at `(t - π, r)`
  have hch : D.W τ (t - Real.pi) (Real.sqrt (D.rho τ (-x) (t - Real.pi)) ^ 2) =
      Work.RPB.chordSurf CI.c a τ (t - Real.pi) (Real.sqrt (D.rho τ (-x) (t - Real.pi))) :=
    D.hWchord τ hτ (t - Real.pi) _ ⟨hrpos, hrle⟩
  have hbase : basePt D.W D.Γc D.Ac D.rho τ (-x) (t - Real.pi) =
      Work.RPB.chordSurf CI.c a τ (t - Real.pi) (Real.sqrt (D.rho τ (-x) (t - Real.pi))) := by
    rw [basePt, ite_eq_right (not_le.mpr (show -Real.sqrt 2 < -x by linarith))]
    conv_lhs => rw [← hrsq]
    exact hch
  -- `τ_π` of the chord at `(t - π, r)` is the chord at `(t, π - r)`
  have hswap := hsw τ hτ (t - Real.pi) (Real.sqrt (D.rho τ (-x) (t - Real.pi))) hrpi
  rw [sub_add_cancel] at hswap
  rw [lagPt, ite_eq_right (not_le.mpr hxpos), hbase]
  exact hswap.symm

end Work.RPB.B5
