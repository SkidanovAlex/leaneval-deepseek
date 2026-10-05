import Mathlib
import Submission.Work.RPB.B5.chartLev_inverse
import Submission.Work.RPB.B5.halfChordSmooth
import Submission.Work.RPB.Defs

namespace Work.RPB.B5

theorem chartLev_eq_sq_mul_hc {CI : Work.RPV.CurveIsotopy} {a : ℝ → ℝ → ℝ → ℝ}
    {W : ℝ → ℝ → ℝ → Work.RPV.PS}
    (hchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    {hc : ℝ → ℝ → ℝ → ℂ}
    (hc_half : ∀ τ t r, r ≠ 0 → hc τ t r = Work.RPB.halfChord CI.c τ t r)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    ∀ ρ ∈ Set.Ioo (0 : ℝ) ((Real.pi / 2) ^ 2),
      Work.RPB.B5.chartLev W τ t ρ = ρ * ‖hc τ t (Real.sqrt ρ)‖ ^ 2 := by
  intro ρ hρ
  rw [Set.mem_Ioo] at hρ
  obtain ⟨hρ0, hρlt⟩ := hρ
  have hsqrt : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ0.le
  have hsne : Real.sqrt ρ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hρ0)
  have hr : Real.sqrt ρ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨Real.sqrt_pos.mpr hρ0, (Real.sqrt_lt' (by positivity)).mpr hρlt⟩
  have hWρ : W τ t ρ = W τ t ((Real.sqrt ρ) ^ 2) := by rw [hsqrt]
  rw [chartLev, hWρ, hchord τ hτ t (Real.sqrt ρ) hr,
    K0_chordSurf_add_one CI.c a τ t (Real.sqrt ρ), ← hc_half τ t (Real.sqrt ρ) hsne, hsqrt]

end Work.RPB.B5
