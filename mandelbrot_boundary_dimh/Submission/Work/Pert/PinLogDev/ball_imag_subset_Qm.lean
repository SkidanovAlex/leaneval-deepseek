import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup

/-!
# `Work.Pert.PinLogDev.ball_imag_subset_Qm`

The lower gate region `Qm Ξ α = MandelDim.Qreg (some (Ξ - 1/α)) (some (-Ξ))` (see
`Work.Pert.Setup`) contains the disc of centre `s · I` and radius `R` as soon as the vertical
segment of imaginary parts `[Ξ + R, s - R]` that contains the disc sits above the bottom vertex
`-Ξ` and strictly to the left of the horizontal half-line `Ξ + 2R + i·ℝ`:

* `Ξ + 2 * R ≤ s` puts the whole disc above the vertex `-(Ξ : ℂ)` of the gate (the second
  conjunct of `Qreg`, `Re (z + Ξ) < |Im (z + Ξ)|`);
* `Ξ + 2 * R < Re (1/α)` puts the whole disc strictly to the right of the slanted boundary
  through `(Ξ : ℂ) - 1/α` (the first conjunct of `Qreg`).

Both are pure real inequalities: for `z ∈ ball (s·I) R` one has `Re z > -R` and `Im z > s - R`,
hence `Re z - Ξ + Re (1/α) > 0` (so `-|Im (z - (Ξ - 1/α))| ≤ 0 < Re (z - (Ξ - 1/α))`) and
`Re z + Ξ < Ξ + R ≤ s - R < Im z ≤ |Im z|`.
-/

namespace Work.Pert.PinLogDev

open Complex Metric

theorem ball_imag_subset_Qm {Ξ R s : ℝ} {α : ℂ}
    (hR : 0 ≤ R) (hs : Ξ + 2 * R ≤ s) (hα : Ξ + 2 * R < (1 / α).re) :
    Metric.ball ((s : ℂ) * Complex.I) R ⊆ Work.Pert.Qm Ξ α := by
  intro w hw
  -- real coordinates of the disc
  have hw' : ‖w - (s : ℂ) * Complex.I‖ < R := by simpa [Complex.dist_eq] using hw
  have hRe_abs : |w.re| < R :=
    lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (w - (s : ℂ) * Complex.I)) hw'
  have hIm_abs : |w.im - s| < R :=
    lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (w - (s : ℂ) * Complex.I)) hw'
  have hre : -R < w.re := (abs_lt.mp hRe_abs).1
  have hre' : w.re < R := (abs_lt.mp hRe_abs).2
  have him : s - R < w.im := by linarith [(abs_lt.mp hIm_abs).1]
  rw [Work.Pert.Qm, MandelDim.Qreg]
  constructor
  · -- right boundary: `-|Im (w - (Ξ - 1/α))| < Re (w - (Ξ - 1/α))`
    intro b hb
    simp only [Option.mem_def, Option.some.injEq] at hb
    subst hb
    have hc : (w - ((Ξ : ℂ) - 1 / α)).re = w.re - Ξ + (1 / α).re := by
      simp [Complex.sub_re]; ring
    have hlt : (0 : ℝ) < (w - ((Ξ : ℂ) - 1 / α)).re := by rw [hc]; linarith
    linarith [abs_nonneg (w - ((Ξ : ℂ) - 1 / α)).im]
  · -- bottom vertex: `Re (w + Ξ) < |Im (w + Ξ)|`
    intro b hb
    simp only [Option.mem_def, Option.some.injEq] at hb
    subst hb
    have hlt : w.re + Ξ < |w.im| := by linarith [le_abs_self w.im]
    simpa [Complex.sub_re, Complex.sub_im] using hlt

end Work.Pert.PinLogDev
