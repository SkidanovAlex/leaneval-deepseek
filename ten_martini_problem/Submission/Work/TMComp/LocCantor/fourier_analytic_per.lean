import Mathlib
import Submission.Work.TMComp.LocCantor.Defs

/-!
# Analyticity and periodicity of the Fourier transform of an exponentially decaying sequence

Let `u : ℤ → ℂ` satisfy `ExpDecay u`, i.e. `‖u n‖ ≤ C exp (-c |n|)` for some `c > 0` and `C`.
This file proves that the Fourier transform

  `U(x) = ∑ₙ uₙ e^{2πinx}`   (`Work.TMComp.fourier u`)

is real analytic on all of `ℝ` (`AnalyticOnNhd ℝ (fourier u) Set.univ`) and `1`-periodic
(`U (x + 1) = U x`), which is the statement of `fourier_analytic_per`.

The analyticity is proved by extending the series to the complex strip `|Im z| < c/(4π)`,
where the `n`-th term is dominated by `max C 0 · exp (-(c/2)|n|)`; there the series is a
locally uniform limit of entire functions, hence holomorphic, and restricting to the real
axis gives real analyticity.  The periodicity is immediate from
`exp (n · (2πI)) = 1` for `n : ℤ`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Filter Topology Set

namespace Work.TMComp.LocCantor

namespace FourierPerAux

open Work.TMContract

/-- `∑_{n : ℤ} e^{-c|n|}` converges for `c > 0`. -/
theorem summable_exp_neg_abs_int (c : ℝ) (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-(c * |(n : ℝ)|))) := by
  rw [summable_int_iff_summable_nat_and_neg]
  have hr : ‖Real.exp (-c)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  constructor
  · refine (summable_geometric_of_norm_lt_one hr).congr ?_
    intro n
    rw [← Real.exp_nat_mul]
    congr 1
    rw [abs_of_nonneg (by positivity)]
    push_cast
    ring
  · refine (summable_geometric_of_norm_lt_one hr).congr ?_
    intro n
    rw [← Real.exp_nat_mul]
    congr 1
    have h : ((↑(-↑n) : ℤ) : ℝ) = -(n : ℝ) := by push_cast; ring
    rw [h, abs_neg, abs_of_nonneg (by positivity)]
    ring

/-- The complex extension `z ↦ ∑ₙ uₙ e^{2πinz}` of the Fourier sum. -/
def fourierC (u : ℤ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℤ, u n * Complex.exp (2 * Real.pi * (n : ℝ) * z * Complex.I)

/-- On the real axis the complex extension is the Fourier transform. -/
theorem fourierC_ofReal (u : ℤ → ℂ) (x : ℝ) :
    fourierC u (x : ℂ) = Work.TMComp.fourier u x := rfl

/-- Norm of the `n`-th Fourier mode at a complex frequency. -/
theorem norm_exp_int_mul_I (n : ℤ) (w : ℂ) :
    ‖Complex.exp (2 * Real.pi * (n : ℝ) * w * Complex.I)‖
      = Real.exp (-(2 * Real.pi * (n : ℝ) * w.im)) := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]

/-- On the strip `|Im w| < c/(4π)` the `n`-th Fourier mode is dominated by
`max C 0 · exp (-(c/2)|n|)`. -/
theorem norm_term_le (u : ℤ → ℂ) {c C : ℝ} (hc : 0 < c)
    (hC : ∀ n : ℤ, ‖u n‖ ≤ C * Real.exp (-(c * |(n : ℝ)|)))
    {w : ℂ} (hw : |w.im| < c / (4 * Real.pi)) (n : ℤ) :
    ‖u n * Complex.exp (2 * Real.pi * (n : ℝ) * w * Complex.I)‖
      ≤ max C 0 * Real.exp (-(c / 2 * |(n : ℝ)|)) := by
  have hCnn : 0 ≤ C :=
    le_trans (norm_nonneg (u 0)) (by simpa using hC 0)
  have hle : -(c * |(n : ℝ)|) + -(2 * Real.pi * (n : ℝ) * w.im) ≤ -(c / 2 * |(n : ℝ)|) := by
    have hb : -(2 * Real.pi * (n : ℝ) * w.im) ≤ 2 * Real.pi * |(n : ℝ)| * |w.im| := by
      have h1 : -(2 * Real.pi * (n : ℝ) * w.im)
          ≤ |2 * Real.pi * (n : ℝ) * w.im| := neg_le_abs _
      rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)] at h1
      exact h1
    have hπn : (0 : ℝ) ≤ 2 * Real.pi * |(n : ℝ)| := by positivity
    have hc2 : 2 * Real.pi * |(n : ℝ)| * |w.im| ≤ c / 2 * |(n : ℝ)| := by
      have h3 : 2 * Real.pi * |(n : ℝ)| * |w.im| ≤ 2 * Real.pi * |(n : ℝ)| * (c / (4 * Real.pi)) :=
        mul_le_mul_of_nonneg_left (le_of_lt hw) hπn
      have h4 : 2 * Real.pi * |(n : ℝ)| * (c / (4 * Real.pi)) = c / 2 * |(n : ℝ)| := by
        field_simp
        ring
      exact h3.trans h4.le
    calc -(c * |(n : ℝ)|) + -(2 * Real.pi * (n : ℝ) * w.im)
        ≤ -(c * |(n : ℝ)|) + c / 2 * |(n : ℝ)| :=
          add_le_add_right (le_trans hb hc2) _
      _ = -(c / 2 * |(n : ℝ)|) := by ring
  calc ‖u n * Complex.exp (2 * Real.pi * (n : ℝ) * w * Complex.I)‖
      = ‖u n‖ * Real.exp (-(2 * Real.pi * (n : ℝ) * w.im)) := by
        rw [norm_mul, norm_exp_int_mul_I]
    _ ≤ (C * Real.exp (-(c * |(n : ℝ)|))) * Real.exp (-(2 * Real.pi * (n : ℝ) * w.im)) :=
        mul_le_mul_of_nonneg_right (hC n) (Real.exp_pos _).le
    _ = C * Real.exp (-(c * |(n : ℝ)|) + -(2 * Real.pi * (n : ℝ) * w.im)) := by
        rw [mul_assoc, ← Real.exp_add]
    _ ≤ C * Real.exp (-(c / 2 * |(n : ℝ)|)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) hCnn
    _ ≤ max C 0 * Real.exp (-(c / 2 * |(n : ℝ)|)) :=
        mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_nonneg _)

/-- The complex extension is holomorphic on the strip `|Im z| < c/(4π)`: there the series
converges locally uniformly, dominated by the summable sequence `max C 0 · exp (-(c/2)|n|)`. -/
theorem fourierC_differentiableOn (u : ℤ → ℂ) {c C : ℝ} (hc : 0 < c)
    (hC : ∀ n : ℤ, ‖u n‖ ≤ C * Real.exp (-(c * |(n : ℝ)|))) :
    DifferentiableOn ℂ (fourierC u) {z : ℂ | |z.im| < c / (4 * Real.pi)} := by
  refine Complex.differentiableOn_tsum_of_summable_norm
    (F := fun n : ℤ => fun w : ℂ => u n * Complex.exp (2 * Real.pi * (n : ℝ) * w * Complex.I))
    (u := fun n : ℤ => max C 0 * Real.exp (-(c / 2 * |(n : ℝ)|)))
    ((summable_exp_neg_abs_int (c / 2) (by linarith)).mul_left _)
    (fun n => by fun_prop) ?_ ?_
  · exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  · intro n w hw
    exact norm_term_le u hc hC hw n

/-- The complex extension is analytic at every real point. -/
theorem fourierC_analyticAt (u : ℤ → ℂ) (hu : ExpDecay u) (x : ℝ) :
    AnalyticAt ℂ (fourierC u) (x : ℂ) := by
  obtain ⟨c, hc, C, hC⟩ := hu
  refine (fourierC_differentiableOn u hc hC).analyticAt ?_
  refine (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).mem_nhds ?_
  simpa using div_pos hc (by positivity : (0 : ℝ) < 4 * Real.pi)

/-- Restricting the complex extension to the real axis gives a real analytic function. -/
theorem fourierC_analyticAt_real (u : ℤ → ℂ) (hu : ExpDecay u) (x : ℝ) :
    AnalyticAt ℝ (fun y : ℝ => fourierC u (y : ℂ)) x :=
  (fourierC_analyticAt u hu x).restrictScalars.comp (Complex.ofRealCLM.analyticAt x)

/-- The Fourier transform of an exponentially decaying sequence is real analytic. -/
theorem fourier_analytic (u : ℤ → ℂ) (hu : ExpDecay u) :
    AnalyticOnNhd ℝ (Work.TMComp.fourier u) Set.univ :=
  fun x _ => fourierC_analyticAt_real u hu x

/-- The Fourier transform of an exponentially decaying sequence is `1`-periodic. -/
theorem fourier_periodic (u : ℤ → ℂ) (x : ℝ) :
    Work.TMComp.fourier u (x + 1) = Work.TMComp.fourier u x := by
  simp only [Work.TMComp.fourier]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_add, Complex.ofReal_one]
  have hexp : 2 * Real.pi * (n : ℝ) * ((x : ℂ) + 1) * Complex.I
      = 2 * Real.pi * (n : ℝ) * (x : ℂ) * Complex.I
        + ((n : ℝ) : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    ring
  rw [hexp, Complex.exp_add, Complex.ofReal_intCast, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end FourierPerAux

open FourierPerAux

/-- The Fourier transform `U(x) = ∑ₙ uₙ e^{2πinx}` of an exponentially decaying sequence
`u : ℤ → ℂ` is real analytic on all of `ℝ` and `1`-periodic. -/
theorem fourier_analytic_per (u : ℤ → ℂ) (hu : Work.TMContract.ExpDecay u) :
    AnalyticOnNhd ℝ (Work.TMComp.fourier u) Set.univ ∧
      (∀ x : ℝ, Work.TMComp.fourier u (x + 1) = Work.TMComp.fourier u x) :=
  ⟨fourier_analytic u hu, fun x => fourier_periodic u x⟩

end Work.TMComp.LocCantor
