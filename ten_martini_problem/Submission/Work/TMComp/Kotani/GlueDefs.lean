import Mathlib
import Submission.Work.TMComp.Kotani.Defs
import Submission.Work.TMComp.Kotani.mfun_props

/-!
# Gluing the local continuations of `mfun` (definitions shared with the fleet)

Vocabulary for `kotani_core_of_local`: the predicate `ExtOn α lam E₀ r x` ("the `m`-function
`mfun α lam · x` continues analytically across `E₀` to the ball `B(E₀,r)`, with the reflection
formula below the axis and positive imaginary part"), and the Cayley transform used to turn the
`ℍ`-valued extensions into a *bounded* family (so that dominated convergence applies).
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Kotani

open Work.TMContract

/-- `ExtOn α lam E₀ r x` says that `mfun α lam · x` continues analytically to the ball
`B(E₀,r)` (with `E₀` real), the continuation equals `1/conj (mfun (conj ·) (α - x))` on the
lower half of that ball, and has positive imaginary part on the whole ball. -/
def ExtOn (α lam : ℝ) (E₀ r x : ℝ) : Prop :=
  ∃ f : ℂ → ℂ,
    AnalyticOnNhd ℂ f (Metric.ball (E₀ : ℂ) r) ∧
    (∀ z ∈ Metric.ball (E₀ : ℂ) r, 0 < z.im → f z = mfun α lam z x) ∧
    (∀ z ∈ Metric.ball (E₀ : ℂ) r, z.im < 0 →
      f z = 1 / star (mfun α lam (star z) (α - x))) ∧
    (∀ z ∈ Metric.ball (E₀ : ℂ) r, 0 < (f z).im)

/-- The Cayley transform `ℍ → 𝔻`, `z ↦ (z - i)/(z + i)`. -/
def cayley (z : ℂ) : ℂ := (z - Complex.I) / (z + Complex.I)

/-- Its inverse `𝔻 → ℍ`, `u ↦ i(1 + u)/(1 - u)`. -/
def cayleyInv (u : ℂ) : ℂ := Complex.I * (1 + u) / (1 - u)

theorem norm_cayley_lt_one {z : ℂ} (hz : 0 < z.im) : ‖cayley z‖ < 1 := by
  have h1 : ‖z - Complex.I‖ ^ 2 = z.re ^ 2 + (z.im - 1) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have h2 : ‖z + Complex.I‖ ^ 2 = z.re ^ 2 + (z.im + 1) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have hne : z + Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  rw [cayley, norm_div, div_lt_one (norm_pos_iff.mpr hne)]
  nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I), sq_nonneg z.re, hz, h1, h2]

theorem im_cayleyInv_pos {u : ℂ} (hu : ‖u‖ < 1) : 0 < (cayleyInv u).im := by
  have hu1 : Complex.normSq u < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg u]
  have hne : (1 : ℂ) - u ≠ 0 := by
    intro h
    have : u = 1 := by linear_combination -h
    rw [this] at hu; simp at hu
  have hden : Complex.normSq (1 - u) = (1 - u.re) ^ 2 + u.im ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have hnum : (Complex.I * (1 + u)).im * (1 - u).re - (Complex.I * (1 + u)).re * (1 - u).im
      = 1 - u.re ^ 2 - u.im ^ 2 := by
    simp [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im]
    ring
  rw [cayleyInv, Complex.div_im, ← sub_div, hnum, hden]
  apply div_pos
  · have := Complex.normSq_apply u; nlinarith [hu1, this]
  · rw [← hden]; exact Complex.normSq_pos.mpr hne

theorem cayleyInv_cayley {z : ℂ} (hz : 0 < z.im) : cayleyInv (cayley z) = z := by
  have hne : z + Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  unfold cayleyInv cayley
  field_simp
  ring

theorem cayley_cayleyInv {u : ℂ} (hu : ‖u‖ < 1) : cayley (cayleyInv u) = u := by
  have hne : (1 : ℂ) - u ≠ 0 := by
    intro h
    have : u = 1 := by linear_combination -h
    rw [this] at hu; simp at hu
  unfold cayley cayleyInv
  field_simp
  ring

theorem continuousOn_cayleyInv : ContinuousOn cayleyInv (Metric.ball (0 : ℂ) 1) := by
  unfold cayleyInv
  refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun u hu => ?_)
  intro h
  have : u = 1 := by linear_combination -h
  rw [this] at hu; simp at hu

/-- Two analytic functions on a ball which both agree with `mfun α lam · x` on the upper half
of the ball are equal on the ball. -/
theorem eqOn_of_eqOn_upper {α lam E₀ r x : ℝ} (hr : 0 < r) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball (E₀ : ℂ) r))
    (hg : AnalyticOnNhd ℂ g (Metric.ball (E₀ : ℂ) r))
    (hfu : ∀ z ∈ Metric.ball (E₀ : ℂ) r, 0 < z.im → f z = mfun α lam z x)
    (hgu : ∀ z ∈ Metric.ball (E₀ : ℂ) r, 0 < z.im → g z = mfun α lam z x) :
    Set.EqOn f g (Metric.ball (E₀ : ℂ) r) := by
  set z₀ : ℂ := (E₀ : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I with hz₀
  have hz₀im : 0 < z₀.im := by
    rw [hz₀]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, zero_add]
    positivity
  have hz₀norm : ‖z₀ - (E₀ : ℂ)‖ = r / 2 := by
    rw [hz₀, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hz₀mem : z₀ ∈ Metric.ball (E₀ : ℂ) r := by
    rw [Metric.mem_ball, dist_eq_norm, hz₀norm]; linarith
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg
    Metric.isPreconnected_ball hz₀mem ?_
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Metric.ball z₀ (r / 4), Metric.ball_mem_nhds _ (by positivity), fun z hz => ?_⟩
  have hzdist : ‖z - z₀‖ < r / 4 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
  have hzim : 0 < z.im := by
    have h1 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
      simpa [Complex.sub_im] using Complex.abs_im_le_norm (z - z₀)
    have h2 : z₀.im = r / 2 := by
      rw [hz₀]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_one, zero_add]
      ring
    have h3 := abs_lt.mp (lt_of_le_of_lt h1 hzdist)
    rw [h2] at h3
    linarith [h3.1]
  have hzmem : z ∈ Metric.ball (E₀ : ℂ) r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsplit : z - (E₀ : ℂ) = (z - z₀) + (z₀ - (E₀ : ℂ)) := by ring
    rw [hsplit]
    calc ‖(z - z₀) + (z₀ - (E₀ : ℂ))‖
        ≤ ‖z - z₀‖ + ‖z₀ - (E₀ : ℂ)‖ := norm_add_le _ _
      _ < r / 4 + r / 2 := by rw [hz₀norm]; linarith
      _ < r := by linarith
  exact (hfu z hzmem hzim).trans (hgu z hzmem hzim).symm

end Work.TMComp.Kotani
