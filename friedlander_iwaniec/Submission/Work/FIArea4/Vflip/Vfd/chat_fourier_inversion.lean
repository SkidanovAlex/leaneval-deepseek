import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.SepDefs

/-!
# Fourier inversion for the chirped cutoff `chat`

The chirped cutoff `chat a b α x = nearCut a b x · |x|^{iα}` (see `SepDefs`) is smooth and
compactly supported: `nearCut a b` is `C^∞` and vanishes for `|x| ≤ a/2`, while `|x|^{iα}`
is `C^∞` away from the origin. Hence `chat a b α` is a Schwartz function, its Fourier
transform is integrable, and the Fourier inversion formula holds pointwise.
-/

namespace Work.FIArea4.Vflip.Vfd

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-- The chirp `u ↦ exp(iα log |u|)`, written in unfolded form, is smooth away from `0`. -/
lemma contDiffOn_chirp_exp (α : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => Complex.exp (((α * Real.log |u| : ℝ) : ℂ) * Complex.I))
      {x : ℝ | x ≠ 0} := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun u : ℝ => |u|) {x : ℝ | x ≠ 0} :=
    contDiffOn_abs (n := ⊤) (by simp)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun u : ℝ => Real.log |u|) {x : ℝ | x ≠ 0} :=
    Real.contDiffOn_log.comp h1 (by intro x hx; simpa using hx)
  have h4 : ContDiffOn ℝ (⊤ : ℕ∞) (fun u : ℝ => α * Real.log |u|) {x : ℝ | x ≠ 0} := by
    simpa using (contDiffOn_const (c := α) (s := {x : ℝ | x ≠ 0})).mul h2
  have h5 : ContDiffOn ℝ (⊤ : ℕ∞) (fun u : ℝ => ((α * Real.log |u| : ℝ) : ℂ))
      {x : ℝ | x ≠ 0} :=
    ContDiff.comp_contDiffOn Complex.ofRealCLM.contDiff h4
  have h6 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => ((α * Real.log |u| : ℝ) : ℂ) * Complex.I) {x : ℝ | x ≠ 0} :=
    h5.mul contDiffOn_const
  exact Complex.contDiff_exp.comp_contDiffOn h6

/-- `chat a b α` agrees with `nearCut a b · chirp α` away from the origin. -/
lemma chat_eq_mul_chirp (a b α x : ℝ) (hx : x ≠ 0) :
    chat a b α x = ((nearCut a b x : ℝ) : ℂ) * chirp α x := by
  rw [chat, cpow_eq_chirp hx]

/-- The chirped cutoff is `C^∞`: it is `C^∞` away from `0` and vanishes identically on
`|x| ≤ a/2`. -/
lemma contDiff_chat (a b α : ℝ) (ha : 0 < a) :
    ContDiff ℝ (⊤ : ℕ∞) (chat a b α) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    have hpos : (0 : ℝ) < a / 2 := by positivity
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with y hy
    have hy' : |y| ≤ a / 2 := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
      exact le_of_lt hy
    simp only [chat]
    rw [nearCut_eq_zero_of_abs_le ha hy', Complex.ofReal_zero, zero_mul]
  · have hF : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y : ℝ => ((nearCut a b y : ℝ) : ℂ) * chirp α y) {x : ℝ | x ≠ 0} :=
      (ContDiff.comp_contDiffOn Complex.ofRealCLM.contDiff
        (contDiff_nearCut a b).contDiffOn).mul (contDiffOn_chirp_exp α)
    refine (hF.contDiffAt (isOpen_ne.mem_nhds hx)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact chat_eq_mul_chirp a b α y hy

/-- The chirped cutoff is supported in `[-2b, 2b]`. -/
lemma hasCompactSupport_chat (a b α : ℝ) (hb : 0 < b) :
    HasCompactSupport (chat a b α) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(2 * b)) (2 * b))
    isCompact_Icc
  intro x hx
  rw [Function.mem_support] at hx
  have hxb : |x| < 2 * b := by
    by_contra hc
    refine hx ?_
    simp only [chat]
    rw [nearCut_eq_zero_of_abs_ge hb (not_lt.mp hc), Complex.ofReal_zero, zero_mul]
  obtain ⟨h1, h2⟩ := abs_lt.mp hxb
  exact ⟨le_of_lt h1, le_of_lt h2⟩

theorem chat_fourier_inversion (a b α : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ContDiff ℝ (⊤ : ℕ∞) (chat a b α) ∧ HasCompactSupport (chat a b α) ∧
      ∀ x : ℝ, ∫ u : ℝ, FourierTransform.fourier (chat a b α) u *
        Complex.exp (2 * Real.pi * Complex.I * (u * x)) = chat a b α x := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hcont := contDiff_chat a b α ha
  have hcs := hasCompactSupport_chat a b α hb
  refine ⟨hcont, hcs, fun x => ?_⟩
  have hint : Integrable (chat a b α) := hcont.continuous.integrable_of_hasCompactSupport hcs
  have h'f : Integrable (𝓕 (chat a b α)) := by
    have h := SchwartzMap.integrable (μ := volume) (𝓕 (hcs.toSchwartzMap hcont))
    rw [SchwartzMap.fourier_coe] at h
    exact h
  have hx := MeasureTheory.Integrable.fourierInv_fourier_eq (v := x) hint h'f
    hcont.continuous.continuousAt
  rw [← hx, Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with v
  rw [smul_eq_mul]
  have he : (↑(2 * Real.pi * inner ℝ v x) : ℂ) * Complex.I =
      2 * Real.pi * Complex.I * (v * x) := by
    rw [Real.inner_apply]; push_cast; ring
  rw [he]
  ring

end

end Work.FIArea4.Vflip.Vfd
