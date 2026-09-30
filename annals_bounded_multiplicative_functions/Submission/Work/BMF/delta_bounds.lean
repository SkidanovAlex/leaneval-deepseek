import Mathlib
import Submission.Work.BMF.parseval_kernels
import Submission.Work.BMF.norm_cpow_I_eq_one
import Submission.Work.BMF.norm_cpow_I_sub_one_le
import Submission.Work.BMF.integral_sub_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bounds for the average kernel `Θ` and the difference kernel `Δ`

We establish the elementary size estimates for the kernels

* `Theta δ t = ((1+δ)^{1+it}-1)/(δ(1+it)) = δ⁻¹ ∫_1^{1+δ} s^{it} ds`,
* `Delta h₁ h₂ x t = Theta (h₁/x) t - Theta (h₂/x) t`,

used in the proof of the short-interval Parseval bound `parseval_short`.

The key point is the integral representation of `Theta` via the fundamental theorem of
calculus: since `d/ds (s^{1+it}/(1+it)) = s^{it}`, one has
`Θ(δ,t) = δ⁻¹ ∫_1^{1+δ} s^{it} ds`.  As `|s^{it}| = 1` this gives `‖Θ‖ ≤ 1`, and
`|s^{it} - 1| ≤ |t| log s ≤ |t|(s-1)` gives the first-order bound `‖Θ - 1‖ ≤ |t|δ/2`.
-/

namespace Work.BMF

open scoped BigOperators
open MeasureTheory intervalIntegral

/-- Fundamental theorem of calculus for the kernel integrand:
`∫_1^{1+δ} s^{it} ds = ((1+δ)^{1+it}-1)/(1+it)`. -/
lemma integral_cpow_I (t δ : ℝ) (hδ : 0 ≤ δ) :
    ∫ s in (1:ℝ)..(1+δ), ((s:ℝ):ℂ)^(Complex.I*(t:ℂ))
      = (((1+δ:ℝ):ℂ)^(Complex.I*(t:ℂ)+1) - 1)/(Complex.I*(t:ℂ)+1) := by
  set w : ℂ := Complex.I*(t:ℂ) with hwdef
  have hw : w ≠ -1 := by
    rw [hwdef]; intro h; have := congrArg Complex.re h; simp at this
  have hle : (1:ℝ) ≤ 1 + δ := by linarith
  have hderiv : ∀ x ∈ Set.uIcc (1:ℝ) (1+δ),
      HasDerivAt (fun y : ℝ => (y:ℂ)^(w+1)/(w+1)) (((x:ℝ):ℂ)^w) x := by
    intro x hx
    have hx0 : x ≠ 0 := by rw [Set.uIcc_of_le hle] at hx; linarith [hx.1]
    simpa using hasDerivAt_ofReal_cpow_const' hx0 hw
  have hint : IntervalIntegrable (fun s : ℝ => ((s:ℝ):ℂ)^w) MeasureTheory.volume 1 (1+δ) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.cpow_const
    · exact Complex.continuous_ofReal.continuousOn
    · intro a ha
      rw [Complex.ofReal_mem_slitPlane]
      rw [Set.uIcc_of_le hle] at ha
      linarith [ha.1]
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hmain]
  simp [Complex.one_cpow, sub_div]

/-- Integral representation of the average kernel:
`Θ(δ,t) = δ⁻¹ ∫_1^{1+δ} s^{it} ds` for `δ > 0`. -/
lemma theta_eq_integral (δ t : ℝ) (hδ : 0 < δ) :
    Theta δ t = (∫ s in (1:ℝ)..(1+δ), ((s:ℝ):ℂ)^(Complex.I*(t:ℂ))) / (δ:ℂ) := by
  have hftc := integral_cpow_I t δ hδ.le
  rw [hftc]
  unfold Theta
  rw [show (1:ℂ) + Complex.I*(t:ℂ) = Complex.I*(t:ℂ) + 1 from by ring]
  rw [div_div, mul_comm (δ:ℂ) (Complex.I*(t:ℂ)+1)]

/-- `‖Θ(δ,t)‖ ≤ 1`: the kernel is an average of the unimodular numbers `s^{it}`. -/
lemma theta_norm_le_one (δ t : ℝ) (hδ : 0 < δ) : ‖Theta δ t‖ ≤ 1 := by
  have hle : (1:ℝ) ≤ 1+δ := by linarith
  have hδn : ‖(δ:ℂ)‖ = δ := by simp [abs_of_pos hδ]
  rw [theta_eq_integral δ t hδ, norm_div, hδn, div_le_iff₀ hδ]
  have h : ‖∫ s in (1:ℝ)..(1+δ), ((s:ℝ):ℂ)^(Complex.I*(t:ℂ))‖ ≤ δ := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1:ℝ)) (b := 1+δ) (C := (1:ℝ))
      (f := fun s : ℝ => ((s:ℝ):ℂ)^(Complex.I*(t:ℂ)))
      (fun x hx => by
        rw [Set.uIoc_of_le hle] at hx
        rw [norm_cpow_I_eq_one t x (by linarith [hx.1])])
    simpa [abs_of_pos hδ] using this
  calc ‖∫ s in (1:ℝ)..(1+δ), ((s:ℝ):ℂ)^(Complex.I*(t:ℂ))‖ ≤ δ := h
    _ = 1 * δ := by ring

/-- `‖Θ(δ,t) - 1‖ ≤ |t|δ/2`: first-order expansion of the average kernel. -/
lemma theta_sub_one_norm_le (δ t : ℝ) (hδ : 0 < δ) : ‖Theta δ t - 1‖ ≤ |t| * δ / 2 := by
  have hle : (1:ℝ) ≤ 1+δ := by linarith
  have hδne : (δ:ℂ) ≠ 0 := by simp only [ne_eq, Complex.ofReal_eq_zero]; linarith
  have hδn : ‖(δ:ℂ)‖ = δ := by simp [abs_of_pos hδ]
  have hfcont : ContinuousOn (fun s : ℝ => ((s:ℝ):ℂ)^(Complex.I*(t:ℂ))) (Set.uIcc (1:ℝ) (1+δ)) := by
    rw [Set.uIcc_of_le hle]
    apply ContinuousOn.cpow_const
    · exact Complex.continuous_ofReal.continuousOn
    · intro a ha
      rw [Complex.ofReal_mem_slitPlane]
      linarith [ha.1]
  have hfi : IntervalIntegrable (fun s : ℝ => ((s:ℝ):ℂ)^(Complex.I*(t:ℂ))) volume (1:ℝ) (1+δ) :=
    hfcont.intervalIntegrable
  have hci : IntervalIntegrable (fun _ : ℝ => (1:ℂ)) volume (1:ℝ) (1+δ) := intervalIntegrable_const
  have hI : (∫ s in (1:ℝ)..(1+δ), ((s:ℝ):ℂ)^(Complex.I*(t:ℂ))) - (δ:ℂ)
      = ∫ s in (1:ℝ)..(1+δ), (((s:ℝ):ℂ)^(Complex.I*(t:ℂ)) - 1) := by
    rw [intervalIntegral.integral_sub hfi hci, intervalIntegral.integral_const]
    simp
  have hmain : Theta δ t - 1
      = (∫ s in (1:ℝ)..(1+δ), (((s:ℝ):ℂ)^(Complex.I*(t:ℂ)) - 1))/(δ:ℂ) := by
    rw [theta_eq_integral δ t hδ, ← hI, sub_div, div_self hδne]
  rw [hmain, norm_div, hδn, div_le_iff₀ hδ]
  have hbound : ‖∫ s in (1:ℝ)..(1+δ), (((s:ℝ):ℂ)^(Complex.I*(t:ℂ)) - 1)‖ ≤ |t| * δ^2/2 := by
    have hgi : IntervalIntegrable (fun s : ℝ => |t| * (s - 1)) volume (1:ℝ) (1+δ) :=
      (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
    have hpt : ∀ᵐ x ∂volume, x ∈ Set.Ioc (1:ℝ) (1+δ) →
        ‖((x:ℝ):ℂ)^(Complex.I*(t:ℂ)) - 1‖ ≤ |t| * (x - 1) :=
      Filter.Eventually.of_forall (fun x hx => norm_cpow_I_sub_one_le t x (le_of_lt hx.1))
    have h := intervalIntegral.norm_integral_le_of_norm_le hle hpt hgi
    calc ‖∫ s in (1:ℝ)..(1+δ), (((s:ℝ):ℂ)^(Complex.I*(t:ℂ)) - 1)‖
        ≤ ∫ s in (1:ℝ)..(1+δ), |t| * (s - 1) := h
      _ = |t| * δ^2/2 := by rw [intervalIntegral.integral_const_mul, integral_sub_one]; ring
  calc ‖∫ s in (1:ℝ)..(1+δ), (((s:ℝ):ℂ)^(Complex.I*(t:ℂ)) - 1)‖ ≤ |t| * δ^2/2 := hbound
    _ = (|t| * δ / 2) * δ := by ring

theorem delta_bounds :
    (∀ (δ t : ℝ), 0 < δ → ‖Work.BMF.Theta δ t‖ ≤ 1) ∧
    (∀ (δ t : ℝ), 0 < δ → ‖Work.BMF.Theta δ t - 1‖ ≤ |t| * δ / 2) ∧
    (∀ (h₁ h₂ x t : ℝ), 0 < h₁ → h₁ ≤ h₂ → 0 < x →
        ‖Work.BMF.Delta h₁ h₂ x t‖ ≤ min 2 (|t| * h₂ / x)) := by
  refine ⟨theta_norm_le_one, theta_sub_one_norm_le, ?_⟩
  intro h₁ h₂ x t hh₁ hh₁₂ hx
  have hh₂ : 0 < h₂ := lt_of_lt_of_le hh₁ hh₁₂
  have hx1 : 0 < h₁ / x := div_pos hh₁ hx
  have hx2 : 0 < h₂ / x := div_pos hh₂ hx
  have hD : Delta h₁ h₂ x t = Theta (h₁/x) t - Theta (h₂/x) t := rfl
  refine le_min ?_ ?_
  · rw [hD]
    calc ‖Theta (h₁/x) t - Theta (h₂/x) t‖
        ≤ ‖Theta (h₁/x) t‖ + ‖Theta (h₂/x) t‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (theta_norm_le_one _ _ hx1) (theta_norm_le_one _ _ hx2)
      _ = 2 := by norm_num
  · rw [hD]
    have hb1 : ‖Theta (h₁/x) t - 1‖ ≤ |t| * (h₁/x)/2 := theta_sub_one_norm_le _ _ hx1
    have hb2 : ‖Theta (h₂/x) t - 1‖ ≤ |t| * (h₂/x)/2 := theta_sub_one_norm_le _ _ hx2
    calc ‖Theta (h₁/x) t - Theta (h₂/x) t‖
        = ‖(Theta (h₁/x) t - 1) - (Theta (h₂/x) t - 1)‖ := by congr 1; ring
      _ ≤ ‖Theta (h₁/x) t - 1‖ + ‖Theta (h₂/x) t - 1‖ := norm_sub_le _ _
      _ ≤ |t| * (h₁/x)/2 + |t| * (h₂/x)/2 := add_le_add hb1 hb2
      _ ≤ |t| * h₂ / x := by
          have hkey : |t| * (h₁/x)/2 + |t| * (h₂/x)/2 = |t| * (h₁ + h₂) / (2*x) := by field_simp
          rw [hkey, div_le_iff₀ (by positivity : (0:ℝ) < 2*x)]
          have hrw : (|t| * h₂ / x) * (2*x) = |t| * (2*h₂) := by field_simp
          rw [hrw]
          nlinarith [mul_le_mul_of_nonneg_left hh₁₂ (abs_nonneg t), abs_nonneg t]

end Work.BMF
