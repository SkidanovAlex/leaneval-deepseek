import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The mean-value bound for a slice: `|u'(θ) - u'(θ₀)| ≤ ∫_{Iθ} |u''|`

If `u` is `C^∞` on the open angular interval `(0, π/2)` and `|u''|` is integrable on
`Iθ = [0, π/2]`, then for any two interior points `θ, θ₀ ∈ (0, π/2)` the fundamental theorem
of calculus on the segment joining them gives

  `u'(θ) - u'(θ₀) = ∫_{θ₀}^{θ} u''`,

and since `|u''| ≥ 0` and the segment `[θ₀, θ]` (respectively `[θ, θ₀]`) is contained in
`Iθ`, the absolute value of this integral is at most `∫_{Iθ} |u''|`.
-/

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.SgamBound

theorem abs_deriv_sub_le_integral_abs_D2 {u : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hD2abs : MeasureTheory.IntegrableOn
      (fun θ => |Work.FTS.EllipticEst.TT.D2 u θ|) Work.Spaces.Iθ)
    {θ θ₀ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hθ₀ : θ₀ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |deriv u θ - deriv u θ₀|
      ≤ ∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u x| := by
  have hπ : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  -- `D2 u` is definitionally the second derivative of `u`.
  have hD2 : Work.FTS.EllipticEst.TT.D2 u = deriv (deriv u) := rfl
  -- `u` is `C²`, so `deriv u` is `C¹` on the open interval.
  have hcd : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm 2).deriv_of_isOpen isOpen_Ioo (by norm_num)
  -- the segment joining `θ₀` and `θ` stays strictly inside `(0, π/2)`.
  have hsub : Set.uIcc θ₀ θ ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hθ₀.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hθ₀.2⟩
  -- Newton–Leibniz on that segment.
  have hFTC : (∫ x in θ₀..θ, deriv (deriv u) x) = deriv u θ - deriv u θ₀ :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hcd.mono hsub)
  have hD2abs' : MeasureTheory.IntegrableOn (fun x => |deriv (deriv u) x|) Work.Spaces.Iθ := by
    simpa only [hD2] using hD2abs
  have hgi : IntervalIntegrable (fun x => |deriv (deriv u) x|) volume (0 : ℝ) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hπ).mpr (by
      simpa only [Work.Spaces.Iθ] using hD2abs')
  -- the integral over `Iθ = [0, π/2]` is the interval integral over `0..π/2`.
  have hIeq : (∫ x in Work.Spaces.Iθ, |deriv (deriv u) x|)
      = ∫ x in (0 : ℝ)..(Real.pi / 2), |deriv (deriv u) x| := by
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hπ]
  rw [← hFTC, hD2]
  rcases le_total θ₀ θ with hle | hle
  · have h1 : |∫ x in θ₀..θ, deriv (deriv u) x| ≤ ∫ x in θ₀..θ, |deriv (deriv u) x| :=
      intervalIntegral.abs_integral_le_integral_abs hle
    have h2 : (∫ x in θ₀..θ, |deriv (deriv u) x|)
        ≤ ∫ x in Work.Spaces.Iθ, |deriv (deriv u) x| := by
      rw [hIeq]
      exact intervalIntegral.integral_mono_interval (le_of_lt hθ₀.1) hle (le_of_lt hθ.2)
        (Eventually.of_forall (fun x => abs_nonneg _)) hgi
    linarith
  · have h1 : |∫ x in θ..θ₀, deriv (deriv u) x| ≤ ∫ x in θ..θ₀, |deriv (deriv u) x| :=
      intervalIntegral.abs_integral_le_integral_abs hle
    have h2 : (∫ x in θ..θ₀, |deriv (deriv u) x|)
        ≤ ∫ x in Work.Spaces.Iθ, |deriv (deriv u) x| := by
      rw [hIeq]
      exact intervalIntegral.integral_mono_interval (le_of_lt hθ.1) hle (le_of_lt hθ₀.2)
        (Eventually.of_forall (fun x => abs_nonneg _)) hgi
    rw [intervalIntegral.integral_symm, abs_neg]
    linarith

end Work.FTS.EllipticEst.SgamBound
