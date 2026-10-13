import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.OpenFTC

/-- **FTC bound on an open interval.**  If `f` is `C¹` on the *open* interval `(0, π/2)`, vanishes
at some point `c` of that interval, and `|f'|` is integrable on the closed interval `Iθ = [0, π/2]`,
then `|f θ| ≤ ∫_{Iθ} |f'|` for every interior `θ ∈ (0, π/2)`.  Proof: the FTC on the segment
`[c, θ] ⊆ (0, π/2)` gives `f θ = ∫_c^θ f'`, and monotonicity of the integral of the nonnegative
`|f'|` bounds this by the integral over `Iθ`. -/
theorem absFtcLeIntegralAbsDeriv {f : ℝ → ℝ} {c : ℝ}
    (hcd : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    (hc : c ∈ Set.Ioo 0 (Real.pi / 2)) (hfz : f c = 0)
    (hint : MeasureTheory.IntegrableOn (fun s : ℝ => |deriv f s|) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ ∫ s in Work.Spaces.Iθ, |deriv f s| := by
  -- `Iθ = [0, π/2]` is the interval of integration, and the interval integral of a function
  -- agrees with the set integral over `Iθ`.
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hIeq : (∫ x in (0 : ℝ)..(Real.pi / 2), |deriv f x|)
      = ∫ s in Work.Spaces.Iθ, |deriv f s| := by
    rw [intervalIntegral.integral_of_le hle, Work.Spaces.Iθ,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- integrability of `|f'|` on the whole interval `[0, π/2]`, in interval-integral form
  have hgi : IntervalIntegrable (fun x : ℝ => |deriv f x|) volume 0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hle]
    exact hint.mono_set Set.Ioc_subset_Icc_self
  intro θ hθ
  -- the segment `[c, θ]` lies in the open interval where `f` is `C¹`
  have hsub : Set.uIcc c θ ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hc.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hc.2⟩
  -- the fundamental theorem of calculus on that segment
  have hFTC : (∫ x in c..θ, deriv f x) = f θ - f c :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hcd.mono hsub)
  have hfθ : f θ = ∫ x in c..θ, deriv f x := by rw [hFTC, hfz, sub_zero]
  rw [hfθ]
  rcases le_total c θ with hct | htc
  · -- `θ` is to the right of `c`
    have h1 : |∫ x in c..θ, deriv f x| ≤ ∫ x in c..θ, |deriv f x| :=
      intervalIntegral.abs_integral_le_integral_abs (f := fun x => deriv f x) hct
    have h2 : (∫ x in c..θ, |deriv f x|) ≤ ∫ x in Work.Spaces.Iθ, |deriv f x| := by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval hc.1.le hct hθ.2.le
        (Eventually.of_forall (fun x => abs_nonneg _)) hgi
    linarith
  · -- `θ` is to the left of `c`: reverse the orientation of the interval integral
    have hsym : (∫ x in c..θ, deriv f x) = -(∫ x in θ..c, deriv f x) := by
      rw [intervalIntegral.integral_symm (a := c) (b := θ)]
      ring
    have h1 : |∫ x in θ..c, deriv f x| ≤ ∫ x in θ..c, |deriv f x| :=
      intervalIntegral.abs_integral_le_integral_abs (f := fun x => deriv f x) htc
    have h2 : (∫ x in θ..c, |deriv f x|) ≤ ∫ x in Work.Spaces.Iθ, |deriv f x| := by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval hθ.1.le htc hc.2.le
        (Eventually.of_forall (fun x => abs_nonneg _)) hgi
    rw [hsym, abs_neg]
    linarith

end Work.FTS.EllipticEst.OpenFTC
