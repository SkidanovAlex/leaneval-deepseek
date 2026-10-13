import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.slice_cs_weighted
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst

/-- If a smooth slice takes the same value at the two endpoints `0` and `π/2`, then its
derivative vanishes somewhere in `Iθ = [0, π/2]` (Rolle / Lagrange mean value theorem). -/
private lemma deriv_zero_exists_of_endpoints {u : ℝ → ℝ} (hsm : SliceSmooth u)
    (h0 : u 0 = u (Real.pi / 2)) : ∃ θ₀ ∈ Work.Spaces.Iθ, deriv u θ₀ = 0 := by
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsub2 : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) :=
    Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos])
  have hle : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcont : ContinuousOn u (Set.Icc (0 : ℝ) (Real.pi / 2)) := hsm.continuousOn.mono hsub
  have hdiff : DifferentiableOn ℝ u (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hsm.differentiableOn (by norm_num)).mono hsub2
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope u hle hcont hdiff
  refine ⟨c, ⟨le_of_lt hc.1, le_of_lt hc.2⟩, ?_⟩
  rw [hcd]
  have hz : u (Real.pi / 2) - u 0 = 0 := by rw [← h0]; ring
  simp [hz]

/-- The second derivative of a smooth slice is continuous on `Iθ`. -/
private lemma sliceV_continuousOn {u : ℝ → ℝ} (hsm : SliceSmooth u) :
    ContinuousOn (sliceV u) Work.Spaces.Iθ := by
  have hsub : Work.Spaces.Iθ ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (by norm_num)
  exact (hd1.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)).mono hsub

/-- If the derivative of a smooth slice vanishes at some `θ₀ ∈ Iθ`, then everywhere on `Iθ`
the derivative is bounded by the full integral of `|u''|` over `Iθ` (fundamental theorem of
calculus plus the triangle inequality for the integral). -/
private lemma abs_deriv_le_integral_abs_sliceV {u : ℝ → ℝ} (hsm : SliceSmooth u) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Work.Spaces.Iθ) (hz : deriv u θ₀ = 0) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |deriv u θ| ≤ ∫ x in Work.Spaces.Iθ, |sliceV u x| := by
  have hsub : Work.Spaces.Iθ ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont : ContinuousOn (sliceV u) Work.Spaces.Iθ := sliceV_continuousOn hsm
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hIeq : (∫ x in (0 : ℝ)..(Real.pi / 2), |sliceV u x|)
      = ∫ x in Work.Spaces.Iθ, |sliceV u x| := by
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    rfl
  have hgi : IntervalIntegrable (fun x => |sliceV u x|) volume 0 (Real.pi / 2) :=
    hcont.abs.intervalIntegrable_of_Icc hle
  intro θ hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ₀
  have huIcc : Set.uIcc θ₀ θ ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans hθ₀.1 h1, le_trans h2 hθ.2⟩
    · exact ⟨le_trans hθ.1 h1, le_trans h2 hθ₀.2⟩
  have hFTC : (∫ x in θ₀..θ, sliceV u x) = deriv u θ - deriv u θ₀ :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hd1.mono (huIcc.trans hsub))
  have hvaleq : deriv u θ = ∫ x in θ₀..θ, sliceV u x := by
    rw [hFTC, hz, sub_zero]
  rw [hvaleq]
  rcases le_total θ₀ θ with hle2 | hle2
  · have h1 : |∫ x in θ₀..θ, sliceV u x| ≤ ∫ x in θ₀..θ, |sliceV u x| :=
      intervalIntegral.abs_integral_le_integral_abs hle2
    have h2 : (∫ x in θ₀..θ, |sliceV u x|) ≤ ∫ x in Work.Spaces.Iθ, |sliceV u x| := by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval hθ₀.1 hle2 hθ.2
        (Eventually.of_forall (fun x => abs_nonneg _)) hgi
    linarith
  · have hsym : (∫ x in θ₀..θ, sliceV u x) = -(∫ x in θ..θ₀, sliceV u x) := intervalIntegral.integral_symm ..
    have h1 : |∫ x in θ..θ₀, sliceV u x| ≤ ∫ x in θ..θ₀, |sliceV u x| :=
      intervalIntegral.abs_integral_le_integral_abs hle2
    have h2 : (∫ x in θ..θ₀, |sliceV u x|) ≤ ∫ x in Work.Spaces.Iθ, |sliceV u x| := by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval hθ.1 hle2 hθ₀.2
        (Eventually.of_forall (fun x => abs_nonneg _)) hgi
    rw [hsym, abs_neg]
    linarith

/-- Boundary (FTC) bound for the first derivative of a smooth slice with equal endpoint values,
with `A = ∫_{Iθ} (u'')² sin(2θ)^{-η}`:

`(∂_θ u θ)² ≤ A · ∫_{Iθ} sin(2θ)^η`   for every `θ ∈ Iθ`.

Route: `∂_θ u` is continuous on `Iθ` and `∫_{Iθ} ∂_θ u = u(π/2) - u(0) = 0`
(`intervalIntegral.integral_deriv_of_contDiffOn_Icc`), so `∂_θ u` has a zero `θ₀` (a continuous
function on an interval whose integral vanishes cannot have a constant non-zero sign); then
`|∂_θ u θ| = |∫_{θ₀}^{θ} u''| ≤ ∫_{Iθ}|u''|`, and Cauchy–Schwarz (`Work.Spaces.cs_integral`)
applied to `|u''|·sin(2θ)^{-η/2}` and `sin(2θ)^{η/2}` — using `sin(2θ)^{-η} ≥ 1` on `Iθ` — gives
`(∫|u''|)² ≤ A · ∫ sin(2θ)^η`.  The hypothesis
`IntegrableOn (fun θ => (u'')² sin(2θ)^{-η}) Iθ` makes `A` honest (not the junk value `0`);
note `η = 99/100 < 1` so `∫_{Iθ} sin(2θ)^η ≤ π/2` is finite. -/
theorem slice_deriv_sq_le {u : ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SliceSmooth u)
    (h0 : u 0 = u (Real.pi / 2))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ) :
    ∀ θ ∈ Work.Spaces.Iθ, (deriv u θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.sliceV u θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := by
  -- Rolle: pick `θ₀ ∈ Iθ` with `deriv u θ₀ = 0` (the mean value theorem, since `u` has the
  -- same value at `0` and `π/2`).
  obtain ⟨θ₀, hθ₀, hz⟩ := deriv_zero_exists_of_endpoints hsm h0
  -- Cauchy–Schwarz on the slice, with the second derivative as the `g` of `slice_cs_weighted`.
  have hvcont : ContinuousOn (sliceV u) Work.Spaces.Iθ := sliceV_continuousOn hsm
  have hcs := slice_cs_weighted (g := sliceV u) hvcont hint
  intro θ hθ
  -- FTC from `θ₀` to `θ`: `deriv u θ = ∫_{θ₀}^{θ} u''`, hence `|deriv u θ| ≤ ∫_{Iθ} |u''|`.
  have habs := abs_deriv_le_integral_abs_sliceV hsm hθ₀ hz θ hθ
  have hsq : (deriv u θ) ^ 2 ≤ (∫ x in Work.Spaces.Iθ, |sliceV u x|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  linarith [hcs, hsq]

end Work.FTS.EllipticEst
