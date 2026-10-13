/-
Copyright: work module for the Elgindi finite-time singularity project.

# The first two one-dimensional slice bounds in the honest `C^∞` class

The slice estimates `Work.FTS.EllipticEst.slice_deriv_sq_le` and
`Work.FTS.EllipticEst.Blocks.slice_self_sq_le` are stated for the class
`Work.FTS.EllipticEst.SliceSmooth u = ContDiffOn ℝ ⊤ u (Ioo (-1) (π/2+1))`, which in this
Mathlib is *analyticity* (`⊤ = ω` in `ℕ∞ω = WithTop ℕ∞`) and is therefore unavailable for the
merely `C^∞` slices of the angular Poincaré estimate.

This module redoes both in the honest `C^∞` class `ThetaU.SliceSmoothO u =
ContDiffOn ℝ ∞ u (Ioo (-1) (π/2+1))`.  Every use of the smoothness hypothesis in the original
proofs is order-uniform (`hsm.continuousOn`, `hsm.differentiableOn (by norm_num)`,
`hsm.deriv_of_isOpen isOpen_Ioo (by norm_num)`, `hsm.of_le …`), so the proofs are copied
verbatim with `SliceSmoothO` in place of `SliceSmooth`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.slice_cs_weighted
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false

/-- If a `C^∞` slice takes the same value at the two endpoints `0` and `π/2`, then its
derivative vanishes somewhere in `Iθ = [0, π/2]` (Rolle / Lagrange mean value theorem). -/
private lemma deriv_zero_exists_of_endpoints {u : ℝ → ℝ} (hsm : SliceSmoothO u)
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

/-- The second derivative of a `C^∞` slice is continuous on `Iθ`. -/
private lemma sliceV_continuousOn {u : ℝ → ℝ} (hsm : SliceSmoothO u) :
    ContinuousOn (sliceV u) Work.Spaces.Iθ := by
  have hsub : Work.Spaces.Iθ ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (by norm_num)
  exact (hd1.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)).mono hsub

/-- If the derivative of a `C^∞` slice vanishes at some `θ₀ ∈ Iθ`, then everywhere on `Iθ`
the derivative is bounded by the full integral of `|u''|` over `Iθ` (fundamental theorem of
calculus plus the triangle inequality for the integral). -/
private lemma abs_deriv_le_integral_abs_sliceV {u : ℝ → ℝ} (hsm : SliceSmoothO u) {θ₀ : ℝ}
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
  · have hsym : (∫ x in θ₀..θ, sliceV u x) = -(∫ x in θ..θ₀, sliceV u x) :=
      intervalIntegral.integral_symm ..
    have h1 : |∫ x in θ..θ₀, sliceV u x| ≤ ∫ x in θ..θ₀, |sliceV u x| :=
      intervalIntegral.abs_integral_le_integral_abs hle2
    have h2 : (∫ x in θ..θ₀, |sliceV u x|) ≤ ∫ x in Work.Spaces.Iθ, |sliceV u x| := by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval hθ.1 hle2 hθ₀.2
        (Eventually.of_forall (fun x => abs_nonneg _)) hgi
    rw [hsym, abs_neg]
    linarith

/-- Boundary (FTC) bound for the first derivative of a `C^∞` slice with equal endpoint values,
with `A = ∫_{Iθ} (u'')² sin(2θ)^{-η}`:

`(∂_θ u θ)² ≤ A · ∫_{Iθ} sin(2θ)^η`   for every `θ ∈ Iθ`.

This is `Work.FTS.EllipticEst.slice_deriv_sq_le` with the analytic class `SliceSmooth` replaced
by the honest `C^∞` class `SliceSmoothO`. -/
theorem slice_deriv_sq_le_open {u : ℝ → ℝ} (hsm : SliceSmoothO u)
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
  have hcs := Work.FTS.EllipticEst.slice_cs_weighted (g := sliceV u) hvcont hint
  intro θ hθ
  -- FTC from `θ₀` to `θ`: `deriv u θ = ∫_{θ₀}^{θ} u''`, hence `|deriv u θ| ≤ ∫_{Iθ} |u''|`.
  have habs := abs_deriv_le_integral_abs_sliceV hsm hθ₀ hz θ hθ
  have hsq : (deriv u θ) ^ 2 ≤ (∫ x in Work.Spaces.Iθ, |sliceV u x|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  linarith [hcs, hsq]

/-- **Boundary bound for a `C^∞` slice vanishing at both angular endpoints.**  With
`A = ∫_{Iθ} (u'')² sin(2θ)^{-η}` (an honest finite number by the hypothesis),

`(u θ)² ≤ (π/2)² · A · ∫_{Iθ} sin(2θ)^η`   for every `θ ∈ Iθ`.

This is `Work.FTS.EllipticEst.Blocks.slice_self_sq_le` with the analytic class `SliceSmooth`
replaced by the honest `C^∞` class `SliceSmoothO`, and calling the `C^∞` version
`slice_deriv_sq_le_open` above. -/
theorem slice_self_sq_le_open {u : ℝ → ℝ} (hsm : SliceSmoothO u)
    (h0 : u 0 = 0) (h1 : u (Real.pi / 2) = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ) :
    ∀ θ ∈ Work.Spaces.Iθ, (u θ) ^ 2
      ≤ (Real.pi / 2) ^ 2 * ((∫ θ in Work.Spaces.Iθ,
            (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))) := by
  -- The slice vanishes at both angular endpoints, so `slice_deriv_sq_le_open` (proved for equal
  -- endpoint values) bounds `(∂_θ u)²` by `A · ∫ sin(2θ)^η` on all of `Iθ`.
  have hend : u 0 = u (Real.pi / 2) := by rw [h0, h1]
  have hderiv := slice_deriv_sq_le_open hsm hend hint
  -- `u` is `C¹` on a neighbourhood of `Iθ`, hence on every sub-interval `uIcc 0 θ`.
  have hcd : ContDiffOn ℝ 1 u (Set.Ioo (-1) (Real.pi / 2 + 1)) := hsm.of_le 1
  intro θ hθ
  have hθI := hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθI
  have hθ0 : (0 : ℝ) ≤ θ := hθI.1
  have hθpi : θ ≤ Real.pi / 2 := hθI.2
  -- abbreviations for the two integrals of the statement
  set A : ℝ := ∫ θ in Work.Spaces.Iθ,
      (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hA
  set B : ℝ := ∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (Work.Spaces.eta) with hB
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x hx => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hx))
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x hx => Real.rpow_nonneg (Work.FTS.EllipticEst.sin_two_nonneg hx) _)
  have hAB : 0 ≤ A * B := mul_nonneg hA0 hB0
  -- pointwise bound for the first derivative on `Iθ`
  have hderivAB : ∀ x ∈ Work.Spaces.Iθ, (deriv u x) ^ 2 ≤ A * B := hderiv
  have hpoint : ∀ x ∈ Work.Spaces.Iθ, |deriv u x| ≤ Real.sqrt (A * B) := fun x hx =>
    Real.abs_le_sqrt (hderivAB x hx)
  -- fundamental theorem of calculus: `u θ = ∫_0^θ ∂_θ u` (and `u 0 = 0`)
  have huIcc : Set.uIcc (0 : ℝ) θ ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hFTC : (∫ x in (0 : ℝ)..θ, deriv u x) = u θ - u 0 :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hcd.mono huIcc)
  have hu_eq : u θ = ∫ x in (0 : ℝ)..θ, deriv u x := by rw [hFTC, h0]; ring
  -- the integral is bounded by the length of the interval times the pointwise bound
  have hbd : ∀ x ∈ Set.uIoc (0 : ℝ) θ, ‖deriv u x‖ ≤ Real.sqrt (A * B) := by
    intro x hx
    rw [Set.mem_uIoc] at hx
    have hxI : x ∈ Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨le_of_lt h1, le_trans h2 hθpi⟩
      · exact ⟨le_trans hθ0 (le_of_lt h1), by linarith [h2, Real.pi_pos]⟩
    rw [Real.norm_eq_abs]
    exact hpoint x hxI
  have hnorm : ‖∫ x in (0 : ℝ)..θ, deriv u x‖ ≤ Real.sqrt (A * B) * |θ - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hbd
  have habs : |u θ| ≤ Real.sqrt (A * B) * (Real.pi / 2) := by
    have h1' : ‖u θ‖ ≤ Real.sqrt (A * B) * |θ - 0| := by
      rw [hu_eq]; exact hnorm
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hθ0), sub_zero] at h1'
    exact le_trans h1' (mul_le_mul_of_nonneg_left hθpi (Real.sqrt_nonneg _))
  have hsq : (u θ) ^ 2 ≤ (Real.sqrt (A * B) * (Real.pi / 2)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  calc (u θ) ^ 2 ≤ (Real.sqrt (A * B) * (Real.pi / 2)) ^ 2 := hsq
    _ = (Real.sqrt (A * B)) ^ 2 * (Real.pi / 2) ^ 2 := by ring
    _ = (A * B) * (Real.pi / 2) ^ 2 := by rw [Real.sq_sqrt hAB]
    _ = (Real.pi / 2) ^ 2 * (A * B) := by ring

end Work.FTS.EllipticEst.ThetaU
