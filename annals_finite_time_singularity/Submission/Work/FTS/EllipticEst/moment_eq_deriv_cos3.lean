import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.contDiffOn_one_bounds
import Submission.Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The antiderivative of `sinCos2 θ = sin θ cos²θ` that vanishes at `θ = π/2`:
`g θ = -(1/3) cos³θ`. -/
def cosCube (θ : ℝ) : ℝ := -(1 / 3) * Real.cos θ ^ 3

theorem hasDerivAt_cosCube (θ : ℝ) : HasDerivAt cosCube (Work.Elliptic.sinCos2 θ) θ := by
  have h : HasDerivAt (fun θ : ℝ => Real.cos θ ^ 3)
      (3 * Real.cos θ ^ (3 - 1) * (-Real.sin θ)) θ := (Real.hasDerivAt_cos θ).pow 3
  have h2 : HasDerivAt (fun θ : ℝ => -(1 / 3) * Real.cos θ ^ 3)
      (-(1 / 3) * (3 * Real.cos θ ^ (3 - 1) * (-Real.sin θ))) θ := h.const_mul (-(1 / 3))
  show HasDerivAt (fun θ : ℝ => -(1 / 3) * Real.cos θ ^ 3) (Work.Elliptic.sinCos2 θ) θ
  convert h2 using 1
  simp only [Work.Elliptic.sinCos2]
  ring

theorem continuousOn_cosCube : Continuous cosCube := by
  unfold cosCube
  fun_prop

theorem cosCube_pi_half : cosCube (π / 2) = 0 := by
  simp [cosCube]

theorem cosCube_zero : cosCube 0 = -(1 / 3) := by
  simp [cosCube]

/-- `deriv f` is continuous on the open interval `(0, π/2)` when `f` is `C¹` on the closed
interval: at interior points the two-sided derivative agrees with the one-sided one, and the
latter is continuous on the compact interval. -/
theorem continuousOn_deriv_Ioo_of_contDiffOn {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (π / 2))) :
    ContinuousOn (deriv f) (Set.Ioo 0 (π / 2)) := by
  have hpos : (0 : ℝ) < π / 2 := by positivity
  have hUniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (π / 2)) := uniqueDiffOn_Icc hpos
  have hcont : ContinuousOn (derivWithin f (Set.Icc (0 : ℝ) (π / 2)))
      (Set.Icc (0 : ℝ) (π / 2)) := hf.continuousOn_derivWithin hUniq le_rfl
  refine (hcont.mono Set.Ioo_subset_Icc_self).congr ?_
  intro x hx
  exact (derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)).symm

/-- At an interior point of `[0, π/2]`, a function that is `C¹` on the closed interval has a
(two-sided) derivative there, equal to `deriv f`. -/
theorem hasDerivAt_of_mem_Ioo_of_contDiffOn {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (π / 2))) {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt f (deriv f x) x := by
  have hmem : x ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨hx.1.le, hx.2.le⟩
  have hnhds : Set.Icc (0 : ℝ) (π / 2) ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
  exact (((hf.contDiffWithinAt hmem).differentiableWithinAt one_ne_zero).differentiableAt
    hnhds).hasDerivAt

/-- `deriv f` is interval integrable on `[0, π/2]` for `f` of class `C¹` there: it is
continuous on the open interval and bounded there by the bound of
`Work.Elliptic.contDiffOn_one_bounds`. -/
theorem intervalIntegrable_deriv_of_contDiffOn {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (π / 2))) (h0 : f 0 = 0) (hπ : f (π / 2) = 0) :
    IntervalIntegrable (deriv f) volume (0 : ℝ) (π / 2) := by
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  obtain ⟨C, -, -, hbound⟩ := Work.Elliptic.contDiffOn_one_bounds hf h0 hπ
  exact Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hpi
    (continuousOn_deriv_Ioo_of_contDiffOn hf) C (fun x hx => by
      simpa [Real.norm_eq_abs] using hbound x hx)

/-- Interval-integral form of the target identity, proved by integration by parts against the
antiderivative `cosCube` of `sinCos2`. -/
theorem intervalIntegral_moment_eq_deriv_cos3 (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (π / 2))) (h0 : f 0 = 0) (hπ : f (π / 2) = 0) :
    ∫ x in (0 : ℝ)..(π / 2), f x * Work.Elliptic.sinCos2 x
      = (1 / 3) * ∫ x in (0 : ℝ)..(π / 2), deriv f x * (Real.cos x) ^ 3 := by
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  have hminmax : Set.Ioo (min (0 : ℝ) (π / 2)) (max (0 : ℝ) (π / 2)) = Set.Ioo 0 (π / 2) := by
    rw [min_eq_left hpi, max_eq_right hpi]
  have hfcont : ContinuousOn f (Set.uIcc (0 : ℝ) (π / 2)) := by
    rw [Set.uIcc_of_le hpi]
    exact hf.continuousOn
  have hgcont : ContinuousOn cosCube (Set.uIcc (0 : ℝ) (π / 2)) :=
    continuousOn_cosCube.continuousOn
  have hsc : ContinuousOn Work.Elliptic.sinCos2 (Set.uIcc (0 : ℝ) (π / 2)) := by
    rw [Set.uIcc_of_le hpi]
    refine (ContinuousOn.mul Real.continuous_sin.continuousOn
      (Real.continuous_cos.continuousOn.pow 2)).congr ?_
    intro x _
    rfl
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := f) (v := cosCube) (u' := deriv f) (v' := Work.Elliptic.sinCos2)
    (a := (0 : ℝ)) (b := π / 2) hfcont hgcont
    (fun x hx => hasDerivAt_of_mem_Ioo_of_contDiffOn hf (by rw [hminmax] at hx; exact hx))
    (fun x _ => hasDerivAt_cosCube x)
    (intervalIntegrable_deriv_of_contDiffOn hf h0 hπ)
    hsc.intervalIntegrable
  have hbnd : f (π / 2) * cosCube (π / 2) - f 0 * cosCube 0 = 0 := by
    rw [h0, hπ]; ring
  rw [hbnd, zero_sub] at hIBP
  have hfun : (fun x : ℝ => deriv f x * cosCube x)
      = fun x : ℝ => (-(1 / 3)) * (deriv f x * Real.cos x ^ 3) := by
    funext x
    simp only [cosCube]
    ring
  rw [hfun, intervalIntegral.integral_const_mul] at hIBP
  rw [hIBP]
  ring

theorem moment_eq_deriv_cos3 (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (π / 2)))
    (h0 : f 0 = 0) (hπ : f (π / 2) = 0) :
    ∫ θ in Work.Spaces.Iθ, f θ * Work.Elliptic.sinCos2 θ
      = (1 / 3) * ∫ θ in Work.Spaces.Iθ, deriv f θ * (Real.cos θ) ^ 3 := by
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  have hconv : ∀ g : ℝ → ℝ, ∫ θ in Work.Spaces.Iθ, g θ = ∫ θ in (0 : ℝ)..(π / 2), g θ := by
    intro g
    rw [show Work.Spaces.Iθ = Set.Icc 0 (π / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi]
  rw [hconv (fun θ => f θ * Work.Elliptic.sinCos2 θ),
    hconv (fun θ => deriv f θ * (Real.cos θ) ^ 3)]
  exact intervalIntegral_moment_eq_deriv_cos3 f hf h0 hπ

end Work.FTS.EllipticEst
