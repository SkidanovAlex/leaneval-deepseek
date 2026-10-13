import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ibp_contdiffon

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Auxiliary

open scoped Real Topology
open MeasureTheory Set Filter

/-- `deriv (sin (2θ)) = 2 cos (2θ)`. -/
lemma deriv_sin_two : deriv (fun θ : ℝ => Real.sin (2 * θ)) = fun θ : ℝ => 2 * Real.cos (2 * θ) := by
  funext θ
  have h1 : HasDerivAt (fun θ : ℝ => (2 : ℝ) * θ) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * θ)) θ := by
    simpa only [Function.comp_def, mul_comm] using ((Real.hasDerivAt_sin (2 * θ)).comp θ h1)
  exact h2.deriv

/-- `θ ↦ 2 cos (2θ)` is `C²`. -/
lemma contDiff_cos_two : ContDiff ℝ 2 (fun θ : ℝ => 2 * Real.cos (2 * θ)) := by
  have h2 : ContDiff ℝ 2 (fun θ : ℝ => (2 : ℝ) * θ) := contDiff_const.mul contDiff_id
  exact contDiff_const.mul (Real.contDiff_cos.comp h2)

/-- `deriv (2 cos (2θ)) = -4 sin (2θ)`. -/
lemma deriv_cos_two : deriv (fun θ : ℝ => 2 * Real.cos (2 * θ))
    = fun θ : ℝ => -4 * Real.sin (2 * θ) := by
  funext θ
  have h1 : HasDerivAt (fun θ : ℝ => (2 : ℝ) * θ) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun θ : ℝ => Real.cos (2 * θ)) (-Real.sin (2 * θ) * 2) θ := by
    simpa only [Function.comp_def, mul_comm] using ((Real.hasDerivAt_cos (2 * θ)).comp θ h1)
  have h3 : HasDerivAt (fun θ : ℝ => 2 * Real.cos (2 * θ)) (2 * (-Real.sin (2 * θ) * 2)) θ :=
    h2.const_mul 2
  rw [h3.deriv]
  ring

/-- Two integrations by parts against `sin (2θ)`: the boundary terms vanish because
`f` is `C²` on `[0,π/2]` and vanishes at both endpoints. -/
theorem pIBP_fts (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2))) (h0 : f 0 = 0)
    (h1 : f (π / 2) = 0) :
    (∫ θ in Work.Spaces.Iθ, deriv f θ * deriv (fun θ => Real.sin (2 * θ)) θ)
      = 4 * (∫ θ in Work.Spaces.Iθ, f θ * Real.sin (2 * θ)) := by
  have hpi : (0 : ℝ) < π / 2 := by positivity
  have hle : (0 : ℝ) ≤ π / 2 := hpi.le
  -- rewrite the set integrals over `Iθ = [0,π/2]` as interval integrals
  have hconv : ∀ g : ℝ → ℝ, ∫ θ in Work.Spaces.Iθ, g θ = ∫ θ in (0 : ℝ)..(π / 2), g θ := by
    intro g
    rw [show Work.Spaces.Iθ = Set.Icc 0 (π / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  rw [hconv (fun θ => deriv f θ * deriv (fun θ => Real.sin (2 * θ)) θ),
    hconv (fun θ => f θ * Real.sin (2 * θ))]
  -- replace `deriv (sin (2θ))` by `2 cos (2θ)`
  rw [intervalIntegral.integral_congr (fun θ _ => by rw [deriv_sin_two])]
  -- integration by parts against the `C²` function `θ ↦ 2 cos (2θ)`
  have hIBP := Work.FTS.EllipticEst.ibp_contdiffon hpi (h := f)
    (ψ := fun θ : ℝ => 2 * Real.cos (2 * θ)) hf contDiff_cos_two
  rw [hIBP]
  -- the boundary terms vanish
  have hb : f (π / 2) * (2 * Real.cos (2 * (π / 2))) - f 0 * (2 * Real.cos (2 * 0)) = 0 := by
    rw [h0, h1]
    ring
  rw [hb, zero_sub]
  -- evaluate the remaining integral
  have hIntEq : (∫ x in (0 : ℝ)..(π / 2), f x * deriv (fun θ : ℝ => 2 * Real.cos (2 * θ)) x)
      = ∫ x in (0 : ℝ)..(π / 2), (-4) * (f x * Real.sin (2 * x)) := by
    apply intervalIntegral.integral_congr
    intro x _
    rw [deriv_cos_two]
    ring
  rw [hIntEq, intervalIntegral.integral_const_mul]
  ring

end Work.FTS.EllipticEst.Auxiliary
