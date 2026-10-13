import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.AngGap.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AngGap.angPhiC_tendsto_zero
import Submission.Work.FTS.EllipticEst.AngGap.angPhiC_integrand_intervalIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap

/-- Hints: with `V = angV h = G/sin 2θ` and `G = angG h`, `hg` gives `V' = h - 2 cot(2θ) V`,
hence `(V h)' = h² + V (h' - 2 cot(2θ) h)`: the integrand
`F θ = h θ² + V θ (deriv h θ - 2 cot(2θ) h θ)` is the derivative on `(0,π/2)` of
`angPhiC h = V · h`, which tends to `0` at both endpoints by `squeeze_zero'` (`hCg` gives
`|V| ≤ C sin²2θ` and `hbdd` gives `|h| ≤ C sin 2θ`, so `|V h| ≤ C² sin³2θ`).  `F` is
continuous on `Ioo 0 (π/2)` and bounded there (`hbdd'` bounds `h'`), so it is
`IntervalIntegrable` on `0..π/2`; conclude with
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto` and the set-integral conversions.

The two analytic inputs are proved in the sibling files `AngGap/angPhiC_tendsto_zero`
(the vanishing of `angPhiC h` at both endpoints) and
`AngGap/angPhiC_integrand_intervalIntegrable` (interval integrability of `F`, of `h²` and
of `V · Q`). -/
theorem ibp (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (Work.FTS.EllipticEst.AngGap.angG h)
        (h θ * Real.sin (2 * θ)) θ)
    (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ))
    (hbdd' : ∀ θ ∈ Set.Ioo 0 (π / 2), |deriv h θ| ≤ C)
    (hCg : ∀ θ ∈ Set.Icc 0 (π / 2),
        |Work.FTS.EllipticEst.AngGap.angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2)
      = - (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngGap.angV h θ
            * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)) := by
  have hpi2 : (0 : ℝ) < π / 2 := by positivity
  -- ## the two analytic inputs
  obtain ⟨hintF, hintH, hintV⟩ :=
    angPhiC_integrand_intervalIntegrable h hh hg C hC hbdd hbdd' hCg
  obtain ⟨htend0, htendπ⟩ := angPhiC_tendsto_zero h C hC hbdd hCg
  -- ## derivative of the primitive `angPhiC h = V · h` on `(0,π/2)`
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), HasDerivAt (angPhiC h)
      ((h θ) ^ 2 + angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)) θ := by
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hsne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs
    have hG : HasDerivAt (angG h) (h θ * Real.sin (2 * θ)) θ := hg θ hθ
    have hH : HasDerivAt h (deriv h θ) θ :=
      ((hh.contDiffAt (Icc_mem_nhds hθ.1 hθ.2)).differentiableAt (by norm_num)).hasDerivAt
    have hs' : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * θ)) θ := by
      have h1 : HasDerivAt (fun θ : ℝ => 2 * θ) 2 θ := by
        simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
      simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    have hmain := HasDerivAt.div (hG.mul hH) hs' hsne
    have hfun : angPhiC h = (fun θ => angG h θ * h θ) / (fun θ : ℝ => Real.sin (2 * θ)) := by
      funext θ; simp only [angPhiC, angV, Pi.div_apply]; ring
    rw [hfun]
    refine hmain.congr_deriv ?_
    simp only [angV, Pi.mul_apply]
    rw [Real.cot_eq_cos_div_sin]
    field_simp
    ring_nf
  -- ## the fundamental theorem of calculus
  have hFTC : (∫ θ in (0 : ℝ)..(π / 2),
      ((h θ) ^ 2 + angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ))) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi2 hderiv hintF
      htend0 htendπ
    simpa using h
  have hsplit : (∫ θ in (0 : ℝ)..(π / 2),
        ((h θ) ^ 2 + angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)))
      = (∫ θ in (0 : ℝ)..(π / 2), (h θ) ^ 2)
        + (∫ θ in (0 : ℝ)..(π / 2), angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)) :=
    intervalIntegral.integral_add hintH hintV
  have hmain : (∫ θ in (0 : ℝ)..(π / 2), (h θ) ^ 2)
      = - (∫ θ in (0 : ℝ)..(π / 2), angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)) := by
    linarith
  -- ## transfer to the set integral over `Iθ`
  have hIθ : ∀ u : ℝ → ℝ, ∫ θ in Work.Spaces.Iθ, u θ = ∫ θ in (0 : ℝ)..(π / 2), u θ := by
    intro u
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi2.le]
  rw [hIθ (fun θ => (h θ) ^ 2),
    hIθ (fun θ => angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ))]
  simpa using hmain

end Work.FTS.EllipticEst.AngGap
