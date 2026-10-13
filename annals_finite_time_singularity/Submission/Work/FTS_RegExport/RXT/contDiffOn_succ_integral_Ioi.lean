import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi
import Submission.Work.FTS.PhiStar.Radial.integrableOn_Ioi_of_Ioi_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.contDiffOn_succ_integral_Ioi`

`z ↦ ∫_r in (z,∞) h r` is `C^{n+1}` on `(0,∞)` for `h` of class `C^n` on `(0,∞)`.

The proof splits on whether `h` is integrable on `(1,∞)`:

* if it is, then (`h` being continuous on `(0,∞)`) it is integrable on `(z,∞)` for every `z > 0`,
  and the fundamental theorem for the tail integral (`Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi`)
  gives `HasDerivAt (fun z => ∫_r in (z,∞) h r) (-(h z)) z`; the criterion
  `contDiffOn_succ_iff_deriv_of_isOpen` finishes, using `ContDiffOn ℝ n (fun z => -(h z))`;
* if it is not, then (again by continuity on `(0,∞)`) `h` is integrable on no `(z,∞)`, so the
  integral is the junk value `0` and the function is constant.
-/

namespace Work.FTS_RegExport.RXT

/-- If `h` is continuous on `(0,∞)` and not integrable on `(1,∞)`, then it is integrable on no
half-line `(z,∞)`, `z > 0`: continuity on `(0,∞)` forces integrability on the half-lines to be
independent of `z`. -/
private theorem not_integrableOn_Ioi_of_not_integrableOn_Ioi_one {h : ℝ → ℝ}
    (hcont : ContinuousOn h (Set.Ioi 0)) (h1 : ¬ MeasureTheory.IntegrableOn h (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ¬ MeasureTheory.IntegrableOn h (Set.Ioi z) := by
  intro z hz hzint
  rcases le_or_gt z 1 with hz1 | hz1
  · exact h1 (hzint.mono_set (Set.Ioi_subset_Ioi hz1))
  · have hc1 : ContinuousOn h (Set.Icc 1 z) :=
      hcont.mono (fun x hx => lt_of_lt_of_le zero_lt_one hx.1)
    have hJ : MeasureTheory.IntegrableOn h (Set.Ioc 1 z) :=
      (hc1.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hU : MeasureTheory.IntegrableOn h (Set.Ioc 1 z ∪ Set.Ioi z) := hJ.union hzint
    exact h1 (hU.mono_set (fun x hx => by
      rcases le_or_gt x z with hxz | hxz
      · exact Or.inl ⟨hx, hxz⟩
      · exact Or.inr hxz))

/-- **Smoothness of the primitive over the half-line.**  For `h` of class `C^n` on `(0,∞)`,
the function `z ↦ ∫_r in (z,∞) h r` is of class `C^{n+1}` on `(0,∞)`.

Two cases: either `h` is integrable on `(a,∞)` for one (hence every) `a > 0`, in which case
`∫_{(z,∞)} h = ∫_{(a,∞)} h - ∫_a^z h` on `z > a` is a constant minus a primitive of `h`; or
`h` is integrable on no `(z,∞)`, `z > 0` (since `h` is locally bounded, once it is integrable
on one half-line it is integrable on all of them), in which case the integral is the junk value
`0` (`MeasureTheory.integral_undef`) and the function is identically zero. -/
theorem contDiffOn_succ_integral_Ioi {n : ℕ} {h : ℝ → ℝ}
    (hc : ContDiffOn ℝ n h (Set.Ioi 0)) :
    ContDiffOn ℝ (n + 1) (fun z => ∫ r in Set.Ioi z, h r) (Set.Ioi 0) := by
  have hcont : ContinuousOn h (Set.Ioi 0) := hc.continuousOn
  by_cases hint : MeasureTheory.IntegrableOn h (Set.Ioi 1)
  · -- integrable case: `F` has derivative `-h`, and `h` is `C^n`
    have hderiv : ∀ z ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun u => ∫ t in Set.Ioi u, h t) (-(h z)) z := by
      intro z hz
      have hz2 : (0 : ℝ) < z / 2 := by
        have : (0 : ℝ) < z := hz
        linarith
      exact Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi (a := z / 2) (z := z) (by linarith)
        (hcont.mono (fun t ht => lt_trans hz2 ht))
        (Work.FTS.PhiStar.Radial.integrableOn_Ioi_of_Ioi_Ioo hz2 hcont hint)
    rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨?_, ?_, ?_⟩
    · exact fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt
    · intro htop
      exact absurd htop (by simp)
    · exact (hc.neg).congr (fun z hz => (hderiv z hz).deriv)
  · -- junk case: `F` is identically `0` on `(0,∞)`
    have hni := not_integrableOn_Ioi_of_not_integrableOn_Ioi_one hcont hint
    have hzero : ∀ z ∈ Set.Ioi (0 : ℝ), (∫ t in Set.Ioi z, h t) = 0 := by
      intro z hz
      exact MeasureTheory.integral_undef (μ := MeasureTheory.volume.restrict (Set.Ioi z))
        (hni z hz)
    exact ContDiffOn.congr contDiffOn_const (fun z hz => (hzero z hz))

end Work.FTS_RegExport.RXT
