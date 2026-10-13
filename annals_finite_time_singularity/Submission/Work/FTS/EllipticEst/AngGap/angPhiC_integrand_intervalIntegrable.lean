/-
# Interval integrability of the integrand of the integration-by-parts identity `Φ_C`

With `V = angV h = angG h / sin 2θ` and `Q = h' - 2 cot(2θ) h`, the identity
`∫ h² = -∫ V Q` needs `h²`, `V Q` and their sum to be interval integrable on `0..π/2`.

Both are handled by the general criterion
`Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound`: continuity on the *open*
interval plus a bound there.  The endpoints are harmless (null set, and the expressions
involving `cot`/`sin` are only controlled on `(0,π/2)` anyway).

* `h²` is continuous because `h` is `C²` hence continuous on `Icc 0 (π/2)`, and
  `|h θ| ≤ C sin 2θ ≤ C` on `(0,π/2)` bounds it by `C²`.
* `V Q`: the two reusable facts proved in the sibling files
  `AngGap/angV_cont_bound_Ioo` and `AngGap/angQ_cont_bound_Ioo` give that `V` and
  `Q = angQ h` are continuous on `(0,π/2)`, with `|V θ| ≤ C sin²2θ` and `|Q θ| ≤ 3C`
  there (`|Q θ| ≤ |h' θ| + 2 |cot 2θ| |h θ| ≤ C + 2 (1/sin 2θ)(C sin 2θ) = 3C` from
  `hbdd`, `hbdd'` and `|cot| ≤ 1/sin`).  Hence the product is continuous on `(0,π/2)`
  and bounded by `(C sin²2θ)(3C) ≤ 3 C²` there.

The first conjunct then follows from `IntervalIntegrable.add`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.AngGap.Defs
import Submission.Work.FTS.EllipticEst.AngGap.angV_cont_bound_Ioo
import Submission.Work.FTS.EllipticEst.AngGap.angQ_cont_bound_Ioo
import Submission.Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.AngGap

set_option autoImplicit false

theorem angPhiC_integrand_intervalIntegrable (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (Work.FTS.EllipticEst.AngGap.angG h)
        (h θ * Real.sin (2 * θ)) θ)
    (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ))
    (hbdd' : ∀ θ ∈ Set.Ioo 0 (π / 2), |deriv h θ| ≤ C)
    (hCg : ∀ θ ∈ Set.Icc 0 (π / 2),
        |Work.FTS.EllipticEst.AngGap.angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    IntervalIntegrable (fun θ => (h θ) ^ 2 + Work.FTS.EllipticEst.AngGap.angV h θ
        * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)) volume 0 (π / 2) ∧
    IntervalIntegrable (fun θ => (h θ) ^ 2) volume 0 (π / 2) ∧
    IntervalIntegrable (fun θ => Work.FTS.EllipticEst.AngGap.angV h θ
        * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)) volume 0 (π / 2) := by
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  -- ## The square integrand
  have hsq : IntervalIntegrable (fun θ : ℝ => (h θ) ^ 2) volume 0 (π / 2) := by
    refine Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hle ?_ (C ^ 2) ?_
    · exact ((hh.mono Set.Ioo_subset_Icc_self).continuousOn).pow 2
    · intro θ hθ
      have hspos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
      have hsin1 : (Real.sin (2 * θ)) ^ 2 ≤ 1 :=
        pow_le_one₀ hspos.le (Real.sin_le_one (2 * θ))
      have hb := hbdd θ ⟨hθ.1.le, hθ.2.le⟩
      have h1 : |h θ| ^ 2 ≤ (C * Real.sin (2 * θ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
      have h2 : (C * Real.sin (2 * θ)) ^ 2 = C ^ 2 * (Real.sin (2 * θ)) ^ 2 := by ring
      calc |(h θ) ^ 2| = |h θ| ^ 2 := by rw [abs_pow]
        _ ≤ C ^ 2 * (Real.sin (2 * θ)) ^ 2 := by rw [← h2]; exact h1
        _ ≤ C ^ 2 * 1 := mul_le_mul_of_nonneg_left hsin1 (sq_nonneg C)
        _ = C ^ 2 := by ring
  -- ## Continuity and bound for `angV` and for `Q = angQ h` on the open interval (delegated)
  obtain ⟨hVcont, hVbdd⟩ := angV_cont_bound_Ioo h C hC hg hCg
  obtain ⟨hQcont, hQbdd⟩ := angQ_cont_bound_Ioo h hh C hC hbdd hbdd'
  have hVQcont : ContinuousOn
      (fun θ : ℝ => angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)) (Set.Ioo 0 (π / 2)) :=
    hVcont.mul hQcont
  have hVQbdd : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)| ≤ 3 * C ^ 2 := by
    intro θ hθ
    rw [abs_mul]
    have hv := hVbdd θ hθ
    have hq : |deriv h θ - 2 * Real.cot (2 * θ) * h θ| ≤ 3 * C := hQbdd θ hθ
    have hsin1 : (Real.sin (2 * θ)) ^ 2 ≤ 1 :=
      pow_le_one₀ (sin_two_pos hθ).le (Real.sin_le_one (2 * θ))
    have h1 : |angV h θ| * |deriv h θ - 2 * Real.cot (2 * θ) * h θ|
        ≤ (C * (Real.sin (2 * θ)) ^ 2) * (3 * C) :=
      mul_le_mul hv hq (abs_nonneg _) (by positivity)
    have h2 : (C * (Real.sin (2 * θ)) ^ 2) * (3 * C) ≤ 3 * C ^ 2 := by
      nlinarith [sq_nonneg C, hC]
    linarith
  -- ## The product integrand, and the assembly
  have hVQ : IntervalIntegrable
      (fun θ : ℝ => angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)) volume 0 (π / 2) :=
    Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hle hVQcont (3 * C ^ 2) hVQbdd
  exact ⟨hsq.add hVQ, hsq, hVQ⟩

end Work.FTS.EllipticEst.AngGap
