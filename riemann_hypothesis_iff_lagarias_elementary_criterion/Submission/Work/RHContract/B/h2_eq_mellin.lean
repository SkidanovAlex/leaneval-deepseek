import Mathlib
import Submission.Work.RHContract.B.PhiSecondDerivDefs

/-!
# `h₂` as a Mellin transform: `h₂(s) = mellin psiSubIdCut (−s − 1)`

The Landau step of the route integrates the correlation function `ψ t − t` twice; the second
power of the variable is exactly a Mellin transform of the cut-off correlation function
`psiSubIdCut = 1_{t > 2}(ψ t − t)`:

`h₂(s) = ∫_2^∞ (ψ t − t) t^{−s−2} dt
      = ∫_0^∞ t^{(−s−1)−1} · 1_{t>2}(ψ t − t) dt
      = mellin psiSubIdCut (−s − 1)`.

The reduction uses only that `psiSubIdCut` is an indicator: the integrand of the Mellin transform
is the same indicator times `t^{−s−2}`, so its integral over `(0, ∞)` is the integral over
`(2, ∞) = (0, ∞) ∩ (2, ∞)`, where the indicator is invisible. This is an identity of *Bochner*
integrals and hence holds for every `s : ℂ` — for those `s` where the integral diverges both sides
vanish by the `integral_undef` convention, so no integrability hypothesis is needed.
-/

namespace Work.RHContract.B

open MeasureTheory

noncomputable section

theorem h2_eq_mellin (s : ℂ) :
    Work.RHContract.Landau.h2 s = mellin Work.RHContract.B.psiSubIdCut (-s - 1) := by
  -- Unfold the Mellin transform: the exponent becomes `-s - 2`.
  rw [mellin, show (-s - 1) - 1 = -s - 2 from by ring]
  -- Push the weight `t^{-s-2}` inside the indicator defining `psiSubIdCut`.
  have hfun : Set.EqOn (fun t : ℝ => (t : ℂ) ^ (-s - 2) • Work.RHContract.B.psiSubIdCut t)
      ((Set.Ioi 2).indicator (fun u : ℝ => (u : ℂ) ^ (-s - 2) • ((Chebyshev.psi u - u : ℝ) : ℂ)))
      (Set.Ioi 0) := by
    intro t ht
    dsimp only
    by_cases h : t ∈ Set.Ioi 2
    · rw [Work.RHContract.B.psiSubIdCut_apply_of_gt h, Set.indicator_of_mem h]
    · rw [Work.RHContract.B.psiSubIdCut_apply_of_le (le_of_not_gt h), Set.indicator_of_notMem h,
        smul_zero]
  -- The integral over `(0, ∞)` of an indicator on `(2, ∞)` is the integral over `(2, ∞)`.
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hfun,
    MeasureTheory.setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi,
    max_eq_right (by norm_num : (0:ℝ) ≤ 2)]
  -- Compare with the definition of `h₂`; only the order of the factors differs, and the cast of
  -- the subtraction is `Complex.ofReal_sub`.
  simp only [Work.RHContract.Landau.h2]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [smul_eq_mul, Complex.ofReal_sub, mul_comm]

end

end Work.RHContract.B
