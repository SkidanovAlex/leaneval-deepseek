import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_XiAux
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_ZSBase
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_FarRepel_xiDerivPF
import Submission.Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero
import Submission.Work.LinnikAreas.xiCZeroInvSqTailBound
import Submission.Work.LinnikAreas.P3RectTuranOther.Work_LinnikAreas_TuranOther_xiZeroSumSummable

namespace Work.LinnikAreas.TuranOther

open scoped BigOperators

-- Route: `Work.LinnikAreas.FarRepel.xiDerivPF k hk` gives the closed-ball divisor sums
-- converging to `iteratedDeriv k (logDeriv Xi) s`; `Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero`
-- turns the (same) sums into `∑' u, ((divisor Xi univ u : ℤ) : ℂ) * (1/(s-u))^(k+1)`, which is the
-- stated tsum after `Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast` (Xi is entire);
-- uniqueness of limits then gives the identity. The `Summable` conjunct is the summability of the
-- same family: dominate `1/‖s-u‖^(k+1)` by `C/‖u‖^2` for `‖u‖ ≥ 2‖s‖+2` (zeros of `Xi` have
-- `u.re ≤ 1` by `DhK.Xi_zero_re_le_one`, so `‖s-u‖ ≥ s.re - 1` and `‖s-u‖ ≥ ‖u‖/2` far out), use
-- `Work.LinnikAreas.xiCZeroInvSqTailBound` for the tail and finiteness of the zeros of `Xi` in a
-- ball (`MeromorphicOn.divisor_support_finite_of_subset`) for the bounded part, and
-- `Commons.Analysis.InfiniteSum.summable_of_finset_tail_bound` (or `summable_of_sum_le`).
-- Do NOT import `Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect`, nor
-- `Submission.Commons.NumberTheory.DirichletCharacter.divisorSum_summable_and_tendsto`, nor
-- `Submission.Commons.NumberTheory.Zeta.xiE_partialFraction_eq`: they clash with `FarRepel.xiDerivPF`.
theorem xiDerivZeroSum (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun u : ℂ => (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ) * (1 / (s - u)) ^ (k + 1)) ∧
    iteratedDeriv k (logDeriv Work.LinnikAreas.DhK.Xi) s
      = (-1 : ℂ) ^ k * (k.factorial : ℂ)
        * (∑' u : ℂ, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ) * (1 / (s - u)) ^ (k + 1)) := by
  classical
  -- `s` is not a zero of `Xi`, since `1 < s.re`
  have hsne : Work.LinnikAreas.DhK.Xi s ≠ 0 :=
    Work.LinnikAreas.DhK.Xi_ne_zero_of_one_lt_re hs
  -- summability of the stated family (the same as the divisor family, see `hterm`)
  have hsumm : Summable (fun u : ℂ =>
      (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ) * (1 / (s - u)) ^ (k + 1)) :=
    xiZeroSumSummable k hk hs
  -- the global divisor of the entire function `Xi` is its order of vanishing
  have hdivu : ∀ u : ℂ,
      MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi Set.univ u
        = (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℤ) :=
    fun u => Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast
      (Work.LinnikAreas.DhK.Xi_analyticOnNhd Set.univ) (Set.mem_univ u)
  have hterm : ∀ u : ℂ,
      (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi Set.univ) u : ℤ) : ℂ)
          * (1 / (s - u)) ^ (k + 1)
        = (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ) * (1 / (s - u)) ^ (k + 1) := by
    intro u
    rw [hdivu u, Int.cast_natCast]
  -- the divisor family is summable
  have hsumm_div : Summable (fun u : ℂ =>
      (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi Set.univ) u : ℤ) : ℂ)
        * (1 / (s - u)) ^ (k + 1)) :=
    hsumm.congr fun u => (hterm u).symm
  -- the closed-ball divisor sums converge to the full divisor sum
  have htend := Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero
    (f := Work.LinnikAreas.DhK.Xi) (Φ := fun u : ℂ => (1 / (s - u)) ^ (k + 1))
    (Work.LinnikAreas.DhK.Xi_meromorphicOn Set.univ) hsumm_div
  have htend' : Filter.Tendsto (fun R : ℝ =>
      ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u)) ^ (k + 1)))
      Filter.atTop (nhds (((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
        (∑' u : ℂ, (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi Set.univ) u : ℤ) : ℂ)
          * (1 / (s - u)) ^ (k + 1)))) :=
    htend.const_mul ((-1 : ℂ) ^ k * (k.factorial : ℂ))
  -- the partial-fraction expansion
  have hPF := Work.LinnikAreas.FarRepel.xiDerivPF k hk s hsne
  have hkey := tendsto_nhds_unique hPF htend'
  have htsum : (∑' u : ℂ, (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi Set.univ) u : ℤ) : ℂ)
        * (1 / (s - u)) ^ (k + 1))
      = ∑' u : ℂ, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
        * (1 / (s - u)) ^ (k + 1) :=
    tsum_congr hterm
  exact ⟨hsumm, by rw [hkey, htsum]⟩

end Work.LinnikAreas.TuranOther
