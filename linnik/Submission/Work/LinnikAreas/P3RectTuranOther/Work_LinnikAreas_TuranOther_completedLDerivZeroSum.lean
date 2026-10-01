import Mathlib
import Submission.Work.LinnikAreas.TuranOther.PFZeroSumDefs
import Submission.Work.LinnikAreas.P3Rect.Work_ZeroFreeTables_P3_CompletedDerivPF
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_FarRepel_divisorSumBallTendsto
import Submission.Work.LinnikAreas.FarRepel.invSubPowLeInvSq
import Submission.Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero

open scoped BigOperators

namespace Work.LinnikAreas.TuranOther

/-- The partial-fraction weight `(t-u)^{-(k+1)}` in the "geometric" form `(1/(t-u))^{k+1}`, which
is how the summability input `divisorSumBallTendsto` is stated. -/
lemma neg_zpow_eq_one_div_pow (z : ℂ) (k : ℕ) :
    z ^ (-(k + 1) : ℤ) = (1 / z) ^ (k + 1) := by
  rw [show (-(k + 1) : ℤ) = -((k + 1 : ℕ) : ℤ) by push_cast; ring]
  rw [zpow_neg, zpow_natCast, one_div, inv_pow]

theorem completedLDerivZeroSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 1 < t.re) :
    Summable (fun u : ℂ =>
        ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℂ)
          * (t - u) ^ (-(k + 1) : ℤ)) ∧
      iteratedDeriv k (logDeriv (DirichletCharacter.completedLFunction χ)) t =
        (-1 : ℂ) ^ k * (k.factorial : ℂ)
          * Work.LinnikAreas.TuranOther.zeroSumK (DirichletCharacter.completedLFunction χ) t k := by
  classical
  have hΛdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction hχ
  -- `Λ t ≠ 0` since `1 < Re t`
  have hΛne : DirichletCharacter.completedLFunction χ t ≠ 0 := by
    intro h0
    have ht0 : t ≠ 0 := by intro h; rw [h] at ht; norm_num at ht
    have ht1 : t ≠ 1 := by intro h; rw [h] at ht; norm_num at ht
    have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ t (Or.inl ht0)
    rw [h0, zero_div] at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr ht1) (le_of_lt ht) h
  -- inverse-square domination of the weight on the critical strip
  obtain ⟨A, hA, hAb⟩ := Work.LinnikAreas.FarRepel.invSubPowLeInvSq ht k hk
  -- summability of the divisor sum, and convergence of the closed-ball partial sums
  obtain ⟨hsum, htend⟩ := Work.LinnikAreas.FarRepel.divisorSumBallTendsto χ hχ hprim hA
    (fun u h1 h2 h3 => hAb u h1 h2 h3)
  -- the partial-fraction identity for the `k`-th derivative
  have hPF := Work.ZeroFreeTables.P3.CompletedDerivPF_identity χ hχ hprim k hk t hΛne
  have hlim := htend.const_mul ((-1 : ℂ) ^ k * (k.factorial : ℂ))
  have hkey := tendsto_nhds_unique hPF hlim
  -- the global divisor is the analytic order of vanishing
  have hdivu : ∀ u : ℂ,
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ u
        = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℤ) :=
    fun u => Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast
      (fun z _ => hΛdiff.analyticAt z) (Set.mem_univ u)
  have hterm : ∀ u : ℂ,
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ)
          * (1 / (t - u)) ^ (k + 1)
        = ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℂ)
          * (t - u) ^ (-(k + 1) : ℤ) := by
    intro u
    rw [hdivu u, Int.cast_natCast, neg_zpow_eq_one_div_pow]
  constructor
  · exact hsum.congr hterm
  · rw [Work.ZeroFreeTables.P3.logDeriv_eq_div]
    rw [hkey]
    congr 1
    unfold zeroSumK
    exact tsum_congr hterm

end Work.LinnikAreas.TuranOther
