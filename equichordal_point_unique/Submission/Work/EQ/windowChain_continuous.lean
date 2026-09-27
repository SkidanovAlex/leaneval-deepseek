import Mathlib
import Submission.Work.EQ.chain_family_defs

namespace Work.EQ

/-- **Continuity of the chain built from a window.**  The map
`t ↦ windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β t` is continuous on the punctured disc.
Each projection `t ↦ (windowChain … t).1 n` is, for fixed `n`, one of the three formulas of
`windowChain` (the case split depends on `n` only), namely `β · (windowIdx n)`, or
`germC a h (λ^n * (u + κ ·^k))`, or `ugermC a h (λ^{-n} * psi2 a Yinv β ·)`; all three are
continuous there by the lemmas of `chain_family_defs`
(`windowChain_analyticOnNhd_germC_fwd`, `windowChain_analyticOnNhd_ugermC_zpow_mul_psi2`,
`windowChain_analyticOnNhd_zpow_mul_psi2`, `windowChain_analyticOnNhd_psi2`), and the two
parameters are continuous too.  Assemble with `continuousOn_pi` (for the `ℤ → ℂ × ℂ` component)
and `ContinuousOn.prod`.  The unfolding lemmas `windowChain_fst_of_window`,
`windowChain_fst_of_fwd`, `windowChain_fst_of_bwd` (all in `chain_family_defs`) give the three
branches. -/
theorem windowChain_continuous {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {n₁ m₁ : ℕ}
    {u κ : ℂ} {k : ℕ} {ρ ρg ρY : ℝ} (hρ : 0 < ρ) {Yinv : ℂ → ℂ}
    {β : ℂ → Fin (n₁ + m₁ + 1) → ℂ × ℂ}
    (hgerm_an : AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρg))
    (hsmall : ∀ t, 0 < ‖t‖ → ‖t‖ < ρ →
      ‖((eqLam a : ℝ) : ℂ) ^ n₁ * (u + κ * t ^ k)‖ < ρg)
    (hβan : ∀ j : Fin (n₁ + m₁ + 1), AnalyticOnNhd ℂ (fun t => β t j)
      (Metric.ball (0 : ℂ) ρ \ {0}))
    (hYan : AnalyticOnNhd ℂ Yinv (Metric.ball (0 : ℂ) ρY))
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w)
    (hYim : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → (germC a h w).2 ∈ Metric.ball (0 : ℂ) ρY)
    (hβcurve : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ∃ w, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧ ugermC a h w = β t 0)
    (hρYg : ρY ≤ ρg) :
    ContinuousOn (fun t => windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β t)
      (Metric.ball (0 : ℂ) ρ \ {0}) := by
  have hlam : ((eqLam a : ℝ) : ℂ) ≠ 0 := win_eqLamC_ne_zero ha0 ha1
  -- The third component `ψ₂` is analytic, hence continuous.
  have hψ2cont : ContinuousOn (fun t => psi2 a Yinv β t)
      (Metric.ball (0 : ℂ) ρ \ {0}) :=
    (windowChain_analyticOnNhd_psi2 hYan (hβan 0) hY3 hYim hβcurve).continuousOn
  -- The first component: each projection is one of the three formulas.
  have hchain : ContinuousOn
      (fun t => (windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β t).1)
      (Metric.ball (0 : ℂ) ρ \ {0}) := by
    rw [continuousOn_pi]
    intro j
    by_cases hj : -((m₁ : ℤ)) ≤ j ∧ j ≤ ((n₁ : ℕ) : ℤ)
    · -- window part
      refine (hβan (windowIdx n₁ m₁ j hj)).continuousOn.congr ?_
      intro t _
      exact windowChain_fst_of_window t hj
    · by_cases hj2 : ((n₁ : ℕ) : ℤ) < j
      · -- forward tail
        refine (windowChain_analyticOnNhd_germC_fwd (n := j) ha0 ha1 hsmall hgerm_an
          (le_of_lt hj2)).continuousOn.congr ?_
        intro t _
        exact windowChain_fst_of_fwd t hj2
      · -- backward tail
        have hj3 : j < -((m₁ : ℤ)) := by omega
        refine (windowChain_analyticOnNhd_ugermC_zpow_mul_psi2 j ha0 ha1 hlam hYan
          (hβan 0) hY3 hYim hβcurve hρYg hgerm_an hj3).continuousOn.congr ?_
        intro t _
        exact windowChain_fst_of_bwd t hj3
  -- The second component `u + κ t^k` is a polynomial.
  have hb : ContinuousOn (fun t => u + κ * t ^ k) (Metric.ball (0 : ℂ) ρ \ {0}) := by
    fun_prop
  exact hchain.prodMk (hb.prodMk hψ2cont)

end Work.EQ
