import Mathlib
import Submission.Work.EQ.chain_family_defs
import Submission.Work.EQ.meromorphicAt_punctured_bounded
import Submission.Work.EQ.windowChain_meromorphicAt_fwd
import Submission.Work.EQ.windowChain_meromorphicAt_bwd
import Submission.Work.EQ.windowChain_meromorphicAt_psi2

namespace Work.EQ

/-- **Meromorphy of the parameters and the entries of the chain built from a window.**  `ψ₂` and
every entry `(E t).1 n` of `E = windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β` are meromorphic at
`0`.

Route (each case uses `Work.EQ.meromorphicAt_punctured_bounded`, which turns "analytic and bounded
on a punctured disc" into `MeromorphicAt`):
* `ψ₂`: analytic on the punctured disc (`windowChain_analyticOnNhd_psi2`), bounded by
  `ρY / λ^{m₁}` (`windowChain_psi2_witness` gives `λ^{m₁} ψ₂ t = w` with `‖w‖ < ρY`);
* window indices `-m₁ ≤ n ≤ n₁`: the entry is `(β · j).i` for a fixed `j`
  (`windowChain_fst_of_window`), so `hβm` applies after `MeromorphicAt.congr` (the two functions
  agree on the punctured disc, which is a punctured neighbourhood of `0` —
  `Work.EQ.ball_diff_zero_mem_nhdsWithin`);
* forward indices `n > n₁`: analytic on the punctured disc
  (`windowChain_analyticOnNhd_germC_fwd`) and bounded, because
  `‖λ^n (u+κt^k)‖ ≤ λ^{n-n₁} ‖λ^{n₁}(u+κt^k)‖ ≤ λ·ρg < ρg` for `n ≥ n₁+1`, so the values lie in
  the closed ball of radius `λ·ρg`, on which `germC a h` is bounded
  (`Work.EQ.exists_norm_bound_germC` with `R = λ·ρg`);
* backward indices `n < -m₁`: analytic on the punctured disc
  (`windowChain_analyticOnNhd_ugermC_zpow_mul_psi2`) and bounded by the same
  `exists_norm_bound_germC` with `R = λ·ρY`, since `‖λ^{-n}ψ₂ t‖ = λ^{-n-m₁}‖w‖ ≤ ‖w‖ < ρY`
  (`windowChain_psi2_witness`) and `‖ugermC a h z‖ = ‖germC a h z‖`. -/
theorem windowChain_meromorphicAt {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {n₁ m₁ : ℕ}
    {u κ : ℂ} {k : ℕ} {ρ ρg ρY : ℝ} (hρ : 0 < ρ) (hρg : 0 < ρg) (hρY : 0 < ρY) (hρYg : ρY ≤ ρg)
    {Yinv : ℂ → ℂ} {β : ℂ → Fin (n₁ + m₁ + 1) → ℂ × ℂ}
    (hgerm_an : AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρg))
    (hsmall : ∀ t, 0 < ‖t‖ → ‖t‖ < ρ →
      ‖((eqLam a : ℝ) : ℂ) ^ n₁ * (u + κ * t ^ k)‖ < ρg)
    (hβm : ∀ j : Fin (n₁ + m₁ + 1),
      MeromorphicAt (fun t => (β t j).1) 0 ∧ MeromorphicAt (fun t => (β t j).2) 0)
    (hβan : ∀ j : Fin (n₁ + m₁ + 1), AnalyticOnNhd ℂ (fun t => β t j)
      (Metric.ball (0 : ℂ) ρ \ {0}))
    (hYan : AnalyticOnNhd ℂ Yinv (Metric.ball (0 : ℂ) ρY))
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w)
    (hYim : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → (germC a h w).2 ∈ Metric.ball (0 : ℂ) ρY)
    (hβcurve : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ∃ w, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧ ugermC a h w = β t 0) :
    MeromorphicAt (fun t => psi2 a Yinv β t) 0 ∧
      (∀ n : ℤ, MeromorphicAt
          (fun t => ((windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β t).1 n).1) 0 ∧
        MeromorphicAt
          (fun t => ((windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β t).1 n).2) 0) := by
  -- `ψ₂` is meromorphic: analytic on the punctured disc and bounded there by `ρY / λ^{m₁}`.
  refine ⟨windowChain_meromorphicAt_psi2 ha0 ha1 hρ hρY hβan hYan hY3 hYim hβcurve,
    fun n => ?_⟩
  -- Case split on the index `n`: window, forward tail, backward tail.
  by_cases hwin : -((m₁ : ℤ)) ≤ n ∧ n ≤ ((n₁ : ℕ) : ℤ)
  · -- window indices: the entry is `β t (windowIdx n₁ m₁ n hwin)`, so `hβm` applies.
    refine ⟨?_, ?_⟩
    · refine (hβm (windowIdx n₁ m₁ n hwin)).1.congr ?_
      filter_upwards [ball_diff_zero_mem_nhdsWithin hρ] with t ht
      exact (congrArg Prod.fst
        (windowChain_fst_of_window (ψ₂ := psi2 a Yinv β) t hwin)).symm
    · refine (hβm (windowIdx n₁ m₁ n hwin)).2.congr ?_
      filter_upwards [ball_diff_zero_mem_nhdsWithin hρ] with t ht
      exact (congrArg Prod.snd
        (windowChain_fst_of_window (ψ₂ := psi2 a Yinv β) t hwin)).symm
  · by_cases hfwd : ((n₁ : ℕ) : ℤ) < n
    · -- forward tail: the entry is `germC a h (λ^n (u + κ t^k))`.
      have h := windowChain_meromorphicAt_fwd (m₁ := m₁) ha0 ha1 hρ hρg hgerm_an hsmall hfwd
      refine ⟨?_, ?_⟩
      · refine h.1.congr (Filter.Eventually.of_forall fun t => ?_)
        exact (congrArg Prod.fst
          (windowChain_fst_of_fwd (ψ₂ := psi2 a Yinv β) t hfwd)).symm
      · refine h.2.congr (Filter.Eventually.of_forall fun t => ?_)
        exact (congrArg Prod.snd
          (windowChain_fst_of_fwd (ψ₂ := psi2 a Yinv β) t hfwd)).symm
    · -- backward tail: the entry is `ugermC a h (λ^{-n} ψ₂ t)`.
      have hbwd : n < -((m₁ : ℤ)) := by omega
      have h := windowChain_meromorphicAt_bwd (u := u) (κ := κ) (k := k) ha0 ha1 hρ hρg hρY
        hρYg hgerm_an hβan hYan hY3 hYim hβcurve hbwd
      refine ⟨?_, ?_⟩
      · refine h.1.congr (Filter.Eventually.of_forall fun t => ?_)
        exact (congrArg Prod.fst
          (windowChain_fst_of_bwd (ψ₂ := psi2 a Yinv β) t hbwd)).symm
      · refine h.2.congr (Filter.Eventually.of_forall fun t => ?_)
        exact (congrArg Prod.snd
          (windowChain_fst_of_bwd (ψ₂ := psi2 a Yinv β) t hbwd)).symm

end Work.EQ
