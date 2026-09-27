import Mathlib
import Submission.Work.EQ.chain_family_defs
import Submission.Work.EQ.meromorphicAt_punctured_bounded

namespace Work.EQ

/-- The backward parameter `ψ₂ = psi2 a Yinv β` of the chain built from a window is meromorphic
at `0`: it is analytic on the punctured disc and bounded there by `ρY / λ^{m₁}`. -/
theorem windowChain_meromorphicAt_psi2 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {n₁ m₁ : ℕ} {ρ ρY : ℝ} (hρ : 0 < ρ) (hρY : 0 < ρY) {Yinv : ℂ → ℂ}
    {β : ℂ → Fin (n₁ + m₁ + 1) → ℂ × ℂ}
    (hβan : ∀ j : Fin (n₁ + m₁ + 1), AnalyticOnNhd ℂ (fun t => β t j)
      (Metric.ball (0 : ℂ) ρ \ {0}))
    (hYan : AnalyticOnNhd ℂ Yinv (Metric.ball (0 : ℂ) ρY))
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w)
    (hYim : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → (germC a h w).2 ∈ Metric.ball (0 : ℂ) ρY)
    (hβcurve : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ∃ w, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧ ugermC a h w = β t 0) :
    MeromorphicAt (fun t => psi2 a Yinv β t) 0 := by
  have hlam : ((eqLam a : ℝ) : ℂ) ≠ 0 := win_eqLamC_ne_zero ha0 ha1
  refine meromorphicAt_punctured_bounded (f := fun t => psi2 a Yinv β t) (r := ρ)
    (C := ρY / eqLam a ^ m₁) hρ
    (windowChain_analyticOnNhd_psi2 hYan (hβan 0) hY3 hYim hβcurve) ?_
  intro t ht
  obtain ⟨w, hw, -, hmul, -, -⟩ := windowChain_psi2_witness hlam hY3 hβcurve ht
  have hwlt : ‖w‖ < ρY := by simpa [Metric.mem_ball, dist_zero_right] using hw
  have hψ : psi2 a Yinv β t = w / ((eqLam a : ℝ) : ℂ) ^ m₁ := by
    rw [eq_div_iff (pow_ne_zero _ hlam), mul_comm]
    exact hmul
  rw [hψ, norm_div, norm_pow, win_norm_eqLamC ha0 ha1]
  exact le_of_lt ((div_lt_div_iff_of_pos_right (pow_pos (win_eqLam_pos ha0 ha1) m₁)).mpr hwlt)

end Work.EQ
