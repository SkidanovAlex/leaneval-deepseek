import Mathlib
import Submission.Work.EQ.chain_family_defs
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.windowChain_regPair

namespace Work.EQ

/-- **The explicit window chain is a chain.**

With the definitions of `Work.EQ.windowChain` and `Work.EQ.psi2`
(`Submission/Work/EQ/chain_family_defs.lean`), the explicit bi-infinite chain built from a window
`β` (a backward `EqRelC`-chain of length `n₁ + m₁` ending at `germC a h (λ ^ n₁ * (u + κ t ^ k))`,
with its first entry on the small unstable germ curve `ugermC a h ·`) is an `IsChain`, for every
parameter `t` of the punctured disc: its window entries are the steps of `β`, its forward tail is
`germC` of `λ ^ j * (u + κ t ^ k)`, its backward tail is `ugermC` of `λ ^ (-j) * ψ₂ t`, and all
steps are regular pairs. -/
theorem windowChain_isChain {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) {n₁ m₁ : ℕ} {u : ℂ} (hu : u ≠ 0) {κ : ℂ} (hκ : κ ≠ 0)
    {k : ℕ} (hk : 0 < k) {ρ ρg : ℝ} (hρ : 0 < ρ) (hρg : 0 < ρg)
    (hgerm_an : AnalyticOnNhd ℂ (Work.EQ.germC a h) (Metric.ball (0 : ℂ) ρg))
    (hgerm_reg : ∀ v : ℂ, v ∈ Metric.ball (0 : ℂ) ρg →
      Work.EQ.RegPair a (Work.EQ.germC a h v)
        (Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) * v)))
    (hsmall : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ →
      ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ n₁ * (u + κ * t ^ k)‖ < ρg)
    (hψne : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ → u + κ * t ^ k ≠ 0)
    {ρY : ℝ} (hρY : 0 < ρY) (hρYg : ρY ≤ ρg) {φ Yinv : ℂ → ℂ}
    (hYan : AnalyticOnNhd ℂ Yinv (Metric.ball (0 : ℂ) ρY))
    (hY1 : ∀ y ∈ Metric.ball (0 : ℂ) ρY, (Work.EQ.germC a h (Yinv y)).2 = y)
    (hY2 : ∀ y ∈ Metric.ball (0 : ℂ) ρY, (Work.EQ.germC a h (Yinv y)).1 = φ y)
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((Work.EQ.germC a h w).2) = w)
    (hYim : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → (Work.EQ.germC a h w).2 ∈ Metric.ball (0 : ℂ) ρY)
    {β : ℂ → Fin (n₁ + m₁ + 1) → ℂ × ℂ}
    (hβan : ∀ j, AnalyticOnNhd ℂ (fun t => β t j) (Metric.ball (0 : ℂ) ρ \ {0}))
    (hβreg : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0}, ∀ j : Fin (n₁ + m₁),
      Work.EQ.RegPair a (β t (Fin.castSucc j)) (β t (Fin.succ j)))
    (hβend : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      β t (Fin.last (n₁ + m₁)) =
        Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n₁ * (u + κ * t ^ k)))
    (hβcurve : ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      ∃ w, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧ Work.EQ.ugermC a h w = β t 0) :
    ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
      Work.EQ.IsChain a h
        (Work.EQ.windowChain a h n₁ m₁ u κ k (Work.EQ.psi2 a Yinv β) β t) := by
  intro t ht
  have hlam : ((eqLam a : ℝ) : ℂ) ≠ 0 := win_eqLamC_ne_zero ha0 ha1
  have htnorm : ‖t‖ < ρ := by
    have h := ht.1
    rwa [Metric.mem_ball, dist_zero_right] at h
  have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- consecutive entries form regular pairs
    exact windowChain_regPair ha0 ha1 hρ hgerm_reg hsmall hβend hβreg hY3 hβcurve hρYg ht
  · -- `ψ₁ = u + κ t^k ≠ 0`
    rw [windowChain_snd_fst]
    exact hψne t htpos htnorm
  · -- `ψ₂ ≠ 0`
    rw [windowChain_snd_snd]
    exact windowChain_psi2_ne_zero hlam hY3 hβcurve ht
  · -- forward tail
    rw [Filter.eventually_atTop]
    refine ⟨n₁ + 1, fun n hn => ?_⟩
    have hlt : ((n₁ : ℕ) : ℤ) < (n : ℤ) := by
      have h : n₁ + 1 ≤ n := hn
      omega
    rw [windowChain_fst_of_fwd (t := t) (j := (n : ℤ)) hlt]
    simp [windowChain_snd_fst]
  · -- backward tail
    rw [Filter.eventually_atTop]
    refine ⟨m₁ + 1, fun n hn => ?_⟩
    have hlt : -(n : ℤ) < -((m₁ : ℕ) : ℤ) := by
      have h : m₁ + 1 ≤ n := hn
      omega
    rw [windowChain_fst_of_bwd (t := t) (j := -(n : ℤ)) hlt]
    simp [windowChain_snd_snd]

end Work.EQ
