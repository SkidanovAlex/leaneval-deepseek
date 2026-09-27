import Mathlib
import Submission.Work.EQ.chain_family_defs
import Submission.Work.EQ.meromorphicAt_punctured_bounded
import Submission.Work.EQ.windowChain_continuous
import Submission.Work.EQ.windowChain_regPair
import Submission.Work.EQ.windowChain_meromorphicAt

namespace Work.EQ

open Complex Metric Filter
open scoped Topology

/-- **A family of windows determines a family of chains.**

`β t : Fin (n₁+m₁+1) → ℂ × ℂ` is a family of `EqRelC`-backward-chains of length `n₁ + m₁` ending
at the stable leaf `germC a h (λ^{n₁} (u + κ t^k))` (`hβend`, `hβreg`), analytic in `t` on a
punctured disc (`hβan`) and meromorphic at `0` in each coordinate (`hβm`), with its first entry on
the small unstable germ curve (`hβcurve`).  Then the window extends to a bi-infinite chain

`E t := (fun j => if -m₁ ≤ j ≤ n₁ then β t (j+m₁) else if n₁ < j then germC (λ^j (u+κt^k))
        else ugermC (λ^{-j} ψ₂ t),  u + κ t^k,  ψ₂ t)`

with `ψ₂ t := Yinv ((β t 0).2) / λ^{m₁}` (`Yinv` the analytic local inverse of the `y`-coordinate
of `germC`, a parameter with its properties `hY1`–`hY3`).

`hgerm_an` is the analyticity of `germC` on `ball 0 ρg` (used for the continuity of the tail
entries), `hgerm_reg` its germ-step regularity, `hYim` says the `y`-coordinate maps `ball 0 ρY`
into itself (so that `Yinv` can be applied to `(β t 0).2`), `hsmall` puts the forward junction
parameter `λ^{n₁}(u+κt^k)` inside `ρg` and `hρYg : ρY ≤ ρg` puts the backward witness there.
`hβcurve` keeps the witness nonzero, so `ψ₂ t ≠ 0`; `hψne` (non-vanishing of `u + κ t ^ k`) is
needed because `IsChain` requires `ψ₁ ≠ 0`.

Note the conclusion only asserts the *existence* of `E` with the listed properties (it does not
repeat the displayed case formula); the forward/backward tails are the `IsChain` clauses and the
window is pinned by the last clause. -/
theorem chain_family_of_window {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) {n₁ m₁ : ℕ}
    {u : ℂ} (hu : u ≠ 0) {κ : ℂ} (hκ : κ ≠ 0) {k : ℕ} (hk : 0 < k) {ρ : ℝ} (hρ : 0 < ρ)
    {ρg : ℝ} (hρg : 0 < ρg)
    (hgerm_an : AnalyticOnNhd ℂ (Work.EQ.germC a h) (Metric.ball (0:ℂ) ρg))
    (hgerm_reg : ∀ v : ℂ, v ∈ Metric.ball (0:ℂ) ρg →
      Work.EQ.RegPair a (Work.EQ.germC a h v)
        (Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) * v)))
    (hsmall : ∀ t, 0 < ‖t‖ → ‖t‖ < ρ →
      ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ n₁ * (u + κ * t ^ k)‖ < ρg)
    (hψne : ∀ t, 0 < ‖t‖ → ‖t‖ < ρ → u + κ * t ^ k ≠ 0)
    {ρY : ℝ} (hρY : 0 < ρY) (hρYg : ρY ≤ ρg) {φ Yinv : ℂ → ℂ}
    (hYan : AnalyticOnNhd ℂ Yinv (Metric.ball (0:ℂ) ρY))
    (hY1 : ∀ y ∈ Metric.ball (0:ℂ) ρY, (Work.EQ.germC a h (Yinv y)).2 = y)
    (hY2 : ∀ y ∈ Metric.ball (0:ℂ) ρY, (Work.EQ.germC a h (Yinv y)).1 = φ y)
    (hY3 : ∀ w, w ∈ Metric.ball (0:ℂ) ρY → Yinv ((Work.EQ.germC a h w).2) = w)
    (hYim : ∀ w, w ∈ Metric.ball (0:ℂ) ρY → (Work.EQ.germC a h w).2 ∈ Metric.ball (0:ℂ) ρY)
    {β : ℂ → Fin (n₁ + m₁ + 1) → ℂ × ℂ}
    (hβm : ∀ j, MeromorphicAt (fun t => (β t j).1) 0 ∧ MeromorphicAt (fun t => (β t j).2) 0)
    (hβan : ∀ j, AnalyticOnNhd ℂ (fun t => β t j) (Metric.ball (0:ℂ) ρ \ {0}))
    (hβend : ∀ t ∈ Metric.ball (0:ℂ) ρ \ {0},
      β t (Fin.last (n₁ + m₁)) =
        Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n₁ * (u + κ * t ^ k)))
    (hβreg : ∀ t ∈ Metric.ball (0:ℂ) ρ \ {0}, ∀ j : Fin (n₁ + m₁),
      Work.EQ.RegPair a (β t (Fin.castSucc j)) (β t (Fin.succ j)))
    (hβcurve : ∀ t ∈ Metric.ball (0:ℂ) ρ \ {0},
      ∃ w, w ∈ Metric.ball (0:ℂ) ρY ∧ w ≠ 0 ∧ Work.EQ.ugermC a h w = β t 0) :
    ∃ (ψ₂ : ℂ → ℂ) (E : ℂ → Work.EQ.ChainData),
      (∀ t ∈ Metric.ball (0:ℂ) ρ \ {0}, Work.EQ.IsChain a h (E t)) ∧
      (∀ t ∈ Metric.ball (0:ℂ) ρ \ {0},
        (E t).2.1 = u + κ * t ^ k ∧ (E t).2.2 = ψ₂ t ∧
        Work.EQ.ugermC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ m₁ * ψ₂ t) = β t 0 ∧
        ∀ j : Fin (n₁ + m₁ + 1), (E t).1 (((j:ℕ):ℤ) - (m₁:ℤ)) = β t j) ∧
      ContinuousOn E (Metric.ball (0:ℂ) ρ \ {0}) ∧
      MeromorphicAt (fun t => ψ₂ t) 0 ∧
      (∀ n : ℤ, MeromorphicAt (fun t => ((E t).1 n).1) 0 ∧
        MeromorphicAt (fun t => ((E t).1 n).2) 0) := by
  have hlam : ((eqLam a : ℝ) : ℂ) ≠ 0 := win_eqLamC_ne_zero ha0 ha1
  refine ⟨fun t => psi2 a Yinv β t,
    fun t => windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β t, ?_, ?_, ?_, ?_⟩
  · -- `IsChain` for every `t` in the punctured disc
    intro t ht
    show IsChain a h (windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β t)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- consecutive entries form regular pairs
      exact windowChain_regPair ha0 ha1 hρ hgerm_reg hsmall hβend hβreg hY3 hβcurve hρYg ht
    · -- `ψ₁ = u + κ t^k ≠ 0`
      rw [windowChain_snd_fst]
      exact hψne t (norm_pos_iff.mpr ht.2) (by
        have h := ht.1
        rwa [Metric.mem_ball, dist_zero_right] at h)
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
  · -- the window data
    intro t ht
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β t).2.1 = u + κ * t ^ k
      exact windowChain_snd_fst t
    · show (windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β t).2.2 = psi2 a Yinv β t
      exact windowChain_snd_snd t
    · -- the first entry is the unstable germ at the witness
      show ugermC a h (((eqLam a : ℝ) : ℂ) ^ m₁ * psi2 a Yinv β t) = β t 0
      obtain ⟨w, hw, hwne, hmul, hwcurve, -⟩ := windowChain_psi2_witness hlam hY3 hβcurve ht
      rw [hmul, hwcurve]
    · -- the window is pinned
      intro j
      show (windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β t).1
        (((j : ℕ) : ℤ) - (m₁ : ℤ)) = β t j
      rw [windowChain_fst_of_window (t := t) (j := ((j : ℕ) : ℤ) - (m₁ : ℤ))
        (by have h := j.isLt; omega)]
      exact congrArg (β t) (windowIdx_sub_m₁ n₁ m₁ j)
  · -- continuity
    exact windowChain_continuous ha0 ha1 hρ hgerm_an hsmall hβan hYan hY3 hYim hβcurve hρYg
  · -- meromorphy of the parameter and of every entry
    exact windowChain_meromorphicAt ha0 ha1 hρ hρg hρY hρYg hgerm_an hsmall hβm hβan hYan hY3
      hYim hβcurve

end Work.EQ
