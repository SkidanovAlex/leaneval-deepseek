import Mathlib
import Submission.Work.EQ.H0_fibre_defs
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.germC_facts

namespace Work.EQ

open Complex Metric Filter _root_.Topology

/-- **The forward branch word of a chain is eventually the principal one.**

Context. `chainWord a p : ℤ → Bool` (`Work.EQ.H0_fibre_defs`) is the branch word of a chain: at
index `n` it is `true` iff `p.1 n = invBranch a true (p.1 (n+1))`.  `IsChain a h p` says that
consecutive points are regular pairs, `ψ₁, ψ₂ ≠ 0`, that
`p.1 n = germC a h (λ^n ψ₁)` for all large `n` (`λ = (1-a)/(1+a) ∈ (0,1)`), and that
`p.1 n = ugermC a h (λ^(-n) ψ₂)` for all `n` very negative.

Claim: `chainWord a p n = true` for all large `n`.

Why: for `n` large, `p.1 n = germC a h (λ^n ψ₁)` and `p.1 (n+1) = germC a h (λ^(n+1) ψ₁)
= germC a h (λ * (λ^n ψ₁))`, and `Work.EQ.germC_facts` gives
`invBranch a true (germC a h (λ * u)) = germC a h u` for `u` in a ball around `0` (as well as
`RegPair a (germC a h u) (germC a h (λ*u))`).  Taking `u = λ^n ψ₁` (arbitrarily small for large
`n`, since `‖ψ₁‖ λ^n → 0`) gives `p.1 n = invBranch a true (p.1 (n+1))`, i.e.
`chainWord a p n = true`. -/
theorem chainWord_eventually_true_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {p : ChainData} (hp : IsChain a h p) :
    ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ n → chainWord a p n = true := by
  -- `germC_facts` supplies the ball around `0` on which the principal backward branch inverts
  -- the stable germ step: `invBranch a true (germC a h (λ * u)) = germC a h u`.
  obtain ⟨ρ, hρpos, _hAn, _hgerm0, hstep, _hinj, _hderiv⟩ := germC_facts ha0 ha1 hh
  -- the forward tail clause of `IsChain`, in `ℤ`-indexed form
  obtain ⟨N₁, hN₁⟩ := isChain_tail_fwd_z hp
  have hl0 : 0 < eqLam a := by rw [eqLam]; positivity
  have hl1 : eqLam a < 1 := by rw [eqLam, div_lt_one (by linarith)]; linarith
  have hlamne : (eqLam a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hl0)
  have hnorm_lt : ‖(eqLam a : ℂ)‖ < 1 := by
    rw [show ‖(eqLam a : ℂ)‖ = |eqLam a| by simp, abs_of_pos hl0]
    exact hl1
  -- `λ^k ψ₁ → 0`, so it lands in the ball of `germC_facts` for all large `k`
  have htend : Tendsto (fun k : ℕ => (eqLam a : ℂ) ^ k * p.2.1) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (eqLam a : ℂ) ^ k) atTop (𝓝 (0 : ℂ)) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm_lt
    simpa using h1.mul tendsto_const_nhds
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp htend ρ hρpos
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn1 : (N₁ : ℤ) ≤ n := le_trans (by exact_mod_cast Nat.le_max_left N₁ N₂) hn
  have hn2 : (N₂ : ℤ) ≤ n := le_trans (by exact_mod_cast Nat.le_max_right N₁ N₂) hn
  have hn0 : (0 : ℤ) ≤ n := le_trans (by exact_mod_cast Nat.zero_le (max N₁ N₂)) hn
  -- the germ parameter `λ^n ψ₁` is small
  have hsmall : ‖(eqLam a : ℂ) ^ n * p.2.1‖ < ρ := by
    have hk : N₂ ≤ n.toNat := by omega
    have h := hN₂ n.toNat hk
    rw [dist_eq_norm, sub_zero] at h
    have hpow : (eqLam a : ℂ) ^ n.toNat = (eqLam a : ℂ) ^ n := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hn0]
    rwa [hpow] at h
  have hu : (eqLam a : ℂ) ^ n * p.2.1 ∈ Metric.ball (0 : ℂ) ρ := by
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero]
  -- both chain points are germ points, at `u = λ^n ψ₁` and at `λu`
  have hpn : p.1 n = germC a h ((eqLam a : ℂ) ^ n * p.2.1) := hN₁ n hn1
  have hpn1 : p.1 (n + 1) = germC a h ((eqLam a : ℂ) ^ (n + 1) * p.2.1) :=
    hN₁ (n + 1) (by omega)
  have harg : (eqLam a : ℂ) ^ (n + 1) * p.2.1 =
      (eqLam a : ℂ) * ((eqLam a : ℂ) ^ n * p.2.1) := by
    rw [zpow_add_one₀ hlamne]; ring
  have hinv : invBranch a true (p.1 (n + 1)) = p.1 n := by
    rw [hpn1, harg, (hstep _ hu).2, hpn]
  have hEq : p.1 n = invBranch a true (p.1 (n + 1)) := hinv.symm
  simp [chainWord, brSign, hEq]

end Work.EQ
