import Mathlib
import Submission.Work.Normal.montel_locallyBounded
import Submission.Work.L61.Normal.tendsto_zero_of_normal
import Submission.Work.L62.contract_small_ball

namespace Work.L62

open Complex Set Metric Filter Topology
open scoped Topology

/-- **Escape to the attracting fixed point.**  Let `Ω ⊆ ℂ` be a bounded, preconnected open set
containing `0`, and let `H : ℂ → ℂ` be holomorphic on `Ω` with `H(Ω) ⊆ Ω`, `H 0 = 0` and
`‖deriv H 0‖ < 1`.  Then the iterates `H^[n]` tend to `0` uniformly on every compact subset of
`Ω`.

Proof.  `H` contracts a small ball `closedBall 0 ρ ⊆ Ω` into itself with ratio `θ < 1`
(`Work.L62.contract_small_ball`), so `H^[n] z → 0` for every `z` in that ball.  Since `Ω` is
bounded, the family of iterates is uniformly bounded, hence normal (Montel).  Any locally uniform
limit `g` of a subsequence of iterates is holomorphic on `Ω` and vanishes on the ball
`ball 0 ρ`, so `g ≡ 0` on `Ω` by the identity theorem.  The elementary principle
`Work.L61.Normal.tendsto_of_forall_subseq` then upgrades this to convergence of the whole
sequence. -/
theorem contract_escape {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩc : IsPreconnected Ω) (h0 : (0 : ℂ) ∈ Ω) {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H Ω) (hmap : Set.MapsTo H Ω Ω) (hfix : H 0 = 0)
    (hder : ‖deriv H 0‖ < 1) :
    ∀ δ : ℝ, 0 < δ → ∀ K : Set ℂ, K ⊆ Ω → IsCompact K →
      ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ K, (H^[n]) z ∈ Metric.ball 0 δ := by
  have hmap' : ∀ n : ℕ, MapsTo (H^[n]) Ω Ω := fun n => hmap.iterate n
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (H^[n]) Ω := fun n => hH.iterate hmap n
  -- a uniform bound for `Ω` and hence for all iterates
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ Ω, ‖z‖ ≤ M := by
    obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hΩb
    exact ⟨M, fun z hz => mem_closedBall_zero_iff.mp (hM hz)⟩
  -- the small ball on which `H` is a contraction
  obtain ⟨θ, hθ0, hθ1, ρ, hρpos, hsub, _hcontr, hiter⟩ :=
    contract_small_ball hΩo hH h0 hfix hder
  -- the family of iterates is normal on `Ω`
  have hMsub : Work.Normal.IsLocallyBoundedOn (Work.Normal.iterateFamily H) Ω := by
    intro K hKΩ _
    exact ⟨M, fun f hf z hz => by
      obtain ⟨n, rfl⟩ := hf
      exact hM ((H^[n]) z) (hmap' n (hKΩ hz))⟩
  have hnormal : Work.Normal.IsNormalFamily (Work.Normal.iterateFamily H) Ω :=
    Work.Normal.montel_locallyBounded hΩo (fun f hf => by
      obtain ⟨n, rfl⟩ := hf
      exact hdiff n) hMsub
  -- every subsequence of iterates has a sub-subsequence going to `0` locally uniformly
  have hstep : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      TendstoLocallyUniformlyOn (fun n => (H^[φ (ψ n)])) (fun _ : ℂ => 0) atTop Ω := by
    intro φ hφ
    obtain ⟨ψ, hψ, hlim | htop⟩ :=
      hnormal (fun n => H^[φ n]) (fun n => Set.mem_range.mpr ⟨φ n, rfl⟩)
    · -- a locally uniform limit `g` of a subsequence vanishes identically
      obtain ⟨g, hg⟩ := hlim
      have hgd : DifferentiableOn ℂ g Ω :=
        hg.differentiableOn (Eventually.of_forall fun n => hdiff (φ (ψ n))) hΩo
      have hgan : AnalyticOnNhd ℂ g Ω := hgd.analyticOnNhd hΩo
      have hball0 : ∀ z ∈ ball (0 : ℂ) ρ, g z = 0 := by
        intro z hz
        have hzcl : z ∈ closedBall (0 : ℂ) ρ := ball_subset_closedBall hz
        have hzΩ : z ∈ Ω := hsub hzcl
        have h1 : Tendsto (fun n => (H^[φ (ψ n)]) z) atTop (𝓝 (g z)) := hg.tendsto_at hzΩ
        have h2 : Tendsto (fun n => (H^[φ (ψ n)]) z) atTop (𝓝 0) := by
          refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
          have hidx : Tendsto (fun n => φ (ψ n)) atTop atTop :=
            (hφ.comp hψ).tendsto_atTop
          have hp : Tendsto (fun n => θ ^ (φ (ψ n))) atTop (𝓝 0) :=
            (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
              (by rw [Real.norm_eq_abs, abs_of_nonneg hθ0]; exact hθ1)).comp hidx
          have hup : Tendsto (fun n => θ ^ (φ (ψ n)) * ‖z‖) atTop (𝓝 0) := by
            simpa using hp.mul_const ‖z‖
          exact tendsto_of_tendsto_of_tendsto_of_le_of_le
            (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hup
            (fun n => norm_nonneg _) (fun n => hiter (φ (ψ n)) z hzcl)
        exact tendsto_nhds_unique h1 h2
      have hev : g =ᶠ[𝓝 (0 : ℂ)] 0 :=
        Filter.eventually_of_mem (ball_mem_nhds 0 hρpos) hball0
      have hg0 : EqOn g 0 Ω :=
        hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩc h0 hev
      exact ⟨ψ, hψ, hg.congr_right hg0⟩
    · -- the `∞` alternative is impossible because the iterates stay in the bounded set `Ω`
      exfalso
      obtain ⟨N, hN⟩ := htop (closedBall (0 : ℂ) ρ) hsub (isCompact_closedBall 0 ρ) (M + 1)
      have h1 : M + 1 ≤ ‖(H^[φ (ψ N)]) 0‖ := hN N le_rfl 0 (mem_closedBall_self hρpos.le)
      have h2 : ‖(H^[φ (ψ N)]) 0‖ ≤ M := hM _ (hmap' (φ (ψ N)) h0)
      linarith
  have hfin : TendstoLocallyUniformlyOn (fun n => (H^[n])) (fun _ : ℂ => 0) atTop Ω :=
    Work.L61.Normal.tendsto_of_forall_subseq hΩo hstep
  intro δ hδ K hKΩ hKc
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hΩo] at hfin
  have hK := hfin K hKΩ hKc
  rw [Metric.tendstoUniformlyOn_iff] at hK
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hK δ hδ)
  refine ⟨N, fun n hn z hz => ?_⟩
  have h := hN n hn z hz
  rw [dist_zero_left] at h
  rw [mem_ball, dist_comm, dist_zero_left]
  exact h

end Work.L62
