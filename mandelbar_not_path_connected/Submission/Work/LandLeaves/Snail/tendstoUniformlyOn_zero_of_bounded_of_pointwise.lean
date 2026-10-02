import Mathlib
import Submission.Work.Normal.exists_subseq_tendstoUniformlyOn_of_locallyBounded

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Topology Metric

namespace Work.LandLeaves.Snail

/-- **Vitali/Osgood convergence theorem** for a uniformly bounded family of holomorphic functions on
a ball (the normal-family convergence theorem): if `g n` is holomorphic and uniformly bounded on
`Metric.ball 0 R`, and `g n (x j) → 0` for a sequence of nonzero points `x j → 0` accumulating at the
interior point `0`, then `g n → 0` uniformly on every strictly smaller ball.

Route: `Work.Normal.montel_locallyBounded` (Montel: locally bounded ⟹ normal), extract a locally
uniformly convergent subsequence, its limit vanishes at every `x j` (the convergence is pointwise
there), hence identically on the ball by the identity theorem; a standard contradiction argument
(`‖g n‖` on `closedBall 0 R'` with the Cauchy estimates, or the compactness of the normal family)
finishes.  Equivalent formulations exist already in the workspace: `Work.Normal.exists_subseq_tendstoLocallyUniformlyOn_of_exhaustion`. -/
theorem tendstoUniformlyOn_zero_of_bounded_of_pointwise {g : ℕ → ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hd : ∀ n, DifferentiableOn ℂ (g n) (Metric.ball 0 R))
    (hb : ∃ M : ℝ, ∀ n z, z ∈ Metric.ball 0 R → ‖g n z‖ ≤ M)
    {x : ℕ → ℂ} (hx : Filter.Tendsto x Filter.atTop (nhds 0)) (hxne : ∀ n, x n ≠ 0)
    (hconv : ∀ j : ℕ, Filter.Tendsto (fun n : ℕ => g n (x j)) Filter.atTop (nhds 0))
    {R' : ℝ} (hR' : 0 < R') (hR'R : R' < R) :
    TendstoUniformlyOn g (fun _ : ℂ => (0 : ℂ)) Filter.atTop (Metric.ball 0 R') := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hc
  rw [Filter.not_eventually] at hc
  have hcP : ∃ᶠ n in Filter.atTop,
      ∃ z, z ∈ Metric.ball 0 R' ∧ ε ≤ dist (0 : ℂ) (g n z) := by
    refine hc.mono fun n hn => ?_
    by_contra hcon
    exact hn fun z hz => lt_of_not_ge fun hge => hcon ⟨z, hz, hge⟩
  rw [Filter.frequently_atTop] at hcP
  obtain ⟨m, hm_mono, hm⟩ := Nat.exists_strictMono_subsequence
    (P := fun n => ∃ z, z ∈ Metric.ball 0 R' ∧ ε ≤ dist (0 : ℂ) (g n z)) fun N => by
      obtain ⟨b, hNb, hbP⟩ := hcP (N + 1)
      exact ⟨b, Nat.lt_of_succ_le hNb, hbP⟩
  -- pick an intermediate radius `R''` with `R' < R'' < R`
  obtain ⟨R'', hR'R'', hR''R⟩ := exists_between hR'R
  have hR''pos : 0 < R'' := lt_trans hR' hR'R''
  have hloc : Work.Normal.IsLocallyBoundedOn (Set.range fun k => g (m k)) (Metric.ball 0 R) := by
    obtain ⟨M, hM⟩ := hb
    exact fun K hKU _hK => ⟨M, fun f hf z hz => by
      obtain ⟨k, rfl⟩ := hf
      exact hM (m k) z (hKU hz)⟩
  obtain ⟨σ, hσ, h, hunif⟩ :=
    Work.Normal.exists_subseq_tendstoUniformlyOn_of_locallyBounded Metric.isOpen_ball
      (isCompact_closedBall 0 R'') (Metric.closedBall_subset_ball hR''R)
      (fun k => g (m k)) (fun k => hd (m k)) hloc
  -- the limit is holomorphic on the smaller ball
  have hderiv : DifferentiableOn ℂ h (Metric.ball 0 R'') := by
    have hlu : TendstoLocallyUniformlyOn (fun k => g (m (σ k))) h Filter.atTop
        (Metric.ball 0 R'') :=
      (hunif.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn
    refine hlu.differentiableOn (Filter.Eventually.of_forall fun k => ?_) Metric.isOpen_ball
    exact (hd (m (σ k))).mono (Metric.ball_subset_ball hR''R.le)
  -- the limit vanishes identically, by the identity theorem
  have hzero : Set.EqOn h (0 : ℂ → ℂ) (Metric.ball 0 R'') := by
    refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure
      (hderiv.analyticOnNhd Metric.isOpen_ball) ?_ (Metric.mem_ball_self hR''pos) ?_
    · exact (convex_ball (0 : ℂ) R'').isPreconnected
    · rw [Metric.mem_closure_iff]
      intro δ hδ
      have hev1 : ∀ᶠ j in Filter.atTop, x j ∈ Metric.ball 0 R'' :=
        hx.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR''pos))
      have hev2 : ∀ᶠ j in Filter.atTop, dist (0 : ℂ) (x j) < δ := by
        filter_upwards [hx.eventually
          (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))] with j hj
        exact Metric.mem_ball'.mp hj
      have hev := hev1.and hev2
      obtain ⟨j, hj1, hj2⟩ := hev.exists
      refine ⟨x j, ⟨?_, hxne j⟩, hj2⟩
      have hxj : x j ∈ Metric.closedBall (0 : ℂ) R'' := Metric.ball_subset_closedBall hj1
      have hpt : Filter.Tendsto (fun k => g (m (σ k)) (x j)) Filter.atTop (nhds (h (x j))) :=
        hunif.tendsto_at hxj
      have hz : Filter.Tendsto (fun k => g (m (σ k)) (x j)) Filter.atTop (nhds 0) :=
        (hconv j).comp ((hm_mono.comp hσ).tendsto_atTop)
      exact tendsto_nhds_unique hpt hz
  -- contradiction: uniform convergence on `closedBall 0 R'`
  have hcl : Metric.closedBall (0 : ℂ) R' ⊆ Metric.ball 0 R'' :=
    Metric.closedBall_subset_ball hR'R''
  have hclcb : Metric.closedBall (0 : ℂ) R' ⊆ Metric.closedBall 0 R'' :=
    Metric.closedBall_subset_closedBall hR'R''.le
  have hunif' : TendstoUniformlyOn (fun k => g (m (σ k))) h Filter.atTop
      (Metric.closedBall 0 R') := hunif.mono hclcb
  rw [Metric.tendstoUniformlyOn_iff] at hunif'
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hunif' ε hε)
  obtain ⟨z, hz1, hz2⟩ := hm (σ K)
  have hzcl : z ∈ Metric.closedBall (0 : ℂ) R' := Metric.ball_subset_closedBall hz1
  have hsmall := hK K le_rfl z hzcl
  have hz0 : h z = 0 := by
    have := hzero (hcl hzcl)
    simpa using this
  rw [hz0] at hsmall
  exact absurd hsmall (not_lt.mpr hz2)

end Work.LandLeaves.Snail
