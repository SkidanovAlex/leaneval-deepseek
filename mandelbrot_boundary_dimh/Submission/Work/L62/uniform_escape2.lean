import Mathlib

/-!
# `Work.L62.uniform_escape2` — uniform escape to the contracting ball

Shishikura, §6 (Lemma 6.2, uniformity step).  Let `Ω ⊆ ℂ` be open, `Λ, K` compact with `K ⊆ Ω`,
let `H : ℂ → ℂ → ℂ` be jointly continuous on `Λ ×ˢ Ω` and let every `H β`, `β ∈ Λ`, map `Ω`
into itself.  Suppose furthermore that on the ball `Metric.ball 0 r ⊆ Ω` every `H β` contracts
norms by a factor `μ < 1`, and that for every `(β, z) ∈ Λ × K` the orbit of `z` under `H β`
eventually enters `Metric.ball 0 r`.  Then the entry time is *uniform*: there is `J` such that
for all `β ∈ Λ`, all `n ≥ J` and all `z ∈ K` the orbit value `((H β)^[n]) z` lies in the
prescribed ball `Metric.ball 0 eps`.

The mathematical content is a compactness argument.  The escape time
`z ↦ min {n | ((H β)^[n]) z ∈ ball 0 r}` is finite on the *compact* set `Λ × K`, and it is
locally bounded: at every `(β₀, z₀)` the map `(β, z) ↦ ((H β)^[n₀]) z₀` is jointly continuous
and `ball 0 r` is open, so the escape time is `≤ n₀` on a whole neighbourhood of `(β₀, z₀)`.
Finitely many such neighbourhoods cover `Λ × K`.  Once inside `ball 0 r` the orbit is trapped
there and is contracted geometrically, which gives the uniform tail.
-/

namespace Work.L62

/-- The `n`-fold iterate of the "graph" self-map `q ↦ (q.1, H q.1 q.2)` of `ℂ × ℂ` is the graph
of the `n`-fold iterate of `H` in the second coordinate. -/
private lemma iterate_graph {H : ℂ → ℂ → ℂ} (p : ℂ × ℂ) (n : ℕ) :
    ((fun q : ℂ × ℂ => (q.1, H q.1 q.2))^[n]) p = (p.1, ((H p.1)^[n]) p.2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']

/-- **Joint continuity of the iterates.**  If `H` is jointly continuous on `Λ ×ˢ Ω` and each
`H β`, `β ∈ Λ`, maps `Ω` into itself, then `(β, z) ↦ ((H β)^[n]) z` is continuous on
`Λ ×ˢ Ω`, for every `n`. -/
private theorem iterate_continuousOn_aux {Ω Λ : Set ℂ} {H : ℂ → ℂ → ℂ}
    (hmap : ∀ β ∈ Λ, Set.MapsTo (H β) Ω Ω)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) (Λ ×ˢ Ω)) :
    ∀ n : ℕ, ContinuousOn (fun p : ℂ × ℂ => ((H p.1)^[n]) p.2) (Λ ×ˢ Ω) := by
  intro n
  have hF : ContinuousOn (fun q : ℂ × ℂ => (q.1, H q.1 q.2)) (Λ ×ˢ Ω) :=
    ContinuousOn.prodMk continuous_fst.continuousOn hcont
  have hmaps : Set.MapsTo (fun q : ℂ × ℂ => (q.1, H q.1 q.2)) (Λ ×ˢ Ω) (Λ ×ˢ Ω) := by
    intro q hq
    rw [Set.mem_prod] at hq ⊢
    exact ⟨hq.1, (hmap q.1 hq.1) hq.2⟩
  have h := (hF.iterate hmaps n).snd
  have hfun : (fun p : ℂ × ℂ => (((fun q : ℂ × ℂ => (q.1, H q.1 q.2))^[n]) p).2)
      = (fun p : ℂ × ℂ => ((H p.1)^[n]) p.2) := by
    funext p
    simp only [iterate_graph p n]
  rwa [hfun] at h

/-- **Iterates of a contraction on a ball.**  If `0 ≤ μ < 1` and `‖H β w‖ ≤ μ ‖w‖` for every
`β ∈ Λ` and every `w ∈ Metric.ball 0 r`, then all iterates stay in the ball and are contracted
geometrically: `‖((H β)^[m]) w‖ ≤ μ ^ m ‖w‖`. -/
private theorem iterate_contraction_bound {Λ : Set ℂ} {H : ℂ → ℂ → ℂ} {r μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    (hcontr : ∀ β ∈ Λ, ∀ w ∈ Metric.ball (0 : ℂ) r, ‖H β w‖ ≤ μ * ‖w‖) :
    ∀ β ∈ Λ, ∀ w ∈ Metric.ball (0 : ℂ) r, ∀ m : ℕ,
      ((H β)^[m]) w ∈ Metric.ball (0 : ℂ) r ∧ ‖((H β)^[m]) w‖ ≤ μ ^ m * ‖w‖ := by
  intro β hβ w hw m
  induction m with
  | zero =>
    refine ⟨by simpa using hw, ?_⟩
    simp
  | succ m ih =>
    obtain ⟨hmem, hnorm⟩ := ih
    rw [Function.iterate_succ_apply']
    have h1 : ‖H β (((H β)^[m]) w)‖ ≤ μ * ‖((H β)^[m]) w‖ := hcontr β hβ _ hmem
    have h3 : ‖((H β)^[m]) w‖ < r := by
      have h4 := Metric.mem_ball.mp hmem
      rwa [dist_zero_right] at h4
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]
      have h2 : μ * ‖((H β)^[m]) w‖ ≤ ‖((H β)^[m]) w‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (le_of_lt hμ1)
      linarith
    · calc ‖H β (((H β)^[m]) w)‖ ≤ μ * ‖((H β)^[m]) w‖ := h1
        _ ≤ μ * (μ ^ m * ‖w‖) := mul_le_mul_of_nonneg_left hnorm hμ0
        _ = μ ^ (m + 1) * ‖w‖ := by rw [pow_succ]; ring

theorem uniform_escape2 {Ω Λ K : Set ℂ} {H : ℂ → ℂ → ℂ} {r μ eps : ℝ}
    (hΩo : IsOpen Ω) (hΛc : IsCompact Λ) (hKc : IsCompact K) (hK : K ⊆ Ω)
    (hr : 0 < r) (hrΩ : Metric.ball 0 r ⊆ Ω) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    (heps : 0 < eps)
    (hmap : ∀ β ∈ Λ, Set.MapsTo (H β) Ω Ω)
    (hcontr : ∀ β ∈ Λ, ∀ w ∈ Metric.ball 0 r, ‖H β w‖ ≤ μ * ‖w‖)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) (Λ ×ˢ Ω))
    (hesc : ∀ β ∈ Λ, ∀ z ∈ K, ∃ n : ℕ, ((H β)^[n]) z ∈ Metric.ball 0 r) :
    ∃ J : ℕ, ∀ β ∈ Λ, ∀ n ≥ J, ∀ z ∈ K, ((H β)^[n]) z ∈ Metric.ball 0 eps := by
  classical
  have hcont_iter := iterate_continuousOn_aux hmap hcont
  -- ## Step 1: near every point of `Λ × K` the orbit enters `ball 0 r` within a bounded time.
  have hex : ∀ p : ↥(Λ ×ˢ K), ∃ n : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ q ∈ (Λ ×ˢ Ω), dist q (p : ℂ × ℂ) < δ →
        ((H q.1)^[n]) q.2 ∈ Metric.ball (0 : ℂ) r := by
    rintro ⟨⟨β, z⟩, hp⟩
    rw [Set.mem_prod] at hp
    obtain ⟨hβ, hz⟩ := hp
    obtain ⟨n, hn⟩ := hesc β hβ z hz
    have hbase : ((fun p : ℂ × ℂ => ((H p.1)^[n]) p.2) ((β, z) : ℂ × ℂ))
        ∈ Metric.ball (0 : ℂ) r := by simpa using hn
    have hball_open : IsOpen (Metric.ball (0 : ℂ) r) := Metric.isOpen_ball
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hball_open
      ((fun p : ℂ × ℂ => ((H p.1)^[n]) p.2) ((β, z) : ℂ × ℂ)) hbase
    have hmemΩ : ((β, z) : ℂ × ℂ) ∈ Λ ×ˢ Ω := by
      rw [Set.mem_prod]; exact ⟨hβ, hK hz⟩
    obtain ⟨δ, hδpos, hδ⟩ :=
      Metric.continuousWithinAt_iff.mp ((hcont_iter n).continuousWithinAt hmemΩ) ε hεpos
    exact ⟨n, δ, hδpos, fun q hq hdist => hεsub (by
      rw [Metric.mem_ball]
      exact hδ hq hdist)⟩
  choose nf df hdf using hex
  -- ## Step 2: finitely many of those neighbourhoods cover the compact set `Λ × K`.
  have hΛK : IsCompact (Λ ×ˢ K) := hΛc.prod hKc
  obtain ⟨t, ht⟩ := hΛK.elim_finite_subcover
    (fun p : ↥(Λ ×ˢ K) => Metric.ball (p : ℂ × ℂ) (df p))
    (fun _ => Metric.isOpen_ball)
    (by
      intro p hp
      exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, by
        simpa using (Metric.mem_ball_self (x := p) (hdf ⟨p, hp⟩).1)⟩)
  -- ## Step 3: once inside `ball 0 r`, the orbit decays geometrically with a uniform rate.
  obtain ⟨J0, hJ0⟩ : ∃ j : ℕ, μ ^ j * r < eps := by
    have htend : Filter.Tendsto (fun n : ℕ => μ ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hμ0 hμ1
    obtain ⟨j, hj⟩ := Metric.tendsto_atTop.mp htend (eps / r) (div_pos heps hr)
    refine ⟨j, ?_⟩
    have h1 : μ ^ j < eps / r := by
      have h2 := hj j le_rfl
      rwa [dist_zero_right, Real.norm_of_nonneg (pow_nonneg hμ0 j)] at h2
    exact (lt_div_iff₀ hr).mp h1
  refine ⟨t.sup nf + J0, ?_⟩
  intro β hβ n hn z hz
  have hq : ((β, z) : ℂ × ℂ) ∈ Λ ×ˢ K := by
    rw [Set.mem_prod]; exact ⟨hβ, hz⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht hq)
  obtain ⟨hit, hqi⟩ := Set.mem_iUnion.mp hi
  have hNi : nf i ≤ t.sup nf := Finset.le_sup hit
  have hle : nf i ≤ n := by omega
  have hJle : J0 ≤ n - nf i := by omega
  have hw0 : ((H β)^[nf i]) z ∈ Metric.ball (0 : ℂ) r :=
    (hdf i).2 ((β, z) : ℂ × ℂ) (by rw [Set.mem_prod]; exact ⟨hβ, hK hz⟩)
      (Metric.mem_ball.mp hqi)
  have hbnd := (iterate_contraction_bound hμ0 hμ1 hcontr β hβ (((H β)^[nf i]) z) hw0
    (n - nf i)).2
  have hw0r : ‖((H β)^[nf i]) z‖ < r := by
    have h4 := Metric.mem_ball.mp hw0
    rwa [dist_zero_right] at h4
  have hpow : μ ^ (n - nf i) ≤ μ ^ J0 := pow_le_pow_of_le_one hμ0 (le_of_lt hμ1) hJle
  have hdecomp : ((H β)^[n]) z = ((H β)^[n - nf i]) (((H β)^[nf i]) z) := by
    conv_lhs => rw [show n = (n - nf i) + nf i from by omega]
    rw [Function.iterate_add_apply]
  rw [Metric.mem_ball, dist_zero_right, hdecomp]
  calc ‖((H β)^[n - nf i]) (((H β)^[nf i]) z)‖
      ≤ μ ^ (n - nf i) * ‖((H β)^[nf i]) z‖ := hbnd
    _ ≤ μ ^ J0 * r := mul_le_mul hpow (le_of_lt hw0r) (norm_nonneg _) (pow_nonneg hμ0 J0)
    _ < eps := hJ0

end Work.L62
