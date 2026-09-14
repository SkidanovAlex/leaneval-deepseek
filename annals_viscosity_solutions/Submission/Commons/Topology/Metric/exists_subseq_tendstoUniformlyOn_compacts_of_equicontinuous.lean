import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.CompletelyRegular

namespace Commons.Topology.Metric

open Filter Set
open _root_.Metric

/-- **Sequential Arzelà–Ascoli on a separable pseudo-metric space.**

Let `X` be a separable pseudo-metric space and `u : ℕ → X → ℝ` a sequence of functions which is
* locally bounded on compact sets, and
* uniformly equicontinuous (one modulus of continuity works for the whole family).

Then there is a strictly monotone `φ : ℕ → ℕ` and a function `U : X → ℝ` such that `u (φ k)`
converges to `U` uniformly on every compact subset of `X`.

The proof is the classical diagonal argument: extract along a countable dense subset, then
propagate the convergence along compact sets using equicontinuity and finite covers. -/
theorem exists_strictMono_tendstoUniformlyOn_compacts_of_equicontinuous_separable
    {X : Type*} [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X]
    {u : ℕ → X → ℝ}
    (hbdd : ∀ K : Set X, IsCompact K → ∃ C : ℝ, ∀ n, ∀ x ∈ K, |u n x| ≤ C)
    (heq : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n (x y : X),
      dist x y < δ → |u n x - u n y| < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ U : X → ℝ,
      ∀ K : Set X, IsCompact K → TendstoUniformlyOn (fun k x => u (φ k) x) U atTop K := by
  classical
  -- A countable dense subset of `X`.
  obtain ⟨D, hDcount, hDense⟩ := TopologicalSpace.exists_countable_dense X
  have hDcnt : Countable D := Set.countable_coe_iff.mpr hDcount
  -- A bound on each singleton.
  choose C hC using fun d : D => hbdd ({↑d} : Set X) isCompact_singleton
  -- The family, viewed in a product of compact sets, one factor per point of `D`.
  let Φ : ℕ → (d : D) → Metric.closedBall (0 : ℝ) (C d) := fun n d =>
    ⟨u n (d : X), by
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      exact hC d n (d : X) (Set.mem_singleton (d : X))⟩
  -- Extract a subsequence converging pointwise on `D`.
  obtain ⟨z, φ, hφmono, hΦtend⟩ := CompactSpace.tendsto_subseq Φ
  have hz : ∀ d : D,
      Tendsto (fun k => u (φ k) (d : X)) atTop
        (nhds ((z d : Metric.closedBall (0 : ℝ) (C d)) : ℝ)) := by
    intro d
    have h1 : Tendsto (fun k => (Φ ∘ φ) k d) atTop (nhds (z d)) :=
      (tendsto_pi_nhds.mp hΦtend) d
    have h2 := tendsto_subtype_rng.mp h1
    simpa [Φ, Function.comp_def] using h2
  -- Density in a convenient form.
  have hDense' : ∀ x : X, ∀ ε > 0, ∃ d : D, dist x (d : X) < ε := by
    intro x ε hε
    obtain ⟨y, hy⟩ := Metric.dense_iff.mp hDense x ε hε
    exact ⟨⟨y, hy.2⟩, by rw [dist_comm]; exact mem_ball.mp hy.1⟩
  -- Equicontinuity in terms of `dist`.
  have heq' : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n (x y : X),
      dist x y < δ → dist (u n x) (u n y) < ε := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := heq ε hε
    exact ⟨δ, hδ, fun n x y hxy => by rw [Real.dist_eq]; exact h n x y hxy⟩
  -- Uniform Cauchy on compact sets.
  have hCau : ∀ K : Set X, IsCompact K → ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N, ∀ y ∈ K,
      dist (u (φ k) y) (u (φ l) y) < ε := by
    intro K hK ε hε
    have hε4 : 0 < ε / 4 := by linarith
    obtain ⟨δ, hδpos, hδ⟩ := heq' (ε / 4) hε4
    obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x (_ : x ∈ K) => ball x (δ / 2))
      (fun x (_ : x ∈ K) => ball_mem_nhds x (by linarith))
    choose c hcd using fun x : X => hDense' x (δ / 2) (by linarith)
    -- the values at the finitely many nearby points of `D` converge
    have hev : ∀ᶠ k in atTop, ∀ x ∈ t,
        dist (((z (c x) : Metric.closedBall (0 : ℝ) (C (c x)))) : ℝ) (u (φ k) (c x : X))
          < ε / 4 := by
      rw [Finset.eventually_all]
      intro x _
      exact ((Metric.tendsto_nhds.mp (hz (c x))) (ε / 4) hε4).mono
        (fun k hk => by rwa [dist_comm] at hk)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine ⟨N, fun k hk l hl y hy => ?_⟩
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht hy)
    have hyx' : dist y (x : X) < δ / 2 := mem_ball.mp hyx
    have hdc : dist y ((c x : D) : X) < δ := by
      calc dist y ((c x : D) : X) ≤ dist y (x : X) + dist (x : X) ((c x : D) : X) :=
            dist_triangle _ _ _
        _ < δ / 2 + δ / 2 := add_lt_add hyx' (hcd (x : X))
        _ = δ := by ring
    have e1 : dist (u (φ k) y) (u (φ k) ((c x : D) : X)) < ε / 4 := hδ (φ k) y _ hdc
    have e3 : dist (u (φ l) ((c x : D) : X)) (u (φ l) y) < ε / 4 :=
      hδ (φ l) _ y (by rw [dist_comm]; exact hdc)
    have ha := hN k hk x hxt
    have hb := hN l hl x hxt
    have e2 : dist (u (φ k) ((c x : D) : X)) (u (φ l) ((c x : D) : X)) < ε / 2 := by
      calc dist (u (φ k) ((c x : D) : X)) (u (φ l) ((c x : D) : X))
          ≤ dist (u (φ k) ((c x : D) : X))
              (((z (c x) : Metric.closedBall (0 : ℝ) (C (c x)))) : ℝ)
            + dist (((z (c x) : Metric.closedBall (0 : ℝ) (C (c x)))) : ℝ)
              (u (φ l) ((c x : D) : X)) := dist_triangle _ _ _
        _ < ε / 4 + ε / 4 := add_lt_add (by rw [dist_comm]; exact ha) hb
        _ = ε / 2 := by ring
    calc dist (u (φ k) y) (u (φ l) y)
        ≤ dist (u (φ k) y) (u (φ k) ((c x : D) : X))
          + dist (u (φ k) ((c x : D) : X)) (u (φ l) y) := dist_triangle _ _ _
      _ ≤ dist (u (φ k) y) (u (φ k) ((c x : D) : X))
          + (dist (u (φ k) ((c x : D) : X)) (u (φ l) ((c x : D) : X))
            + dist (u (φ l) ((c x : D) : X)) (u (φ l) y)) := by
            gcongr; exact dist_triangle _ _ _
      _ < ε / 4 + (ε / 2 + ε / 4) := add_lt_add e1 (add_lt_add e2 e3)
      _ = ε := by ring
  -- Pointwise Cauchy everywhere, and the limit function.
  have hcauchy : ∀ x : X, CauchySeq (fun k => u (φ k) x) := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hCau {x} isCompact_singleton ε hε
    exact ⟨N, fun m hm n hn => hN m hm n hn x (Set.mem_singleton x)⟩
  let U : X → ℝ := fun x => Classical.choose (cauchySeq_tendsto_of_complete (hcauchy x))
  have hU : ∀ x : X, Tendsto (fun k => u (φ k) x) atTop (nhds (U x)) := fun x =>
    Classical.choose_spec (cauchySeq_tendsto_of_complete (hcauchy x))
  refine ⟨φ, hφmono, U, fun K hK => ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hCau K hK (ε / 2) (by linarith)
  refine eventually_atTop.mpr ⟨N, fun k hk y hy => ?_⟩
  have htend : Tendsto (fun l => dist (u (φ l) y) (u (φ k) y)) atTop
      (nhds (dist (U y) (u (φ k) y))) := (hU y).dist tendsto_const_nhds
  have hle : dist (U y) (u (φ k) y) ≤ ε / 2 := by
    refine le_of_tendsto htend ?_
    exact eventually_atTop.mpr ⟨N, fun l hl => le_of_lt (hN l hl k hk y hy)⟩
  linarith

theorem exists_subseq_tendstoUniformlyOn_compacts_of_equicontinuous {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {N : ℕ}
    {u : ℕ → EuclideanSpace E (Fin N) → ℝ}
    (hbdd : ∀ K : Set (EuclideanSpace E (Fin N)), IsCompact K →
      ∃ C : ℝ, ∀ n, ∀ x ∈ K, |u n x| ≤ C)
    (heq : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n (x y : EuclideanSpace E (Fin N)),
      dist x y < δ → |u n x - u n y| < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ U : EuclideanSpace E (Fin N) → ℝ,
      ∀ K : Set (EuclideanSpace E (Fin N)), IsCompact K →
        TendstoUniformlyOn (fun k x => u (φ k) x) U atTop K :=
  exists_strictMono_tendstoUniformlyOn_compacts_of_equicontinuous_separable hbdd heq

end Commons.Topology.Metric