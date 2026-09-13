import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Filter Set
open _root_.Metric
open scoped Topology

namespace Commons.Topology.Metric

/-- **Arzelà–Ascoli with a graded (threshold) equicontinuity hypothesis.**

Let `K ⊆ ℝ⁴` be compact and `u : ℕ → ℝ⁴ → ℝ` a sequence of functions which is
* uniformly bounded on `K`, and
* *eventually* equicontinuous in the following graded sense: for every `j`
  there are `Kj` and `h > 0` such that for all `k ≥ Kj` the function `u k` has
  oscillation at most `1/(j+1)` on `h`-balls contained in `K`.

Then some strictly increasing subsequence of `u` converges uniformly on `K`.

The proof is the classical diagonal argument: extract along a countable dense
subset of `K` (which exists because `K` is a compact pseudo-metric space), then
propagate the pointwise convergence to uniform convergence on `K` using a finite
`h`-net and the graded equicontinuity. -/
theorem arzelaAscoli_threshold {K : Set (EuclideanSpace ℝ (Fin 4))} (hK : IsCompact K) {u : ℕ → EuclideanSpace ℝ (Fin 4) → ℝ} (hbdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ k, ∀ x ∈ K, |u k x| ≤ M) (hthr : ∀ j : ℕ, ∃ Kj : ℕ, ∃ h : ℝ, 0 < h ∧ ∀ k ≥ Kj, ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ h → |u k x - u k y| ≤ 1 / (j + 1)) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : EuclideanSpace ℝ (Fin 4) → ℝ, TendstoUniformlyOn (fun k => u (φ k)) g atTop K := by
  classical
  obtain ⟨M, hM0, hM⟩ := hbdd
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  -- Countable dense subset of `K`, transported to the ambient space.
  obtain ⟨D', hD'count, hD'dense⟩ := TopologicalSpace.exists_countable_dense K
  let D : Set (EuclideanSpace ℝ (Fin 4)) :=
    (fun k : K => (k : EuclideanSpace ℝ (Fin 4))) '' D'
  have hDsub : D ⊆ K := by rintro d ⟨k, -, rfl⟩; exact k.2
  have hDcount : D.Countable := hD'count.image _
  haveI : Countable D := Set.countable_coe_iff.mpr hDcount
  have hDense : ∀ x ∈ K, ∀ ε > 0, ∃ d ∈ D, dist x d < ε := by
    intro x hx ε hε
    obtain ⟨y, hyball, hyD'⟩ := Metric.dense_iff.mp hD'dense ⟨x, hx⟩ ε hε
    refine ⟨(y : EuclideanSpace ℝ (Fin 4)), ⟨y, hyD', rfl⟩, ?_⟩
    rw [mem_ball] at hyball
    rw [Subtype.dist_eq] at hyball
    simpa [dist_comm] using hyball
  -- Diagonal extraction of a subsequence converging pointwise on `D`.
  let Φ : ℕ → (d : D) → Metric.closedBall (0 : ℝ) M := fun n d =>
    ⟨u n (d : EuclideanSpace ℝ (Fin 4)), by
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      exact hM n (d : EuclideanSpace ℝ (Fin 4)) (hDsub d.2)⟩
  obtain ⟨z, φ, hφmono, hΦtend⟩ := CompactSpace.tendsto_subseq Φ
  have hz : ∀ d : D, Tendsto (fun k => u (φ k) (d : EuclideanSpace ℝ (Fin 4))) atTop
      (nhds ((z d : Metric.closedBall (0 : ℝ) M) : ℝ)) := by
    intro d
    have h1 : Tendsto (fun k => (Φ ∘ φ) k d) atTop (nhds (z d)) :=
      (tendsto_pi_nhds.mp hΦtend) d
    have h2 := tendsto_subtype_rng.mp h1
    simpa [Φ, Function.comp_def] using h2
  -- Uniform Cauchy on `K`.
  have hCau : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N, ∀ y ∈ K,
      dist (u (φ k) y) (u (φ l) y) < ε := by
    intro ε hε
    obtain ⟨j, hjlt⟩ := exists_nat_one_div_lt (K := ℝ) (show (0 : ℝ) < ε / 4 by linarith)
    obtain ⟨Kj, h, hhpos, hthrj⟩ := hthr j
    have hh2 : 0 < h / 2 := by linarith
    -- A finite net of `K` by `h/2`-balls.
    obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x (_ : x ∈ K) => ball x (h / 2))
      (fun x (_ : x ∈ K) => ball_mem_nhds x hh2)
    -- A nearby point of `D` for every centre.
    have hnet : ∀ x : t, ∃ d ∈ D, dist (((x : K) : EuclideanSpace ℝ (Fin 4))) d < h / 2 :=
      fun x => hDense ((x : K) : EuclideanSpace ℝ (Fin 4)) x.val.2 (h / 2) hh2
    choose c hcD hcd using hnet
    -- At the finitely many nearby points the sequence converges, hence is Cauchy.
    have hev : ∀ᶠ k in atTop, ∀ x : t,
        dist (u (φ k) (c x))
          (((z ⟨c x, hcD x⟩ : Metric.closedBall (0 : ℝ) M)) : ℝ) < ε / 4 := by
      rw [Filter.eventually_all]
      intro x
      exact (Metric.tendsto_nhds.mp (hz ⟨c x, hcD x⟩)) (ε / 4) (by linarith)
    obtain ⟨N1, hN1⟩ := eventually_atTop.mp hev
    refine ⟨max N1 Kj, fun k hk l hl y hy => ?_⟩
    have hkKj : Kj ≤ φ k := le_trans (le_trans (le_max_right N1 Kj) hk) (hφmono.id_le k)
    have hlKj : Kj ≤ φ l := le_trans (le_trans (le_max_right N1 Kj) hl) (hφmono.id_le l)
    have hk1 : N1 ≤ k := le_trans (le_max_left N1 Kj) hk
    have hl1 : N1 ≤ l := le_trans (le_max_left N1 Kj) hl
    -- Locate `y` in a net ball, and pick the corresponding point of `D`.
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht hy)
    have hyx' : dist y ((x : K) : EuclideanSpace ℝ (Fin 4)) < h / 2 := mem_ball.mp hyx
    have hyc : dist y (c ⟨x, hxt⟩) ≤ h :=
      le_of_lt (by
        calc dist y (c ⟨x, hxt⟩)
            ≤ dist y ((x : K) : EuclideanSpace ℝ (Fin 4))
              + dist ((x : K) : EuclideanSpace ℝ (Fin 4)) (c ⟨x, hxt⟩) := dist_triangle _ _ _
          _ < h / 2 + h / 2 := add_lt_add hyx' (hcd ⟨x, hxt⟩)
          _ = h := by ring)
    have hcK : c ⟨x, hxt⟩ ∈ K := hDsub (hcD ⟨x, hxt⟩)
    have e1 : dist (u (φ k) y) (u (φ k) (c ⟨x, hxt⟩)) < ε / 4 :=
      lt_of_le_of_lt (by
        rw [Real.dist_eq]
        exact hthrj (φ k) hkKj y hy (c ⟨x, hxt⟩) hcK hyc) hjlt
    have e3 : dist (u (φ l) (c ⟨x, hxt⟩)) (u (φ l) y) < ε / 4 :=
      lt_of_le_of_lt (by
        rw [Real.dist_eq]
        exact hthrj (φ l) hlKj (c ⟨x, hxt⟩) hcK y hy (by rw [dist_comm]; exact hyc)) hjlt
    have e2 : dist (u (φ k) (c ⟨x, hxt⟩)) (u (φ l) (c ⟨x, hxt⟩)) < ε / 2 := by
      have hk' := hN1 k hk1 ⟨x, hxt⟩
      have hl' := hN1 l hl1 ⟨x, hxt⟩
      calc dist (u (φ k) (c ⟨x, hxt⟩)) (u (φ l) (c ⟨x, hxt⟩))
          ≤ dist (u (φ k) (c ⟨x, hxt⟩))
              (((z ⟨c ⟨x, hxt⟩, hcD ⟨x, hxt⟩⟩ : Metric.closedBall (0 : ℝ) M)) : ℝ)
            + dist (((z ⟨c ⟨x, hxt⟩, hcD ⟨x, hxt⟩⟩ : Metric.closedBall (0 : ℝ) M)) : ℝ)
              (u (φ l) (c ⟨x, hxt⟩)) := dist_triangle _ _ _
        _ = dist (u (φ k) (c ⟨x, hxt⟩))
              (((z ⟨c ⟨x, hxt⟩, hcD ⟨x, hxt⟩⟩ : Metric.closedBall (0 : ℝ) M)) : ℝ)
            + dist (u (φ l) (c ⟨x, hxt⟩))
              (((z ⟨c ⟨x, hxt⟩, hcD ⟨x, hxt⟩⟩ : Metric.closedBall (0 : ℝ) M)) : ℝ) := by
              rw [dist_comm (u (φ l) (c ⟨x, hxt⟩))
                (((z ⟨c ⟨x, hxt⟩, hcD ⟨x, hxt⟩⟩ : Metric.closedBall (0 : ℝ) M)) : ℝ)]
        _ < ε / 4 + ε / 4 := add_lt_add hk' hl'
        _ = ε / 2 := by ring
    calc dist (u (φ k) y) (u (φ l) y)
        ≤ dist (u (φ k) y) (u (φ k) (c ⟨x, hxt⟩))
          + dist (u (φ k) (c ⟨x, hxt⟩)) (u (φ l) y) := dist_triangle _ _ _
      _ ≤ dist (u (φ k) y) (u (φ k) (c ⟨x, hxt⟩))
          + (dist (u (φ k) (c ⟨x, hxt⟩)) (u (φ l) (c ⟨x, hxt⟩))
            + dist (u (φ l) (c ⟨x, hxt⟩)) (u (φ l) y)) := by
            gcongr; exact dist_triangle _ _ _
      _ < ε / 4 + (ε / 2 + ε / 4) := add_lt_add e1 (add_lt_add e2 e3)
      _ = ε := by ring
  -- Pointwise Cauchy everywhere on `K`, and the limit function.
  have hcauchy : ∀ x ∈ K, CauchySeq (fun k => u (φ k) x) := by
    intro x hx
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hCau ε hε
    exact ⟨N, fun m hm n hn => hN m hm n hn x hx⟩
  let g : EuclideanSpace ℝ (Fin 4) → ℝ := fun x =>
    if hx : x ∈ K then Classical.choose (cauchySeq_tendsto_of_complete (hcauchy x hx)) else 0
  have hgK : ∀ x ∈ K, Tendsto (fun k => u (φ k) x) atTop (nhds (g x)) := by
    intro x hx
    simp only [g, dif_pos hx]
    exact Classical.choose_spec (cauchySeq_tendsto_of_complete (hcauchy x hx))
  refine ⟨φ, hφmono, g, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hCau (ε / 2) (by linarith)
  refine eventually_atTop.mpr ⟨N, fun k hk y hy => ?_⟩
  have htend : Tendsto (fun l => dist (u (φ l) y) (u (φ k) y)) atTop
      (nhds (dist (g y) (u (φ k) y))) := (hgK y hy).dist tendsto_const_nhds
  have hle : dist (g y) (u (φ k) y) ≤ ε / 2 := by
    refine le_of_tendsto htend ?_
    exact eventually_atTop.mpr ⟨N, fun l hl => le_of_lt (hN l hl k hk y hy)⟩
  linarith

end Commons.Topology.Metric