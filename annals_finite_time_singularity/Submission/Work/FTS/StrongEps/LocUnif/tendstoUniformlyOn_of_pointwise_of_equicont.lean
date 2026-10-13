import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Lemmas

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

theorem tendstoUniformlyOn_of_pointwise_of_equicont {k : ℕ} {K : Set (ℝ × ℝ)}
    {F : ℕ → ℝ × ℝ → (Fin k → ℝ)} {f : ℝ × ℝ → (Fin k → ℝ)}
    (hK : IsCompact K)
    (hpt : ∀ p ∈ K, Filter.Tendsto (fun n => F n p) Filter.atTop (nhds (f p)))
    (heqc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
      dist p q < δ → ‖F n p - F n q‖ < ε) :
    TendstoUniformlyOn F f Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨δ, hδpos, hδ⟩ := heqc (ε / 3) hε3
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun p => Metric.ball p δ)
    (fun p _ => Metric.ball_mem_nhds p hδpos)
  -- Eventually all centres of the finite cover are close to the limit function.
  have hcen : ∀ᶠ n in Filter.atTop, ∀ y ∈ t, dist (F n y) (f y) < ε / 3 := by
    rw [Filter.eventually_all_finset]
    intro y hy
    exact (hpt y (htK y hy)).eventually (Metric.ball_mem_nhds (f y) hε3)
  filter_upwards [hcen] with n hn
  intro x hx
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.1 (hcov hx)
  have hxyδ : dist x y < δ := by simpa [Metric.mem_ball] using hxy
  have hny' : dist (f y) (F n y) < ε / 3 := by
    have h0 := hn y hyt
    rwa [dist_comm] at h0
  -- `F n` itself is `δ`-equicontinuous, uniformly in `n`.
  have hFnyx : dist (F n y) (F n x) < ε / 3 := by
    have h1 : dist (F n x) (F n y) < ε / 3 := by
      have h0 := hδ n x hx y (htK y hyt) hxyδ
      rwa [← dist_eq_norm] at h0
    rwa [dist_comm] at h1
  -- Passing to the pointwise limits at `x` and `y` gives the same bound for `f`.
  have hfyx : dist (f x) (f y) ≤ ε / 3 := by
    refine le_of_tendsto' ((hpt x hx).dist (hpt y (htK y hyt))) (fun m => ?_)
    have h1 : dist (F m x) (F m y) < ε / 3 := by
      have h0 := hδ m x hx y (htK y hyt) hxyδ
      rwa [← dist_eq_norm] at h0
    linarith
  have htri : dist (f x) (F n x) ≤
      dist (f x) (f y) + dist (f y) (F n y) + dist (F n y) (F n x) :=
    dist_triangle4 _ _ _ _
  linarith

end Work.FTS.StrongEps.LocUnif
