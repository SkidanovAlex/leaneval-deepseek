import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

lemma tendstoUniformlyOn_of_pointwise_of_holder {K : Set (ℝ × ℝ)} {F : ℕ → ℝ × ℝ → ℝ}
    {f : ℝ × ℝ → ℝ}
    (hK : IsCompact K)
    (hpt : ∀ p ∈ K, Filter.Tendsto (fun n : ℕ => F n p) Filter.atTop (nhds (f p)))
    (heqc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
      dist p q < δ → |F n p - F n q| < ε) :
    TendstoUniformlyOn F f Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := heqc (ε / 3) (by linarith)
  obtain ⟨t, htK, htfin, hcov⟩ := hK.finite_cover_balls hδpos
  have hev : ∀ᶠ n in Filter.atTop, ∀ y ∈ t, |F n y - f y| < ε / 3 := by
    rw [htfin.eventually_all]
    intro y hy
    have h1 : ∀ᶠ n in Filter.atTop, dist (F n y) (f y) < ε / 3 :=
      Metric.tendsto_nhds.mp (hpt y (htK hy)) (ε / 3) (by linarith)
    filter_upwards [h1] with n hn
    simpa [Real.dist_eq] using hn
  filter_upwards [hev] with n hn
  intro x hx
  rcases Set.mem_iUnion₂.mp (hcov hx) with ⟨y, hyt, hxy⟩
  have hyK : y ∈ K := htK hyt
  have hdxy : dist x y < δ := Metric.mem_ball.mp hxy
  have hlim : Filter.Tendsto (fun n => dist (F n y) (F n x)) Filter.atTop
      (nhds (dist (f y) (f x))) := (hpt y hyK).dist (hpt x hx)
  have hle : dist (f y) (f x) ≤ ε / 3 := by
    refine le_of_tendsto hlim ?_
    filter_upwards with m
    rw [Real.dist_eq, abs_sub_comm]
    exact le_of_lt (hδ m x hx y hyK hdxy)
  calc dist (f x) (F n x)
      ≤ dist (f x) (f y) + dist (f y) (F n y) + dist (F n y) (F n x) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h1 : dist (f x) (f y) ≤ ε / 3 := by
          rw [dist_comm]; exact hle
        have h2 : dist (f y) (F n y) < ε / 3 := by
          rw [Real.dist_eq, abs_sub_comm]; exact hn y hyt
        have h3 : dist (F n y) (F n x) < ε / 3 := by
          rw [Real.dist_eq, abs_sub_comm]; exact hδ n x hx y hyK hdxy
        linarith
    _ = ε := by ring

end Work.FTS.StrongEps.E5G
