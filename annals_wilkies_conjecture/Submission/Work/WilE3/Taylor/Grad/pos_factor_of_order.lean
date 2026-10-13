import Mathlib

namespace Work.WilE3.Taylor.Grad

open Filter Set
open scoped Topology

/-- If `G` is analytic at `0` with analytic order `n`, and `G` is eventually positive on the right
of `0`, then `G` factors as `G t = t ^ n * g t` near `0` with `g` analytic at `0` and `g 0 > 0`. -/
theorem pos_factor_of_order {G : ℝ → ℝ} {n : ℕ} (hG : AnalyticAt ℝ G 0) (hGord : analyticOrderAt G 0 = n) (hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < G t) : ∃ g : ℝ → ℝ, AnalyticAt ℝ g 0 ∧ 0 < g 0 ∧ ∀ᶠ t in nhds (0 : ℝ), G t = t ^ n * g t := by
  -- Extract the analytic factor from the analytic order.
  obtain ⟨g, hgan, hg0ne, hgeq⟩ := (hG.analyticOrderAt_eq_natCast).mp hGord
  have hgeq' : ∀ᶠ t in nhds (0 : ℝ), G t = t ^ n * g t := by
    filter_upwards [hgeq] with t ht
    rw [ht]
    simp [smul_eq_mul]
  refine ⟨g, hgan, ?_, hgeq'⟩
  -- Positivity of `g` on a right-neighbourhood follows from that of `G`, since `t ^ n > 0`.
  have htend : Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (g 0)) :=
    hgan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hgpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < g t := by
    filter_upwards [hpos, hgeq'.filter_mono nhdsWithin_le_nhds,
      (self_mem_nhdsWithin : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioi 0)]
      with t hGt hG' ht
    rw [hG'] at hGt
    exact pos_of_mul_pos_right hGt (le_of_lt (pow_pos ht n))
  -- Passing to the limit along the right gives `0 ≤ g 0`, and `g 0 ≠ 0` upgrades this.
  have hle : 0 ≤ g 0 := ge_of_tendsto htend (hgpos.mono fun t ht => le_of_lt ht)
  exact lt_of_le_of_ne' hle hg0ne

end Work.WilE3.Taylor.Grad
