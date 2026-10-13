import Mathlib
import Submission.Work.WilG3.Defs
import Submission.Work.WilG3.GeoLTile
import Submission.Work.WilG3.GeoRTile

set_option linter.unusedVariables false
-- (`ε > 0` is not needed for the covering estimate: it holds for every real `ε`.)

namespace Work.WilG3

/-! ## The chart family covers `[ρ^K/2, 1 - ρ^K/2]`

With `geoRho r = 1 - 1/(r+2) ∈ (0, 1]`, the left charts `[ρ^(k+1)/2, ρ^k/2]`, `k < K`, are
consecutive closed intervals whose union over `k < K` is exactly `[ρ^K/2, 1/2]`; the right charts
are their mirror images under `x ↦ 1 - x` and tile `[1/2, 1 - ρ^K/2]`.  These two tilings are
`GeoLTile` and `GeoRTile` (proved in the sibling modules of this directory); below we convert them
into membership in the chart family `geoCharts r K` and finish the covering.

Since `[ε, 1-ε] ⊆ [ρ^K/2, 1 - ρ^K/2]` as soon as `ρ^K/2 ≤ ε`, the cover holds for every `ε`,
positive or not. -/

/-- The chart of scale `k < K` on the left belongs to the chart family. -/
theorem mem_geoCharts_geoL (r K k : ℕ) (hk : k < K) :
    (geoRho r ^ (k + 1) / 2, geoRho r ^ k / 2) ∈ geoCharts r K :=
  mem_geoCharts.mpr (Or.inl (mem_geoL.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩))

/-- The chart of scale `k < K` on the right belongs to the chart family. -/
theorem mem_geoCharts_geoR (r K k : ℕ) (hk : k < K) :
    (1 - geoRho r ^ k / 2, 1 - geoRho r ^ (k + 1) / 2) ∈ geoCharts r K :=
  mem_geoCharts.mpr (Or.inr (mem_geoR.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩))

-- Covering half of `WilkieDesign.CG.G3_affine_cover` for the concrete chart family of
-- `Submission/Work/WilG3/Defs.lean` (re-read the definitions there: every pair is stored as
-- `(lower endpoint, upper endpoint)`).  If the scales have reached below `ε` (`ρ^K/2 ≤ ε`) and
-- `K ≥ 1`, the charts cover `[ε, 1-ε]`.  In fact they cover the whole interval
-- `[ρ^K/2, 1 - ρ^K/2]`: the left charts `k ↦ [ρ^(k+1)/2, ρ^k/2]` (`k < K`) tile it down to `1/2`
-- (induction on `K` using `1 ≥ ρ ≥ 0`), their mirror images tile `[1/2, 1 - ρ^K/2]`, and
-- `[ε, 1-ε] ⊆ [ρ^K/2, 1 - ρ^K/2]` follows from `ρ^K/2 ≤ ε` (for `ε ≥ 1/2` the left side is empty
-- or `{1/2}`, which lies in `[ρ^K/2, 1 - ρ^K/2]` since `ρ^K < 1`).
theorem GeoChartsCovers (r K : ℕ) (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε)
    (hρ : geoRho r ^ K / 2 ≤ ε) :
    Set.Icc ε (1 - ε) ⊆ ⋃ p ∈ geoCharts r K, Set.Icc p.1 p.2 := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  -- `ε ≤ x ≤ 1 - ε` together with `ρ^K/2 ≤ ε` gives `ρ^K/2 ≤ x ≤ 1 - ρ^K/2`.
  have hxlo : geoRho r ^ K / 2 ≤ x := le_trans hρ hx1
  have hxhi : x ≤ 1 - geoRho r ^ K / 2 := le_trans hx2 (by linarith)
  by_cases hxle : x ≤ 1 / 2
  · -- left half: the left chart of some scale `k < K` contains `x`
    obtain ⟨k, hk, hkl, hku⟩ := GeoLTile r K hK x hxlo hxle
    refine Set.mem_iUnion.mpr ⟨(geoRho r ^ (k + 1) / 2, geoRho r ^ k / 2), ?_⟩
    refine Set.mem_iUnion.mpr ⟨mem_geoCharts_geoL r K k hk, ?_⟩
    exact ⟨hkl, hku⟩
  · -- right half: the right chart of some scale `k < K` contains `x`
    obtain ⟨k, hk, hkl, hku⟩ := GeoRTile r K hK x (le_of_lt (not_le.mp hxle)) hxhi
    refine Set.mem_iUnion.mpr ⟨(1 - geoRho r ^ k / 2, 1 - geoRho r ^ (k + 1) / 2), ?_⟩
    refine Set.mem_iUnion.mpr ⟨mem_geoCharts_geoR r K k hk, ?_⟩
    exact ⟨hkl, hku⟩

end Work.WilG3
