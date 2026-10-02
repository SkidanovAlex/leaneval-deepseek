import Mathlib
import Submission.Work.FatouCoordFix.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Every orbit in the wide petal reaches the half-plane petal

Let `f : ℂ → ℂ` be a (not assumed holomorphic) map whose chart dynamics `wMap f` grows in the
wide sector of level `M'`: on `{M' < sgauge W}` the gauge stays `> M'` and the real part
increases by at least `1/2`.  Then every `u` in the wide petal `WidePetal M'` has an iterate
`f^[n] u` in the half-plane petal `HPlanePetal M`, for **every** level `M` (no relation between
`M` and `M'` is needed).

The proof is purely combinatorial.  Writing `W k = (wMap f)^[k] (chart u)` for the chart orbit,
the hypothesis gives `M' < sgauge (W k)` and `(W k).re + 1/2 ≤ (W (k+1)).re` for all `k`, hence
`(W k).re → +∞`.  Moreover `chart (f^[k] u) = W k` for all `k`: this is the point where the
convention `1/0 = 0` matters, because `chart ∘ chart = id` holds on *all* of `ℂ` (not merely on
`ℂ \ {0}`), so the identity survives an orbit passing through `0`.  Picking `N` with
`(W N).re > max M 0` then gives `f^[N] u ≠ 0` (as `W N ≠ 0`) and `M < (chart (f^[N] u)).re`,
which is exactly `f^[N] u ∈ HPlanePetal M`.
-/

open Set Filter Function

namespace Work.FatouCoordFix.HPetal

/-- The parabolic chart `z ↦ -1/z` is an involution of the whole plane: with the convention
`1/0 = 0` one has `chart 0 = 0`, so `chart (chart z) = z` also at `z = 0`. -/
theorem chart_chart_all (z : ℂ) : Work.FatouCoord.chart (Work.FatouCoord.chart z) = z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Work.FatouCoord.chart]
  · exact Work.FatouCoord.chart_chart hz

/-- The chart value of an iterate is the iterate of the chart value under `wMap`. -/
theorem chart_iterate_wMap (f : ℂ → ℂ) (u : ℂ) (k : ℕ) :
    Work.FatouCoord.chart ((f^[k]) u) = (Work.FatouCoord.wMap f)^[k] (Work.FatouCoord.chart u) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    simp only [Work.FatouCoord.wMap]
    rw [chart_chart_all]

theorem exists_iterate_mem_HPlanePetal {f : ℂ → ℂ} {M M' : ℝ} (hgr : ∀ W : ℂ, M' < Work.FatouCoord.Flower.sgauge W → M' < Work.FatouCoord.Flower.sgauge (Work.FatouCoord.wMap f W) ∧ W.re + 1 / 2 ≤ (Work.FatouCoord.wMap f W).re) {u : ℂ} (hu : u ∈ Work.FatouCoord.Flower.WidePetal M') : ∃ n : ℕ, (f^[n]) u ∈ Work.FatouCoordFix.HPlanePetal M := by
  obtain ⟨hu0, huM⟩ := hu
  -- the chart orbit of `u`
  set W : ℕ → ℂ := fun k => (Work.FatouCoord.wMap f)^[k] (Work.FatouCoord.chart u) with hW
  have hW0 : W 0 = Work.FatouCoord.chart u := rfl
  have hstep : ∀ k : ℕ, W (k + 1) = Work.FatouCoord.wMap f (W k) := fun k =>
    Function.iterate_succ_apply' _ _ _
  -- the chart orbit stays in the wide sector
  have hsg : ∀ k : ℕ, M' < Work.FatouCoord.Flower.sgauge (W k) := by
    intro k
    induction k with
    | zero => rw [hW0]; exact huM
    | succ k ih => rw [hstep k]; exact (hgr (W k) ih).1
  -- hence its real part grows without bound
  have hre : ∀ k : ℕ, (W 0).re + (k : ℝ) / 2 ≤ (W k).re := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h2 : (W k).re + 1 / 2 ≤ (W (k + 1)).re := by
        have h2' := (hgr (W k) (hsg k)).2
        rwa [← hstep k] at h2'
      have hcast : ((k + 1 : ℕ) : ℝ) / 2 = (k : ℝ) / 2 + 1 / 2 := by push_cast; ring
      rw [hcast]
      linarith
  -- the chart of the `k`-th iterate of `u` is the `k`-th point of the chart orbit
  have hchart_iter : ∀ k : ℕ, Work.FatouCoord.chart ((f^[k]) u) = W k := fun k =>
    chart_iterate_wMap f u k
  -- choose an index whose chart real part exceeds both `M` and `0`
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (max M 0 - (W 0).re))
  have hNbound : max M 0 < (W 0).re + (N : ℝ) / 2 := by
    have h : (2 * (max M 0 - (W 0).re) : ℝ) < (N : ℝ) := hN
    linarith
  have hWN : max M 0 < (W N).re := lt_of_lt_of_le hNbound (hre N)
  refine ⟨N, ?_, ?_⟩
  · -- `f^[N] u ≠ 0`, since its chart value `W N` has positive real part
    intro h0
    have hz : Work.FatouCoord.chart ((f^[N]) u) = 0 := by rw [h0]; simp [Work.FatouCoord.chart]
    rw [hchart_iter N] at hz
    have : (W N).re = 0 := by rw [hz]; simp
    linarith [hWN, le_max_right M 0]
  · show M < (Work.FatouCoord.chart ((f^[N]) u)).re
    rw [hchart_iter N]
    exact lt_of_le_of_lt (le_max_left M 0) hWN

end Work.FatouCoordFix.HPetal
