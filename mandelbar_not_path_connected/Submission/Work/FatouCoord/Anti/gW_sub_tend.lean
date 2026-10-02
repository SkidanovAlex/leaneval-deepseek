import Mathlib
import Submission.Work.FatouCoord.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The `w`-chart pull-back of `g` differs from `star w` by `star b`

Let `g` be an antiholomorphic germ at `0` which is a first-order approximation to the reflection
`z ↦ star z`: on the disc of radius `r`,

`‖g z - star z‖ ≤ G * ‖z‖ ^ 2`,

and whose second-order quotient converges,

`(star (g z) - z) / z ^ 2 → b`  as `z → 0`, `z ≠ 0`.

Then, along the region `Re w → +∞` of the parabolic chart `w = -1/z`, the conjugate dynamics
`chart (g (chart w))` is asymptotic to the reflection `star w` with constant `star b`:

`chart (g (chart w)) - star w → star b`  as `Re w → +∞`.

This is the `w`-chart statement that lets one compare the anti-equivariant dynamics with the
holomorphic Fatou coordinate.

The proof is the computation

`chart (g z) - star (chart z) = e / (g z * star z)`,  `e = g z - star z`,
`star ((star (g z) - z) / z ^ 2) = e / (star z) ^ 2`,

whose difference is the exactly cancellable quantity `- e ^ 2 / (g z * (star z) ^ 2)`.  Since
`e = O(‖z‖ ^ 2)` and `‖g z‖ ≥ ‖z‖ / 2` for small `z`, that difference is `O(‖z‖) = O(1/‖w‖)`,
while the leading term tends to `star b` because `chart → 0` (punctured) along `Re w → +∞`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

open scoped Topology

namespace Work.FatouCoord.Anti

open Work.FatouCoord Filter Metric

/-- In the parabolic chart `w ↦ z = -1/w`, the region `Re w → +∞` corresponds to `z → 0` inside
the punctured plane.  Hence the chart `z = -1/w` tends to `0` along `comap Complex.re atTop`.

Indeed, `Re w > M` forces `‖z‖ = 1/‖w‖ ≤ 1/Re w < 1/M` and `z ≠ 0`. -/
theorem tendsto_chart_comap_re :
    Filter.Tendsto (chart : ℂ → ℂ) (Filter.comap Complex.re Filter.atTop)
      (nhdsWithin 0 {0}ᶜ) := by
  rw [Filter.tendsto_def]
  intro s hs
  rw [Metric.mem_nhdsWithin_iff] at hs
  obtain ⟨e, he, hsub⟩ := hs
  rw [Filter.mem_comap]
  refine ⟨Set.Ioi (max e⁻¹ 1), Ioi_mem_atTop _, ?_⟩
  intro w hw
  simp only [Set.mem_preimage, Set.mem_Ioi, max_lt_iff] at hw
  obtain ⟨hw1, hw2⟩ := hw
  apply hsub
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw2; exact absurd hw2 (by norm_num)
  rw [Set.mem_inter_iff, mem_ball_zero_iff, Set.mem_compl_singleton_iff]
  refine ⟨?_, chart_ne_zero hw0⟩
  rw [norm_chart hw0]
  exact (inv_lt_comm₀ he (norm_pos_iff.mpr hw0)).mp (lt_of_lt_of_le hw1 (Complex.re_le_norm w))

/-- **The error term is `O(1/Re w)`.**  Under the linear bound `‖g z - star z‖ ≤ G₀ ‖z‖ ^ 2` on
the disc of radius `r`, the difference between the chart pull-back of `g` and the leading term
`star ((star (g z) - z)/z ^ 2)` is bounded by `2 G₀ ^ 2 / Re w` as soon as `Re w` exceeds both
`1/r` and `2 G₀`. -/
theorem err_bound {g : ℂ → ℂ} {r G₀ : ℝ} (hr : 0 < r) (hG₀ : 0 ≤ G₀)
    (hlin : ∀ z ∈ Metric.ball 0 r, ‖g z - star z‖ ≤ G₀ * ‖z‖ ^ 2)
    {w : ℂ} (hw : 0 < w.re) (hwr : 1 / r < w.re) (hwG : 2 * G₀ < w.re) :
    ‖(chart (g (chart w)) - star w)
      - star ((star (g (chart w)) - chart w) / (chart w) ^ 2)‖ ≤ 2 * G₀ ^ 2 / w.re := by
  set z := chart w with hzdef
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  have hz0 : z ≠ 0 := by rw [hzdef]; exact chart_ne_zero hw0
  have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hsz : star z ≠ 0 := by simpa using hz0
  have hzw : chart z = w := by rw [hzdef, chart_chart hw0]
  have hzn : ‖z‖ = (‖w‖)⁻¹ := by rw [hzdef, norm_chart hw0]
  have hznle : ‖z‖ ≤ 1 / w.re := by
    rw [hzn, one_div]
    simpa [one_div] using one_div_le_one_div_of_le hw (Complex.re_le_norm w)
  have h1wr : 1 / w.re < r := by
    rw [div_lt_iff₀ hw]
    have h2 : 1 < w.re * r := (div_lt_iff₀ hr).mp hwr
    linarith [mul_comm w.re r]
  have hzr : ‖z‖ < r := lt_of_le_of_lt hznle h1wr
  have hzball : z ∈ Metric.ball 0 r := by rw [mem_ball_zero_iff]; exact hzr
  have hlinz : ‖g z - star z‖ ≤ G₀ * ‖z‖ ^ 2 := hlin z hzball
  -- `G₀ ‖z‖ < 1/2`, hence `‖g z‖ ≥ ‖z‖/2`.
  have hzG : G₀ * ‖z‖ < 1 / 2 := by
    have h1 : G₀ * ‖z‖ ≤ G₀ * (1 / w.re) := mul_le_mul_of_nonneg_left hznle hG₀
    have h2 : G₀ * (1 / w.re) < 1 / 2 := by
      rw [mul_one_div, div_lt_iff₀ hw]; linarith
    linarith
  have hgnorm : ‖z‖ / 2 ≤ ‖g z‖ := by
    have h2 : ‖star z - g z‖ = ‖g z - star z‖ := by
      rw [show star z - g z = -(g z - star z) by ring, norm_neg]
    have h4 : ‖star z - g z‖ ≤ G₀ * ‖z‖ ^ 2 := by rw [h2]; exact hlinz
    have h5 := norm_sub_norm_le (star z) (g z)
    rw [norm_star] at h5
    have h6 : G₀ * ‖z‖ ^ 2 < (1 / 2) * ‖z‖ := by
      have h7 := mul_lt_mul_of_pos_right hzG hzp
      calc G₀ * ‖z‖ ^ 2 = (G₀ * ‖z‖) * ‖z‖ := by ring
        _ < (1 / 2) * ‖z‖ := h7
    linarith
  have hgz0 : g z ≠ 0 := by
    intro h; rw [h] at hgnorm; simp at hgnorm; linarith [hzp]
  -- the two algebraic identities
  have hA : chart (g z) - star (chart z) = (g z - star z) / (g z * star z) := by
    have h1 : star (chart z) = -1 / star z := by simp [chart]
    rw [chart, h1, div_sub_div _ _ hgz0 hsz]
    ring
  have hB : star ((star (g z) - z) / z ^ 2) = (g z - star z) / (star z) ^ 2 := by simp
  have hD : (chart (g z) - star w) - star ((star (g z) - z) / z ^ 2)
      = -(g z - star z) ^ 2 / (g z * (star z) ^ 2) := by
    rw [← hzw, hA, hB]
    field_simp <;> ring
  have hDnorm : ‖(chart (g z) - star w) - star ((star (g z) - z) / z ^ 2)‖
      = ‖g z - star z‖ ^ 2 / (‖g z‖ * ‖z‖ ^ 2) := by
    rw [hD, norm_div, norm_neg, norm_pow, norm_mul, norm_pow, norm_star]
  rw [hDnorm]
  have h2 : (G₀ * ‖z‖ ^ 2) ^ 2 / ((‖z‖ / 2) * ‖z‖ ^ 2) = 2 * G₀ ^ 2 * ‖z‖ := by
    field_simp <;> ring
  have h3 : ‖g z - star z‖ ^ 2 / (‖g z‖ * ‖z‖ ^ 2)
      ≤ (G₀ * ‖z‖ ^ 2) ^ 2 / ((‖z‖ / 2) * ‖z‖ ^ 2) := by
    have h1 : ‖g z - star z‖ ^ 2 ≤ (G₀ * ‖z‖ ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hlinz 2
    gcongr
  have h4 : 2 * G₀ ^ 2 * ‖z‖ ≤ 2 * G₀ ^ 2 / w.re := by
    have hG2 : (0:ℝ) ≤ 2 * G₀ ^ 2 := by positivity
    calc 2 * G₀ ^ 2 * ‖z‖ ≤ 2 * G₀ ^ 2 * (1 / w.re) := mul_le_mul_of_nonneg_left hznle hG2
      _ = 2 * G₀ ^ 2 / w.re := by ring
  linarith [h3, h2, h4]

theorem gW_sub_tend {g : ℂ → ℂ} {r G : ℝ} {b : ℂ} (hr : 0 < r) (hg_lin : ∀ z ∈ Metric.ball 0 r, ‖g z - star z‖ ≤ G * ‖z‖ ^ 2) (hb_tend : Filter.Tendsto (fun z : ℂ => (star (g z) - z) / z ^ 2) (nhdsWithin 0 {0}ᶜ) (nhds b)) : Filter.Tendsto (fun w : ℂ => Work.FatouCoord.chart (g (Work.FatouCoord.chart w)) - star w) (Filter.comap Complex.re Filter.atTop) (nhds (star b)) := by
  set G₀ : ℝ := max G 0 with hG₀def
  have hG₀ : 0 ≤ G₀ := le_max_right G 0
  have hlin : ∀ z ∈ Metric.ball 0 r, ‖g z - star z‖ ≤ G₀ * ‖z‖ ^ 2 := by
    intro z hz
    have h1 := hg_lin z hz
    have h2 : G * ‖z‖ ^ 2 ≤ G₀ * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left G 0) (by positivity)
    linarith
  -- the leading term `star ((star (g z) - z)/z^2)` tends to `star b` along `Re w → +∞`
  have hF : Filter.Tendsto
      (fun w : ℂ => star ((star (g (chart w)) - chart w) / (chart w) ^ 2))
      (Filter.comap Complex.re Filter.atTop) (nhds (star b)) := by
    have h1 : Filter.Tendsto (fun z : ℂ => star ((star (g z) - z) / z ^ 2))
        (nhdsWithin 0 {0}ᶜ) (nhds (star b)) :=
      (continuous_star.tendsto b).comp hb_tend
    exact h1.comp tendsto_chart_comap_re
  -- the error term tends to `0`
  have herr : Filter.Tendsto
      (fun w : ℂ => (chart (g (chart w)) - star w)
        - star ((star (g (chart w)) - chart w) / (chart w) ^ 2))
      (Filter.comap Complex.re Filter.atTop) (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set M : ℝ := 1 / r + 1 + (2 * G₀ + 1) + (2 * G₀ ^ 2 / ε + 1) with hMdef
    have hA1 : (0:ℝ) ≤ 2 * G₀ + 1 := by linarith
    have hA2 : (0:ℝ) ≤ 2 * G₀ ^ 2 / ε + 1 := by positivity
    refine Filter.mem_comap.mpr ⟨Set.Ioi M, Ioi_mem_atTop M, ?_⟩
    intro w hw
    simp only [Set.mem_preimage, Set.mem_Ioi] at hw
    have hMr : 1 / r < w.re := by linarith [hMdef, hA1, hA2, hw]
    have h1r : (0:ℝ) < 1 / r := by positivity
    have hwpos : 0 < w.re := by linarith [hMdef, hA1, hA2, hw, h1r]
    have hMG : 2 * G₀ < w.re := by linarith [hMdef, hA1, hA2, hw]
    have hMe : 2 * G₀ ^ 2 / ε < w.re := by linarith [hMdef, hA1, hA2, hw]
    have hfin : 2 * G₀ ^ 2 / w.re < ε := by
      rw [div_lt_iff₀ hwpos]
      have h3 : 2 * G₀ ^ 2 < w.re * ε := (div_lt_iff₀ hε).mp hMe
      linarith [mul_comm w.re ε]
    have hb := err_bound hr hG₀ hlin hwpos hMr hMG
    change dist (chart (g (chart w)) - star w
      - star ((star (g (chart w)) - chart w) / (chart w) ^ 2)) 0 < ε
    rw [dist_eq_norm, sub_zero]
    linarith [hb, hfin]
  have hsum := herr.add hF
  simpa using hsum

end Work.FatouCoord.Anti
