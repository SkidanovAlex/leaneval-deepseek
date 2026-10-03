import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.iterate_re_growth

namespace Work.FatouCoord.Petal

open Work.FatouCoord Metric Set Filter

theorem petal_orbit_tendsto_zero {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') : ∃ M : ℝ, 0 < M ∧ ∀ z ∈ Petal r M, Tendsto (fun n : ℕ => f^[n] z) atTop (nhds 0) := by
  obtain ⟨N, hNpos, hNr, hgrowth⟩ := Work.FatouCoord.Estimate.iterate_re_growth hb
  have hr : 0 < r := hb.hr
  refine ⟨max N 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz
  have hz0 : z ≠ 0 := ne_zero_of_mem_Petal hz
  have hchart : chart z ∈ PetalChart r (max N 1) := (chart_mem_Petal_iff hr hz0).mp hz
  have hwN : N < (chart z).re := lt_of_le_of_lt (le_max_left _ _) hchart.1
  have hgrowthz : ∀ k : ℕ, N + (k:ℝ)/2 ≤ ((wMap f)^[k] (chart z)).re :=
    fun k => hgrowth (chart z) hwN k
  have hne : ∀ k : ℕ, (wMap f)^[k] (chart z) ≠ 0 := by
    intro k
    have h := hgrowthz k
    have hk0 : (0:ℝ) ≤ (k:ℝ)/2 := by positivity
    have hpos : 0 < ((wMap f)^[k] (chart z)).re := by linarith
    intro hc
    rw [hc] at hpos
    simp at hpos
  have hiter : ∀ k : ℕ, f^[k] z = chart ((wMap f)^[k] (chart z)) := by
    intro k
    induction k with
    | zero =>
        simp only [Function.iterate_zero_apply]
        rw [chart_chart hz0]
    | succ k ih =>
        rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
        have hvne : f (chart ((wMap f)^[k] (chart z))) ≠ 0 := by
          intro hc
          have hzero : (wMap f)^[k+1] (chart z) = 0 := by
            rw [Function.iterate_succ_apply']
            simp [wMap, hc]
          exact hne (k+1) hzero
        rw [show wMap f ((wMap f)^[k] (chart z))
              = chart (f (chart ((wMap f)^[k] (chart z)))) from rfl,
            chart_chart hvne]
  have hbound : ∀ k : ℕ, ‖f^[k] z‖ ≤ 1 / (N + (k:ℝ)/2) := by
    intro k
    have hk : N + (k:ℝ)/2 ≤ ‖((wMap f)^[k] (chart z))‖ := by
      have h1 := hgrowthz k
      have h2 : ((wMap f)^[k] (chart z)).re ≤ ‖((wMap f)^[k] (chart z))‖ :=
        Complex.re_le_norm _
      linarith
    have hpos : 0 < N + (k:ℝ)/2 := by
      have hk0 : (0:ℝ) ≤ (k:ℝ)/2 := by positivity
      linarith
    rw [hiter k, norm_chart (hne k), one_div]
    exact inv_anti₀ hpos hk
  have hlim : Tendsto (fun k : ℕ => 1 / (N + (k:ℝ)/2)) atTop (nhds 0) := by
    have h1 : Tendsto (fun k : ℕ => (k:ℝ)/2) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num)
    have h2 : Tendsto (fun k : ℕ => N + (k:ℝ)/2) atTop atTop :=
      tendsto_atTop_mono (fun k => by
        have hk0 : (0:ℝ) ≤ (k:ℝ)/2 := by positivity
        linarith) h1
    have h3 : Tendsto (fun k : ℕ => (N + (k:ℝ)/2)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp h2
    simpa [one_div] using h3
  have hnormlim : Tendsto (fun k : ℕ => ‖f^[k] z‖) atTop (nhds 0) :=
    squeeze_zero (fun k => norm_nonneg _) hbound hlim
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnormlim

end Work.FatouCoord.Petal
