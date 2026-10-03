import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouCoord.Setup
import Submission.Work.Parab.petal_cone
import Submission.Work.Parab.basinGood.basin_good_exists
import Submission.Work.FatouCoord.Estimate.iterate_re_growth

/-!
# PARAB0: the flower and `basin_enter` for the concrete choice `Ωp = Petal r M`

`Ωp` in the interface is ours to choose; we take it to be the library's petal `Petal r M`
(the level `M` of `Work.Parab.basinGood.basin_good_exists`).  This file assembles

* `basin_enter_petal`: `ParabData.basin_enter` for that choice;
* `flower_petal`: `ParabData.flower` for that choice, from the single geometric input that the
  repelling piece `φ '' QLeft ξ` contains the cone `{‖z‖ < ρ, |arg z| ≤ π/2 + π/12}` (which is
  what `Work.Parab.coverCone.cover_cone_wedge` produces).
-/

open Complex Set Metric Filter
open scoped Topology

namespace Work.Parab

noncomputable section

/-- `basin_enter` for `Ωp = Petal r M`: a basin orbit that never hits `0` enters the petal. -/
theorem basin_enter_petal {f h : ℂ → ℂ} {a : ℂ} {r A A' M : ℝ} {D : Set ℂ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') (hM : 0 < M) :
    ∀ z ∈ MandelDim.ParabolicBasin f D, (∀ n : ℕ, f^[n] z ≠ 0) →
      ∃ n : ℕ, f^[n] z ∈ Work.FatouCoord.Petal r M := by
  intro z hz hzne
  obtain ⟨n, hn⟩ := Work.Parab.basinGood.basin_good_exists hb hM z hz
  rcases hn with h | h
  · exact ⟨n, h⟩
  · exact absurd h (hzne n)

/-- The flower for `Ωp = Petal r M`, from the cover of the complementary cone. -/
theorem flower_petal {f : ℂ → ℂ} {φ : ℂ → ℂ} {ξ r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (hcover : ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ →
      |z.arg| ≤ Real.pi / 2 + Real.pi / 12 →
        ∃ w ∈ MandelDim.QLeft ξ, φ w = z) :
    Work.FatouCoord.Petal r M ∪ φ '' MandelDim.QLeft ξ ∪ {0} ∈ nhds (0 : ℂ) := by
  obtain ⟨ρ₂, hρ₂pos, hρ₂⟩ := hcover
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ :=
    petal_cone (r := r) (M := M) (δ := Real.pi / 12) hr hM (by norm_num [Real.pi_pos])
      (by linarith [Real.pi_pos])
  exact flower_of_cones hρ₁pos hρ₂pos hρ₁ hρ₂


/-- **Uniform convergence on the petal.**  The bound `‖f^k u‖ ≤ 1/(N + k/2)` of
`Petal/petal_orbit_tendsto_zero` is uniform in `u ∈ Petal r M'`, so the orbits of the whole petal
converge to `0` uniformly.  This is the `hconvΩ` hypothesis of
`Work.Parab.enterLeft.eventually_mem_left`. -/
theorem petal_uniform_convergence {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ M' : ℝ, 0 < M' ∧ ∀ ε > 0, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∀ u ∈ Work.FatouCoord.Petal r M', ‖(f^[k]) u‖ < ε := by
  obtain ⟨N, hNpos, hNr, hgrowth⟩ := Work.FatouCoord.Estimate.iterate_re_growth hb
  refine ⟨max N 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  have hbound : ∀ u ∈ Work.FatouCoord.Petal r (max N 1), ∀ k : ℕ,
      ‖(f^[k]) u‖ ≤ 1 / (N + (k : ℝ) / 2) := by
    intro u hu k
    have hu0 : u ≠ 0 := Work.FatouCoord.ne_zero_of_mem_Petal hu
    have hchart : Work.FatouCoord.chart u ∈
        Work.FatouCoord.PetalChart r (max N 1) :=
      (Work.FatouCoord.chart_mem_Petal_iff hb.hr hu0).mp hu
    have hwN : N < (Work.FatouCoord.chart u).re :=
      lt_of_le_of_lt (le_max_left _ _) hchart.1
    have hgrowthz : N + (k : ℝ) / 2 ≤
        ((Work.FatouCoord.wMap f)^[k] (Work.FatouCoord.chart u)).re :=
      hgrowth (Work.FatouCoord.chart u) hwN k
    have hne : ∀ j : ℕ, (Work.FatouCoord.wMap f)^[j] (Work.FatouCoord.chart u) ≠ 0 := by
      intro j
      have h := hgrowth (Work.FatouCoord.chart u) hwN j
      have hj0 : (0 : ℝ) ≤ (j : ℝ) / 2 := by positivity
      have hpos : 0 < ((Work.FatouCoord.wMap f)^[j] (Work.FatouCoord.chart u)).re := by
        linarith
      intro hc
      rw [hc] at hpos
      simp at hpos
    have hiter : ∀ j : ℕ, (f^[j]) u =
        Work.FatouCoord.chart ((Work.FatouCoord.wMap f)^[j] (Work.FatouCoord.chart u)) := by
      intro j
      induction j with
      | zero =>
          simp only [Function.iterate_zero_apply]
          rw [Work.FatouCoord.chart_chart hu0]
      | succ j ih =>
          rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
          have hvne : f (Work.FatouCoord.chart
              ((Work.FatouCoord.wMap f)^[j] (Work.FatouCoord.chart u))) ≠ 0 := by
            intro hc
            have hzero : (Work.FatouCoord.wMap f)^[j + 1] (Work.FatouCoord.chart u) = 0 := by
              rw [Function.iterate_succ_apply']
              simp [Work.FatouCoord.wMap, hc]
            exact hne (j + 1) hzero
          rw [show Work.FatouCoord.wMap f
                ((Work.FatouCoord.wMap f)^[j] (Work.FatouCoord.chart u))
              = Work.FatouCoord.chart (f (Work.FatouCoord.chart
                ((Work.FatouCoord.wMap f)^[j] (Work.FatouCoord.chart u)))) from rfl,
            Work.FatouCoord.chart_chart hvne]
    have hk : N + (k : ℝ) / 2 ≤
        ‖((Work.FatouCoord.wMap f)^[k] (Work.FatouCoord.chart u))‖ := by
      have h2 : ((Work.FatouCoord.wMap f)^[k] (Work.FatouCoord.chart u)).re ≤
          ‖((Work.FatouCoord.wMap f)^[k] (Work.FatouCoord.chart u))‖ :=
        Complex.re_le_norm _
      linarith
    have hpos : 0 < N + (k : ℝ) / 2 := by
      have hk0 : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
      linarith
    rw [hiter k, Work.FatouCoord.norm_chart (hne k), one_div]
    exact inv_anti₀ hpos hk
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * (1 / ε - N))
  refine ⟨K, fun k hk u hu => ?_⟩
  have h1 : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlt : 1 / ε < N + (k : ℝ) / 2 := by nlinarith [hK, h1]
  have h2 : 1 / (N + (k : ℝ) / 2) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    have h3 : ε * (1 / ε) = 1 := by field_simp
    nlinarith [hlt, hε]
  exact lt_of_le_of_lt (hbound u hu k) h2

end
end Work.Parab
