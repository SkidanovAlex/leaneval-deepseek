import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.wMap_iterate_deriv_bound
import Submission.Work.Parab.leftCoord.wMap_orbit_facts

namespace Work.Parab.Eends

open scoped Topology
open Filter Metric

/-- **The parabolic germ is analytic and not locally constant near `0`.**  For a germ `f z = z + z^2 h z` satisfying `ParabolicBounds f h a r A A'` there is `ρ ∈ (0, r]` such that every `u` with `‖u‖ < ρ` has `f` analytic at `u` and `f` not constant on any neighbourhood of `u` (equivalently `deriv f u ≠ 0`: `deriv f u = 1 + 2 u h u + u^2 h' u` there, and `‖2 u h u + u^2 h' u‖ ≤ 4ρ + A'ρ^2 ≤ 1/2`, cf. `injOn_ball_of_parabolicBounds`). -/
theorem analytic_not_eventuallyConst {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∀ u : ℂ, ‖u‖ < ρ →
      AnalyticAt ℂ f u ∧ ¬ ∀ᶠ w in nhds u, f w = f u := by
  obtain ⟨ρ, hρpos, hρr, hinj⟩ := Work.Parab.leftCoord.injOn_ball_of_parabolicBounds hb
  refine ⟨ρ, hρpos, hρr, ?_⟩
  -- the disc of radius `ρ` is contained in the disc of radius `r` on which the bounds hold
  have hsub : ball (0 : ℂ) ρ ⊆ ball (0 : ℂ) r := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    linarith
  intro u hu
  have huρ : u ∈ ball (0 : ℂ) ρ := by rw [mem_ball_zero_iff]; exact hu
  have hur : u ∈ ball (0 : ℂ) r := hsub huρ
  constructor
  · -- analyticity: `f` agrees with the explicit polynomial germ near `u`
    have hh : AnalyticAt ℂ h u := hb.h_diff.analyticAt (Metric.isOpen_ball.mem_nhds hur)
    have hid : AnalyticAt ℂ (fun z : ℂ => z) u := analyticAt_id
    have hg : AnalyticAt ℂ (fun z : ℂ => z + z ^ 2 * h z) u :=
      hid.add ((hid.pow 2).mul hh)
    have hev : (fun z : ℂ => z + z ^ 2 * h z) =ᶠ[nhds u] f := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hur] with z hz
      exact (hb.f_eq z hz).symm
    exact hg.congr hev
  · -- non-constancy: an eventual equality near `u` contradicts injectivity on `ball 0 ρ`
    intro hconst
    have hconst' : {w : ℂ | f w = f u} ∈ nhds u := hconst
    have hballρ : ball (0 : ℂ) ρ ∈ nhds u := Metric.isOpen_ball.mem_nhds huρ
    have hinter : ({w : ℂ | f w = f u} ∩ ball (0 : ℂ) ρ) ∈ nhds u :=
      Filter.inter_mem hconst' hballρ
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hinter
    have hcne : ((ε / 2 : ℝ) : ℂ) ≠ 0 := fun h => by
      have h' : ε / 2 = 0 := RCLike.ofReal_eq_zero.mp h
      linarith
    have hwmem : u + ((ε / 2 : ℝ) : ℂ) ∈ ball u ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    obtain ⟨hfeq, hwρ⟩ := hεsub hwmem
    have hune : u + ((ε / 2 : ℝ) : ℂ) ≠ u := by
      intro hwu
      have hdiff : (u + ((ε / 2 : ℝ) : ℂ)) - u = ((ε / 2 : ℝ) : ℂ) := by ring
      rw [hwu, sub_self] at hdiff
      exact hcne hdiff.symm
    exact hune (hinj hwρ huρ hfeq)

end Work.Parab.Eends
