import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouCoord.Petal.reflected_inverse_germ
import Submission.Work.Parab.Setup

/-!
# PARAB0: from the germ class to the quantitative hypotheses

`MandelDim.IsParabolicGerm f D` says that `f` is holomorphic on the open set `D ∋ 0`,
`f 0 = 0`, `f'(0) = 1` and `f''(0) = 2`.  The `FatouCoord` chapter works with the
quantitative hypothesis `ParabolicBounds f h a r A A'` (`f z = z + z² h z`, `h 0 = 1`,
`h z = 1 + a z + O(z²)`, `h`, `h'` bounded on `ball 0 r`).  This file removes the gap:
every parabolic germ gives `ParabolicBounds` on a ball contained in `D`, together with a
two-sided local inverse on a ball.
-/

open Complex Set Metric Filter
open scoped Topology

namespace Work.Parab

noncomputable section

/-- **The germ of the interface gives the quantitative hypotheses.**  For
`IsParabolicGerm f D` there are `h, a, r, A, A'` with `ParabolicBounds f h a r A A'`
and `ball 0 r ⊆ D`. -/
theorem exists_parabolicBounds_of_germ {f : ℂ → ℂ} {D : Set ℂ}
    (hg : MandelDim.IsParabolicGerm f D) :
    ∃ (h : ℂ → ℂ) (a : ℂ) (r A A' : ℝ),
      Work.FatouCoord.ParabolicBounds f h a r A A' ∧ ball 0 r ⊆ D := by
  obtain ⟨hDopen, h0D, hdiff, hf0, hd1, hd2⟩ := hg
  obtain ⟨ρ, hρpos, hρ⟩ : ∃ ρ > 0, ball (0 : ℂ) ρ ⊆ D := by
    obtain ⟨ρ, hρpos, hρ⟩ := Metric.mem_nhds_iff.mp (hDopen.mem_nhds h0D)
    exact ⟨ρ, hρpos, hρ⟩
  have hfan : AnalyticAt ℂ f 0 := hdiff.analyticAt (hDopen.mem_nhds h0D)
  have hd1' : iteratedDeriv 1 f 0 = 1 := by rw [iteratedDeriv_one]; exact hd1
  have hd2' : iteratedDeriv 2 f 0 = 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact hd2
  obtain ⟨hF, r', A'', A''', hr', hA'', hA''', hEq, hDiff, hClose, hBound, hDeriv⟩ :=
    Work.FatouCoord.Petal.exists_parabolic_germ_bounds (b := iteratedDeriv 3 f 0 / 6)
      hfan hf0 hd1' hd2' (by ring)
  refine ⟨hF, iteratedDeriv 3 f 0 / 6, min r' ρ, A'', A''', ?_, ?_⟩
  · exact Work.FatouCoord.ParabolicBounds.mk (lt_min hr' hρpos) hA'' hA'''
      (fun u hu => hEq u (ball_subset_ball (min_le_left _ _) hu))
      (hDiff.mono (ball_subset_ball (min_le_left _ _)))
      (fun u hu => hClose u (ball_subset_ball (min_le_left _ _) hu))
      (fun u hu => hBound u (ball_subset_ball (min_le_left _ _) hu))
      (fun u hu => hDeriv u (ball_subset_ball (min_le_left _ _) hu))
  · intro u hu
    exact hρ (ball_subset_ball (min_le_right _ _) hu)

/-- **The local inverse on a ball.**  A parabolic germ has a two-sided holomorphic inverse
on a ball, which is the inverse branch used whenever a preimage near `0` is needed. -/
theorem exists_local_inverse_ball {f : ℂ → ℂ} {D : Set ℂ} (hg : MandelDim.IsParabolicGerm f D) :
    ∃ (G : ℂ → ℂ) (δ : ℝ), 0 < δ ∧ G 0 = 0 ∧ deriv G 0 = 1 ∧
      DifferentiableOn ℂ G (ball 0 δ) ∧ (∀ z ∈ ball 0 δ, G z ∈ D) ∧
      (∀ z ∈ ball 0 δ, G (f z) = z) ∧ (∀ z ∈ ball 0 δ, f (G z) = z) := by
  obtain ⟨h, a, r, A, A', hb, hball⟩ := exists_parabolicBounds_of_germ hg
  obtain ⟨G, hGan, hG0, hGd, -, -, hGl, hGr⟩ :=
    Work.FatouCoord.Petal.exists_local_inverse_of_parabolicBounds hb
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), G (f z) = z ∧ f (G z) = z ∧ G z ∈ D := by
    have hDnhds : D ∈ 𝓝 (G 0) := by rw [hG0]; exact hg.1.mem_nhds hg.2.1
    filter_upwards [hGl, hGr, hGan.continuousAt.preimage_mem_nhds hDnhds] with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hdiff_ev : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ G z :=
    hGan.eventually_analyticAt.mono fun z hz => hz.differentiableAt
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.eventually_nhds_iff.mp hdiff_ev
  refine ⟨G, min δ δ₁, lt_min hδpos hδ₁pos, hG0, hGd, ?_,
    fun z hz => (hδ (ball_subset_ball (min_le_left _ _) hz)).2.2,
    fun z hz => (hδ (ball_subset_ball (min_le_left _ _) hz)).1,
    fun z hz => (hδ (ball_subset_ball (min_le_left _ _) hz)).2.1⟩
  intro z hz
  exact (hδ₁ (ball_subset_ball (min_le_right _ _) hz)).differentiableWithinAt

end
end Work.Parab
