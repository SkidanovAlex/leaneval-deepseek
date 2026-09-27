import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.germCHelpers

namespace Work.EQ

open Complex Metric Filter Set
open scoped Topology

noncomputable section

set_option maxHeartbeats 1600000

/-- **The `y`-coordinate of the germ is invertible near the origin.**  There is a holomorphic
local right inverse `g` of `u ↦ (germC a h u).2` near `0`, with `g 0 = 0`.

The inputs are `germC_facts` (analyticity near `0`, and `deriv (fun u => (germC a h u).2) 0 =
(1 - a)/2 ≠ 0` for `a < 1`) and the analytic inverse function theorem
(`AnalyticAt.localInverse`). -/
theorem germC_y_inverse {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ (ρ : ℝ) (g : ℂ → ℂ), 0 < ρ ∧ AnalyticOnNhd ℂ g (Metric.ball 0 ρ) ∧ g 0 = 0 ∧
      ∀ w ∈ Metric.ball (0 : ℂ) ρ, (germC a h (g w)).2 = w := by
  obtain ⟨ρ₀, hρ₀pos, hAnC, hgerm0, -, -, hderiv⟩ := germC_facts ha0 ha1 hh
  let Y : ℂ → ℂ := fun u => (germC a h u).2
  have hYan : AnalyticAt ℂ Y 0 := by
    have hproj : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (germC a h 0) :=
      (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _
    have h1 := hproj.comp (hAnC 0 (by simp [hρ₀pos]))
    simpa [Y, Function.comp_def] using h1
  have hY0 : Y 0 = 0 := by simp [Y, hgerm0]
  have hYderiv : deriv Y 0 = (((1 - a) / 2 : ℝ) : ℂ) := hderiv
  have hf' : deriv Y 0 ≠ 0 := by
    rw [hYderiv, Complex.ofReal_ne_zero]
    exact div_ne_zero (by linarith) (by norm_num)
  let g : ℂ → ℂ := HasStrictDerivAt.localInverse Y (deriv Y 0) 0 hYan.hasStrictDerivAt hf'
  have hgan : AnalyticAt ℂ g 0 := by
    have h := hYan.analyticAt_localInverse hf'
    rwa [hY0] at h
  have hg0 : g 0 = 0 := by
    have h := (hYan.hasStrictDerivAt.eventually_left_inverse hf').self_of_nhds
    rwa [hY0] at h
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := hgan.exists_ball_analyticOnNhd
  have hrev : ∀ᶠ y in 𝓝 (Y 0), Y (g y) = y :=
    hYan.hasStrictDerivAt.eventually_right_inverse hf'
  rw [hY0] at hrev
  obtain ⟨ρ₂, hρ₂pos, hρ₂⟩ := Metric.mem_nhds_iff.mp hrev
  refine ⟨min ρ₁ ρ₂, g, lt_min hρ₁pos hρ₂pos,
    hρ₁.mono (Metric.ball_subset_ball (min_le_left _ _)), hg0, ?_⟩
  intro w hw
  exact hρ₂ (Metric.ball_subset_ball (min_le_right _ _) hw)

end

end Work.EQ
