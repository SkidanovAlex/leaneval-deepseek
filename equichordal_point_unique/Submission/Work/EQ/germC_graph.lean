import Mathlib
import Submission.Work.EQ.germC_facts

namespace Work.EQ

open Complex Metric Filter Set
open scoped Topology

noncomputable section

set_option maxHeartbeats 1600000

/-- **The germ curve of `A₁` is a graph over its second (`y`) coordinate, near `0`.**

`Work.EQ.germC a h : ℂ → ℂ × ℂ` is the (removable-singularity-completed) stable curve of `A₁` in
rectangular coordinates, as a function of the linearising parameter `u`.  Its second coordinate
`u ↦ (germC a h u).2` has derivative `(1-a)/2 ≠ 0` at `0` (`Work.EQ.germC_facts`), so it is a local
biholomorphism at `0`.  Consequently there are `ρ > 0`, an analytic `φ` and an analytic local
inverse `Yinv` of the `y`-coordinate on `ball 0 ρ`, so that near the origin the germ curve is the
graph `x = φ y`:
* `(germC a h (Yinv y)).2 = y` and `(germC a h (Yinv y)).1 = φ y`;
* `Yinv ((germC a h u).2) = u` for `‖u‖ < ρ`.

Consequence, used in `Work.EQ.H0_path_limit`: the unstable germ curve
`ugermC a h = eqMirror ∘ germC a h` is the zero set of `Z ↦ Z.1 + φ Z.2` near the origin, and a
function taking values on it can be reparametrised analytically by `Z ↦ Yinv Z.2`.

(There is already `Work.EQ.germC_y_inverse` in the workspace, which supplies `Yinv` and
conjunct 3; only the left inverse and the joint radius are new.) -/
theorem germC_graph {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ (ρ : ℝ) (_ : 0 < ρ) (φ : ℂ → ℂ) (Yinv : ℂ → ℂ),
      AnalyticOnNhd ℂ φ (Metric.ball (0 : ℂ) ρ) ∧
      AnalyticOnNhd ℂ Yinv (Metric.ball (0 : ℂ) ρ) ∧
      (∀ y ∈ Metric.ball (0 : ℂ) ρ, (Work.EQ.germC a h (Yinv y)).2 = y) ∧
      (∀ y ∈ Metric.ball (0 : ℂ) ρ, (Work.EQ.germC a h (Yinv y)).1 = φ y) ∧
      (∀ u, u ∈ Metric.ball (0 : ℂ) ρ → Yinv ((Work.EQ.germC a h u).2) = u) := by
  -- The `y`-coordinate of the germ, and the basic facts about it near `0`.
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
  -- `Y` is a local biholomorphism at `0`; `Yinv` is its analytic local inverse.
  let Yinv : ℂ → ℂ := HasStrictDerivAt.localInverse Y (deriv Y 0) 0 hYan.hasStrictDerivAt hf'
  have hYinv_an : AnalyticAt ℂ Yinv 0 := by
    have h := hYan.analyticAt_localInverse hf'
    rwa [hY0] at h
  have hYinv0 : Yinv 0 = 0 := by
    have h := (hYan.hasStrictDerivAt.eventually_left_inverse hf').self_of_nhds
    rwa [hY0] at h
  -- Both inverse identities, near `0` (they become ball statements after shrinking `ρ`).
  have hright : ∀ᶠ y in 𝓝 (0 : ℂ), Y (Yinv y) = y := by
    have h := hYan.hasStrictDerivAt.eventually_right_inverse hf'
    rwa [hY0] at h
  have hleft : ∀ᶠ u in 𝓝 (0 : ℂ), Yinv (Y u) = u :=
    hYan.hasStrictDerivAt.eventually_left_inverse hf'
  -- The germ curve as a function of `y` and its `x`-coordinate `φ`.
  let Z : ℂ → ℂ × ℂ := fun y => germC a h (Yinv y)
  have hZan : AnalyticAt ℂ Z 0 := by
    have hg : AnalyticAt ℂ (germC a h) (Yinv 0) := by
      rw [hYinv0]; exact hAnC 0 (by simp [hρ₀pos])
    have h1 := AnalyticAt.comp hg hYinv_an
    simpa [Z, Function.comp_def] using h1
  let φ : ℂ → ℂ := fun y => (Z y).1
  have hφan : AnalyticAt ℂ φ 0 := by
    have hp : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) (Z 0) :=
      (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _
    have h1 := AnalyticAt.comp hp hZan
    simpa [φ, Z, Function.comp_def] using h1
  -- A common radius on which all the clauses hold.
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := hYinv_an.exists_ball_analyticOnNhd
  obtain ⟨ρ₂, hρ₂pos, hρ₂⟩ := exists_ball_of_eventually hright
  obtain ⟨ρ₃, hρ₃pos, hρ₃⟩ := exists_ball_of_eventually hleft
  obtain ⟨ρ₄, hρ₄pos, hρ₄⟩ := hφan.exists_ball_analyticOnNhd
  set ρ : ℝ := min ρ₁ (min ρ₂ (min ρ₃ ρ₄)) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; exact lt_min hρ₁pos (lt_min hρ₂pos (lt_min hρ₃pos hρ₄pos))
  have hρle₁ : ρ ≤ ρ₁ := by rw [hρdef]; exact min_le_left _ _
  have hρle₂ : ρ ≤ ρ₂ := by rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρle₃ : ρ ≤ ρ₃ := by
    rw [hρdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρle₄ : ρ ≤ ρ₄ := by
    rw [hρdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨ρ, hρpos, φ, Yinv, ?_, ?_, ?_, ?_, ?_⟩
  · exact hρ₄.mono (Metric.ball_subset_ball hρle₄)
  · exact hρ₁.mono (Metric.ball_subset_ball hρle₁)
  · intro y hy
    have hy' : y ∈ Metric.ball (0 : ℂ) ρ₂ := Metric.ball_subset_ball hρle₂ hy
    simpa [Y] using hρ₂ y hy'
  · intro y hy
    simp [φ, Z]
  · intro u hu
    have hu' : u ∈ Metric.ball (0 : ℂ) ρ₃ := Metric.ball_subset_ball hρle₃ hu
    simpa [Y] using hρ₃ u hu'

end

end Work.EQ
