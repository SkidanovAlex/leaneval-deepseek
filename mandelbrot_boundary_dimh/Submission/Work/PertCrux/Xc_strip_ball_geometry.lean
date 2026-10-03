import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Parab.Setup

/-!
# `Work.PertCrux.Xc_strip_ball_geometry`

**The statement.**  For a parabolic datum `d` (whose only feature used here is `0 < d.ξ₀`) and
any `R : ℝ` there is `M₁ > 0` such that for every `M ≥ M₁`, every width `T ∈ [0, M]`, every
`r ∈ [0, M/16]`, every point `u` of the deep strip `Dstrip M T = {-M-1 ≤ Re ≤ -M, |Im| ≤ T}`
and every `z` with `‖z - u‖ ≤ r`:

* `z ∈ QLeft ξ₀`,  `ball z (‖z‖/10) ⊆ QLeft ξ₀`,  and  `R ≤ ‖z‖`.

**Why it is true (and elementary).**  `MandelDim.QLeft ξ = {w | π/3 < |arg (w+ξ)|}` contains the
whole left half-plane `{Re w < -ξ}` (`Work.Parab.halfplane_subset_QLeft`), so it is enough to show
that every point of the ball `ball z (‖z‖/10)` has real part `< -ξ₀`.  Now

`Re z ≤ -M + r ≤ -15M/16`  and  `‖z‖ ≤ ‖u‖ + r ≤ (M+1) + M + M/16 ≤ 33M/16 + 1`,

using `‖u‖ ≤ |Re u| + |Im u| ≤ (M+1) + T ≤ (M+1) + M`; hence for `w` in the ball

`Re w ≤ Re z + ‖w - z‖ < Re z + ‖z‖/10 ≤ -15M/16 + 33M/160 + 1/10 = -117M/160 + 1/10 < -ξ₀`,

the last inequality being exactly `M > 2(ξ₀+1)` (no other property of `d` is used).  Finally
`‖z‖ ≥ |Re z| ≥ 15M/16 ≥ R` as soon as `M ≥ 16R/15 + 1`.

So the whole content is a quantitative estimate on the real parts; the constant chosen below is
`M₁ = max 3 (max (2(ξ₀+1)) (16R/15+1))`.
-/

namespace Work.PertCrux

open Complex Set Metric

noncomputable section

/-- Elementary bound: `‖w‖ ≤ |Re w| + |Im w|` (the `ℓ¹` bound for the complex modulus). -/
lemma norm_le_abs_re_add_abs_im (w : ℂ) : ‖w‖ ≤ |w.re| + |w.im| := by
  calc ‖w‖ = ‖(w.re : ℂ) + (w.im : ℂ) * Complex.I‖ :=
        congrArg norm ((Complex.re_add_im w).symm)
    _ ≤ ‖(w.re : ℂ)‖ + ‖(w.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |w.re| + |w.im| := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_real, Real.norm_eq_abs]

theorem Xc_strip_ball_geometry {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (R : ℝ) :
    ∃ M₁ : ℝ, 0 < M₁ ∧ ∀ M : ℝ, M₁ ≤ M → ∀ T : ℝ, 0 ≤ T → T ≤ M → ∀ r : ℝ, 0 ≤ r →
      r ≤ M / 16 → ∀ u : ℂ, u ∈ Work.Pert.Dstrip M T → ∀ z : ℂ, ‖z - u‖ ≤ r →
        z ∈ MandelDim.QLeft d.ξ₀ ∧ Metric.ball z (‖z‖ / 10) ⊆ MandelDim.QLeft d.ξ₀ ∧
          R ≤ ‖z‖ := by
  refine ⟨max 3 (max (2 * (d.ξ₀ + 1)) (16 * R / 15 + 1)),
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) (le_max_left _ _), ?_⟩
  intro M hM T hT0 hTM r hr0 hrM u hu z hz
  have hM3 : 3 ≤ M := le_trans (le_max_left _ _) hM
  have hMa : 2 * (d.ξ₀ + 1) ≤ M :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have hMb : 16 * R / 15 + 1 ≤ M :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  obtain ⟨hu1, hu2, hu3⟩ := hu
  have hM0 : 0 < M := by linarith
  have huim : |u.im| ≤ M := le_trans hu3 hTM
  -- `‖u‖ ≤ 2M + 1` from the strip bounds
  have hnormu : ‖u‖ ≤ 2 * M + 1 := by
    have h1 : |u.re| ≤ M + 1 := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    calc ‖u‖ ≤ |u.re| + |u.im| := norm_le_abs_re_add_abs_im u
      _ ≤ (M + 1) + M := add_le_add h1 huim
      _ = 2 * M + 1 := by ring
  -- `Re z ≤ -15M/16`
  have hrz : z.re ≤ -15 * M / 16 := by
    have h1 : |(z - u).re| ≤ ‖z - u‖ := Complex.abs_re_le_norm _
    have h2 : (z - u).re = z.re - u.re := by simp
    have h3 : ‖z - u‖ ≤ M / 16 := le_trans hz hrM
    rw [h2] at h1
    have h4 := (abs_le.mp h1).2
    linarith
  -- `‖z‖ ≤ 33M/16 + 1`
  have hnormz : ‖z‖ ≤ 33 * M / 16 + 1 := by
    have h4 : ‖z - u‖ ≤ M / 16 := le_trans hz hrM
    have hzu : z = u + (z - u) := by ring
    calc ‖z‖ = ‖u + (z - u)‖ := congrArg norm hzu
      _ ≤ ‖u‖ + ‖z - u‖ := norm_add_le _ _
      _ ≤ (2 * M + 1) + M / 16 := add_le_add hnormu h4
      _ = 33 * M / 16 + 1 := by ring
  have hnormzpos : 0 < ‖z‖ := by
    have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have h2 : |z.re| = -z.re := abs_of_nonpos (by linarith)
    linarith
  -- the real-part estimate that puts the whole `‖z‖/10`-ball in the left half-plane
  have hkey : z.re + ‖z‖ / 10 < -d.ξ₀ := by
    have h1 : ‖z‖ / 10 ≤ 33 * M / 160 + 1 / 10 := by linarith
    have h2 : d.ξ₀ + 1 / 10 < 117 * M / 160 := by
      have := d.ξ₀_pos
      linarith
    linarith
  have hballsub : Metric.ball z (‖z‖ / 10) ⊆ MandelDim.QLeft d.ξ₀ := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    refine Work.Parab.halfplane_subset_QLeft d.ξ₀ ?_
    change w.re < -d.ξ₀
    have h1 : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm _
    have h2 : (w - z).re = w.re - z.re := by simp
    rw [h2] at h1
    have h3 := (abs_le.mp h1).2
    linarith
  refine ⟨?_, hballsub, ?_⟩
  · have hzball : z ∈ Metric.ball z (‖z‖ / 10) := by
      rw [Metric.mem_ball, dist_self]; linarith
    exact hballsub hzball
  · have h4 : 15 * M / 16 ≤ ‖z‖ := by
      have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      have h2 : |z.re| = -z.re := abs_of_nonpos (by linarith)
      linarith
    linarith

end

end Work.PertCrux
