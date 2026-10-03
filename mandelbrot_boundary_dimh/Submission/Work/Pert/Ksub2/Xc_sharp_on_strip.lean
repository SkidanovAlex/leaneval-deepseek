import Mathlib
import Submission.Work.Pert.Ksub2.Xcurve_bounds
import Submission.Work.Pert.Ksub2.Setup

/-!
# `Work.Pert.Ksub2.Xc_sharp_on_strip`

The curve `u ↦ Xc d u = τ₀ (φ₀ u)` of a `§4.1`-datum `d` is close to the identity on the deep
strip `Dstrip M T = {-M-1 ≤ Re u ≤ -M, |Im u| ≤ T}` at the *logarithmic* scale: there is `C > 0`,
depending only on `d`, such that for all large `M` and all `T ≤ M/160`

* `‖Xc d (-M) + M‖ ≤ C (1 + log M)`, and
* `‖Xc d u - u‖ ≤ C (1 + log M)` for every `u` in the strip.

This sharpens `Xc_bounds_on_strip` (which gives the *linear* bound `M/320`) to the logarithmic scale
that `Xcurve_bounds` supplies: there, on deep points `u ∈ QLeft ξ₀` whose `‖u‖/10`-ball stays in the
sector, `‖Xc d u - u‖ ≤ C (1 + log ‖u‖)`.  On the strip `M ≤ ‖u‖ ≤ M + 1 + T ≤ 2M` and the whole
`‖u‖/10`-ball stays well inside the left half-plane `{Re w < -ξ₀}` (hence in `QLeft ξ₀`), so the
sector estimate applies; finally `1 + log ‖u‖ ≤ 1 + log (2M) = 1 + log 2 + log M ≤
(1 + log 2)(1 + log M)` for `M ≥ 1`.
-/

namespace Work.Pert.Ksub2

open Complex Metric

theorem Xc_sharp_on_strip {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → ∀ T : ℝ, T ≤ M / 160 →
      ‖Work.Pert.Xc d (((-M : ℝ) : ℂ)) - (((-M : ℝ) : ℂ))‖ ≤ C * (1 + Real.log M) ∧
      (∀ u ∈ Work.Pert.Dstrip M T, ‖Work.Pert.Xc d u - u‖ ≤ C * (1 + Real.log M)) := by
  obtain ⟨C, hCpos, hXcur⟩ := Xcurve_bounds d
  set C' : ℝ := max 1 (C * (1 + Real.log 2)) with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hCClog : C * (1 + Real.log 2) ≤ C' := le_max_right _ _
  refine ⟨C', hC'pos, C + 400 * (d.ξ₀ + 1) + 400, by linarith [d.ξ₀_pos, hCpos], ?_⟩
  intro M hM T hT
  have hξ0 : 0 < d.ξ₀ := d.ξ₀_pos
  have hMbig : 400 * (d.ξ₀ + 1) + 400 ≤ M := by linarith
  have hMC : C ≤ M := by linarith
  have hM400 : 400 ≤ M := by linarith
  have hMpos : 0 < M := by linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  -- the uniform bound on any deep strip point
  have hbound : ∀ T' : ℝ, T' ≤ M / 160 → ∀ u ∈ Work.Pert.Dstrip M T',
      ‖Work.Pert.Xc d u - u‖ ≤ C' * (1 + Real.log M) := by
    intro T' hT' u hu
    have hre_lb : -M - 1 ≤ u.re := hu.1
    have hre_ub : u.re ≤ -M := hu.2.1
    have him : |u.im| ≤ T' := hu.2.2
    have huQ : u ∈ MandelDim.QLeft d.ξ₀ :=
      Work.Parab.halfplane_subset_QLeft d.ξ₀ (by linarith : u.re < -d.ξ₀)
    have hu_norm_ge : M ≤ ‖u‖ := by
      have h1 : |u.re| ≤ ‖u‖ := Complex.abs_re_le_norm u
      have h2 : |u.re| = -u.re := abs_of_nonpos (by linarith)
      linarith
    have hu_norm_le : ‖u‖ ≤ 2 * M := by
      have h1 : ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
      have h2 : |u.re| ≤ M + 1 := by
        apply abs_le.mpr; constructor <;> linarith
      have h3 : |u.im| ≤ M / 160 := le_trans him hT'
      linarith
    have hballQ : Metric.ball u (‖u‖ / 10) ⊆ MandelDim.QLeft d.ξ₀ := by
      intro w hw
      refine Work.Parab.halfplane_subset_QLeft d.ξ₀ ?_
      show w.re < -d.ξ₀
      have h1 : dist w u < ‖u‖ / 10 := Metric.mem_ball.mp hw
      rw [dist_eq_norm] at h1
      have h2 : w.re - u.re ≤ ‖w - u‖ := by
        have h := Complex.abs_re_le_norm (w - u)
        rw [Complex.sub_re] at h
        exact (abs_le.mp h).2
      have h3 : w.re < -M + ‖u‖ / 10 := by linarith
      have h4 : ‖u‖ / 10 ≤ M / 5 := by linarith
      have h5 : d.ξ₀ < 4 * M / 5 := by
        have h5a : d.ξ₀ ≤ M / 5 := by linarith [hMbig, d.ξ₀_pos]
        linarith
      linarith
    obtain ⟨hv, _⟩ := hXcur u huQ (by linarith) hballQ
    -- replace `log ‖u‖` by `log M`
    have hlog_le : Real.log ‖u‖ ≤ Real.log (2 * M) :=
      Real.log_le_log (by linarith) hu_norm_le
    have h2M : Real.log (2 * M) = Real.log 2 + Real.log M :=
      Real.log_mul (by norm_num) (ne_of_gt hMpos)
    have hkey : 1 + Real.log ‖u‖ ≤ (1 + Real.log 2) * (1 + Real.log M) := by
      rw [h2M] at hlog_le
      nlinarith [hlog_le, hlogM, hlog2]
    calc ‖Work.Pert.Xc d u - u‖ ≤ C * (1 + Real.log ‖u‖) := hv
      _ ≤ C * ((1 + Real.log 2) * (1 + Real.log M)) :=
            mul_le_mul_of_nonneg_left hkey hCpos.le
      _ = (C * (1 + Real.log 2)) * (1 + Real.log M) := by ring
      _ ≤ C' * (1 + Real.log M) := mul_le_mul_of_nonneg_right hCClog (by linarith)
  constructor
  · -- the sharp bound at the real point `-M` (a point of `Dstrip M 0`)
    have hmem : (((-M : ℝ)) : ℂ) ∈ Work.Pert.Dstrip M 0 := by
      simp only [Work.Pert.Dstrip, Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im,
        abs_zero]
      exact ⟨by linarith, by linarith, le_refl 0⟩
    exact hbound 0 (by linarith) _ hmem
  · exact fun u hu => hbound T hT u hu

end Work.Pert.Ksub2
