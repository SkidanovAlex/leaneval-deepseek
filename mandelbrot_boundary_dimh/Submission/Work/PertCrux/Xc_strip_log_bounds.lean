import Mathlib
import Submission.Work.Pert.Ksub2.Xcurve_bounds
import Submission.Work.Pert.Ksub2.Setup

namespace Work.PertCrux

open Complex Metric

/-!
# `Work.PertCrux.Xc_strip_log_bounds`

`Xc d u = τ₀ (φ₀ u)` is the datum's curve of a §4.1-datum `d` for a parabolic germ.  On the deep
horizontal strip `Dstrip M T = {-M-1 ≤ Re u ≤ -M, |Im u| ≤ T}` (with the *weak* width hypothesis
`T ≤ M`, not the `T ≤ M/160` of `Xc_sharp_on_strip`) the curve is close to the identity at the
logarithmic scale, and its total variation over the strip (measured from the real anchor `-M`) is
`O(1 + T + log M)`.

The proof is the one of `Work.Pert.Ksub2.Xc_sharp_on_strip`, rerun with the weaker width bound: on
the strip `M ≤ ‖u‖ ≤ M + 1 + T ≤ 3M`, and the whole `‖u‖/10`-ball of a strip point lies in the
left half plane `{Re w < -ξ₀} ⊆ QLeft ξ₀`, so `Xcurve_bounds` (the two-term asymptotic of the Fatou
coordinate plus Cauchy's estimate) applies.  Then `1 + log ‖u‖ ≤ (1 + log 3)(1 + log M)`, and the
difference to the anchor `-M` follows by the triangle inequality across
`(Xc u - u) + (u + M) + (-M - Xc (-M))` with `‖u + M‖ ≤ 1 + T`.
-/

/-- The logarithmic bound on the deep strip, with the weak width hypothesis `T ≤ M`. -/
theorem strip_log_bound_aux {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ C M₀ : ℝ, 0 < C ∧ 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → ∀ T : ℝ, 0 ≤ T → T ≤ M →
      ∀ u ∈ Work.Pert.Dstrip M T, ‖Work.Pert.Xc d u - u‖ ≤ C * (1 + Real.log M) := by
  obtain ⟨C, hCpos, hXcur⟩ := Work.Pert.Ksub2.Xcurve_bounds d
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨C * (1 + Real.log 3), max 1 (max (C + 1) (2 * d.ξ₀ + 1)),
    mul_pos hCpos (by linarith), ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_left _ _)
  · intro M hM T hT0 hTM u hu
    have hM1 : 1 ≤ M := le_trans (le_max_left _ _) hM
    have hMC : C + 1 ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
    have hMξ : 2 * d.ξ₀ + 1 ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
    have hMpos : 0 < M := by linarith
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
    have hre1 : -M - 1 ≤ u.re := hu.1
    have hre2 : u.re ≤ -M := hu.2.1
    have him : |u.im| ≤ T := hu.2.2
    have hnorm_ge : M ≤ ‖u‖ := by
      have h1 := Complex.abs_re_le_norm u
      have h2 : |u.re| = -u.re := abs_of_nonpos (by linarith)
      linarith
    have hnorm_le : ‖u‖ ≤ 3 * M := by
      have h1 := Complex.norm_le_abs_re_add_abs_im u
      have h2 : |u.re| ≤ M + 1 := by
        apply abs_le.mpr; constructor <;> linarith
      have h3 : |u.im| ≤ M := le_trans him hTM
      linarith
    have huQ : u ∈ MandelDim.QLeft d.ξ₀ :=
      Work.Parab.halfplane_subset_QLeft d.ξ₀ (by linarith [d.ξ₀_pos] : u.re < -d.ξ₀)
    have hballQ : Metric.ball u (‖u‖ / 10) ⊆ MandelDim.QLeft d.ξ₀ := by
      intro w hw
      refine Work.Parab.halfplane_subset_QLeft d.ξ₀ (show w.re < -d.ξ₀ from ?_)
      have h1 : ‖w - u‖ < ‖u‖ / 10 := by
        have h := Metric.mem_ball.mp hw
        rwa [dist_eq_norm] at h
      have h2 : w.re - u.re ≤ ‖w - u‖ := by
        have h := Complex.abs_re_le_norm (w - u)
        rw [Complex.sub_re] at h
        exact (abs_le.mp h).2
      have h4 : ‖u‖ / 10 ≤ 3 * M / 10 := by linarith
      linarith [h1, h2, h4, hre2, hMξ, d.ξ₀_pos]
    have hC_le : C ≤ ‖u‖ := by linarith
    obtain ⟨hval, -⟩ := hXcur u huQ hC_le hballQ
    have hlogkey : 1 + Real.log ‖u‖ ≤ (1 + Real.log 3) * (1 + Real.log M) := by
      have h3M : Real.log ‖u‖ ≤ Real.log (3 * M) :=
        Real.log_le_log (by linarith) hnorm_le
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hMpos)] at h3M
      nlinarith [h3M, hlogM, hlog3]
    calc ‖Work.Pert.Xc d u - u‖ ≤ C * (1 + Real.log ‖u‖) := hval
      _ ≤ C * ((1 + Real.log 3) * (1 + Real.log M)) :=
            mul_le_mul_of_nonneg_left hlogkey hCpos.le
      _ = (C * (1 + Real.log 3)) * (1 + Real.log M) := by ring

theorem Xc_strip_log_bounds {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ C M₀ : ℝ, 0 < C ∧ 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → ∀ T : ℝ, 0 ≤ T → T ≤ M →
      ∀ u ∈ Work.Pert.Dstrip M T,
        ‖Work.Pert.Xc d u - u‖ ≤ C * (1 + Real.log M) ∧
        ‖Work.Pert.Xc d u - Work.Pert.Xc d (((-M : ℝ)) : ℂ)‖ ≤ C * (1 + T + Real.log M) := by
  obtain ⟨C, M₀, hCpos, hM₀pos, hbound⟩ := strip_log_bound_aux d
  refine ⟨2 * C + 1, max M₀ 1, by linarith, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro M hM T hT0 hTM u hu
  have hM₀ : M₀ ≤ M := le_trans (le_max_left _ _) hM
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hbU : ‖Work.Pert.Xc d u - u‖ ≤ C * (1 + Real.log M) :=
    hbound M hM₀ T hT0 hTM u hu
  have hbA : ‖Work.Pert.Xc d (((-M : ℝ)) : ℂ) - (((-M : ℝ)) : ℂ)‖
      ≤ C * (1 + Real.log M) := by
    refine hbound M hM₀ T hT0 hTM _ ?_
    simp only [Work.Pert.Dstrip, Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im,
      abs_zero]
    exact ⟨by linarith, le_refl _, hT0⟩
  refine ⟨?_, ?_⟩
  · exact le_trans hbU
      (mul_le_mul_of_nonneg_right (by linarith [hCpos]) (by linarith))
  · -- the difference to the anchor `-M` through the point `u`
    have hgeom : ‖u - (((-M : ℝ)) : ℂ)‖ ≤ 1 + T := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (u - (((-M : ℝ)) : ℂ))
      have h2 : (u - (((-M : ℝ)) : ℂ)).re = u.re + M := by simp
      have h3 : (u - (((-M : ℝ)) : ℂ)).im = u.im := by simp
      rw [h2, h3] at h1
      have h4 : |u.re + M| ≤ 1 := by
        apply abs_le.mpr; constructor <;> linarith [hu.1, hu.2.1]
      linarith [h1, h4, hu.2.2]
    have hsplit : Work.Pert.Xc d u - Work.Pert.Xc d (((-M : ℝ)) : ℂ) =
        (Work.Pert.Xc d u - u) + (u - (((-M : ℝ)) : ℂ)) +
          (((((-M : ℝ)) : ℂ)) - Work.Pert.Xc d (((-M : ℝ)) : ℂ)) := by ring
    rw [hsplit]
    have ha := norm_add_le
      ((Work.Pert.Xc d u - u) + (u - (((-M : ℝ)) : ℂ)))
      (((((-M : ℝ)) : ℂ)) - Work.Pert.Xc d (((-M : ℝ)) : ℂ))
    have hb := norm_add_le (Work.Pert.Xc d u - u) (u - (((-M : ℝ)) : ℂ))
    have hc : ‖((((-M : ℝ)) : ℂ)) - Work.Pert.Xc d (((-M : ℝ)) : ℂ)‖
        = ‖Work.Pert.Xc d (((-M : ℝ)) : ℂ) - (((-M : ℝ)) : ℂ)‖ := norm_sub_rev _ _
    rw [hc] at ha
    have hfinal : ‖(Work.Pert.Xc d u - u) + (u - (((-M : ℝ)) : ℂ)) +
        (((((-M : ℝ)) : ℂ)) - Work.Pert.Xc d (((-M : ℝ)) : ℂ))‖
        ≤ C * (1 + Real.log M) + (1 + T) + C * (1 + Real.log M) := by
      linarith [ha, hb, hbU, hgeom, hbA]
    have harith : C * (1 + Real.log M) + (1 + T) + C * (1 + Real.log M)
        ≤ (2 * C + 1) * (1 + T + Real.log M) := by
      nlinarith [hCpos, hT0, hlogM]
    linarith [hfinal, harith]

end Work.PertCrux
