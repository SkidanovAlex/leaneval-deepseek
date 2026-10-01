import Mathlib
import Submission.Work.LinnikAreas.A5.Weights
import Submission.Work.LinnikAreas.A5.f1_data
import Submission.Work.LinnikAreas.A5.Basic
import Submission.Work.LinnikAreas.A5.wc_tanh_bound
import Submission.Work.LinnikAreas.A5.wc_bounds
import Submission.Work.LinnikAreas.A5.wc_contDiffOn_iteratedDeriv
import Submission.Work.LinnikAreas.A5.wc_deriv_Ioo
import Submission.Work.LinnikAreas.A5.wc_deriv_corners

open Filter
open scoped Topology

namespace Work.LinnikAreas.A5

/-
Data for the normalised HB-13.3 test function `wc K lam` (λ > 0 case) used in Area 5:
`wc K lam t = (sinh (K*lam))⁻¹ * f1 K lam t` for `t ≥ 0` and `0` for `t < 0`
(`f1 K lam t = sinh((K-t)*lam)` on `t ≤ K`, `0` for `t ≥ K`, so `wc` is supported in `[0,K]`).

This is exactly the "Condition 1" data needed by HB's smoothing estimate (§5) with x₀ = K and
B = R², plus the extra global bound `‖wc‖ ≤ 1` on all of ℝ and the derivative bound on `[0,K]`
needed by the Lambert/von-Mangoldt partial-summation input.

Proof notes: on `t ∈ (0,K)` the function equals the smooth branch `sinh((K-t)λ)/sinh(Kλ)`, so
C²-ness and the second-derivative bound `λ² ≤ R²` come from `f1_data`; `wc 0 = 1` is
`f1_zero`; the global bound is `sinh((K-t)λ) ≤ sinh(Kλ)` for `t ∈ [0,K]` (and `0` elsewhere);
`deriv wc t = -λ cosh((K-t)λ)/sinh(Kλ)` on `(0,K)`, bounded by `λ/tanh(Kλ) ≤ 1/K + λ ≤ 1/K + R`
(using `tanh x ≥ x/(1+x)`, from `Real.add_one_le_exp`), while at the corners `t = 0` and `t = K`
`wc` is *not* differentiable (one-sided slopes differ), so `deriv` takes its convention value `0`
there — the same argument as the existing `Work.LinnikAreas.A5.f1_deriv_at_K`
(`hasDerivAt_iff_tendsto_slope_left_right` + `deriv_zero_of_not_differentiableAt`).
-/
theorem wc_data (K lam R : ℝ) (hK : 0 < K) (hlam : 0 < lam) (hlamR : lam ≤ R) :
    Work.LinnikAreas.A5.wc K lam 0 = 1 ∧
    ContinuousOn (Work.LinnikAreas.A5.wc K lam) (Set.Ici 0) ∧
    (∀ t : ℝ, K ≤ t → Work.LinnikAreas.A5.wc K lam t = 0) ∧
    ContDiffOn ℝ 2 (Work.LinnikAreas.A5.wc K lam) (Set.Ioo 0 K) ∧
    (∀ t ∈ Set.Ioo (0:ℝ) K, ‖iteratedDeriv 2 (Work.LinnikAreas.A5.wc K lam) t‖ ≤ R ^ 2) ∧
    (∀ t : ℝ, ‖Work.LinnikAreas.A5.wc K lam t‖ ≤ 1) ∧
    (∀ t ∈ Set.Icc (0:ℝ) K, ‖deriv (Work.LinnikAreas.A5.wc K lam) t‖ ≤ 1 / K + R) ∧
    (∀ t : ℝ, 0 ≤ Work.LinnikAreas.A5.wc K lam t) := by
  -- positivity of the normalising denominator and of `1/K`
  have hs : (0:ℝ) < Real.sinh (K * lam) := Real.sinh_pos_iff.mpr (mul_pos hK hlam)
  have h1K : (0:ℝ) < 1 / K := one_div_pos.mpr hK
  have hR : (0:ℝ) < R := lt_of_lt_of_le hlam hlamR
  -- the five imported components
  obtain ⟨hcorn0, hcornK⟩ := wc_deriv_corners K lam hK hlam
  obtain ⟨hbnd, hnn⟩ := wc_bounds K lam hK hlam
  obtain ⟨hcd, hd2, _hd2form⟩ := wc_contDiffOn_iteratedDeriv K lam hK hlam
  refine ⟨?_, ?_, ?_, hcd, ?_, hbnd, ?_, hnn⟩
  · -- `wc K lam 0 = (sinh (Kλ))⁻¹ · sinh (Kλ) = 1`
    rw [wc_of_nonneg le_rfl, f1_zero hK.le]
    exact inv_mul_cancel₀ (ne_of_gt hs)
  · -- on `[0,∞)` the cutoff is inactive, so `wc` is a constant multiple of the continuous `f1`
    exact ((continuous_f1 K lam).const_mul ((Real.sinh (K * lam))⁻¹)).continuousOn.congr
      (fun t ht => wc_of_nonneg ht)
  · -- `wc` vanishes beyond `K`
    intro t ht
    rw [wc_of_nonneg (le_trans hK.le ht), f1_of_ge ht, mul_zero]
  · -- `|wc''| ≤ λ² ≤ R²` on `(0,K)`
    intro t ht
    have hle : lam ^ 2 ≤ R ^ 2 := by nlinarith
    linarith [hd2 t ht]
  · -- the derivative bound on `[0,K]`
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0, hcorn0, norm_zero]; linarith
    · rcases eq_or_lt_of_le ht.2 with hK' | hK'
      · rw [hK', hcornK, norm_zero]; linarith
      · -- interior point: exact derivative, then `λ coth (Kλ) ≤ 1/K + λ ≤ 1/K + R`
        rw [wc_deriv_Ioo K lam ⟨h0, hK'⟩]
        have hnorm : ‖-lam * Real.cosh ((K - t) * lam) / Real.sinh (K * lam)‖
            = lam * Real.cosh ((K - t) * lam) / Real.sinh (K * lam) := by
          rw [Real.norm_eq_abs, abs_div, abs_of_pos hs, abs_mul, abs_neg, abs_of_pos hlam,
              abs_of_pos (Real.cosh_pos _)]
        rw [hnorm]
        have hcosh : Real.cosh ((K - t) * lam) ≤ Real.cosh (K * lam) := by
          rw [Real.cosh_le_cosh,
              abs_of_nonneg (mul_nonneg (by linarith) hlam.le),
              abs_of_nonneg (mul_nonneg hK.le hlam.le)]
          exact mul_le_mul_of_nonneg_right (by linarith) hlam.le
        have h2 : lam * Real.cosh ((K - t) * lam) / Real.sinh (K * lam)
            ≤ lam * Real.cosh (K * lam) / Real.sinh (K * lam) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcosh hlam.le) hs.le
        linarith [wc_tanh_bound K lam hK hlam, h2]

end Work.LinnikAreas.A5
