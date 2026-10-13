/-
# `Work.FTS.Regularity.chiModuli` — the moduli of the cut-off `χ`

The team's cut-off `Work.Stability.chi` is the explicit bump
`chi x = Real.smoothTransition (2 - ‖x‖)` of `Submission.Work.Stability.Cutoff`: it is `C^∞`,
`0 ≤ chi ≤ 1`, equals `1` on `[-1,1]` and vanishes off `(-2,2)`.

This module records the **quantitative moduli** of that cut-off — the six data points of
`chiModuli`:

* `chi` is bounded (`|χ| ≤ 1`), uniformly Lipschitz;
* `χ'` and `χ''` are bounded, and `χ'` is uniformly Lipschitz.

These are exactly the moduli consumed by the transfer/regularity chapter
(`Work.FTS.Regularity`): the cut-off is applied to the profile at scale `L` (`chi (z/L)`,
`Work.Stability.zcut`) and the bounds above are what make every cut term, its `z`-derivative and
the `τ`-derivative of the truncated profile bounded and Lipschitz *uniformly* in the parameters.

## Proof

Everything rests on one soft fact and one compactness fact.

*Soft fact.* `χ` is locally constant (`≡ 1` on `(-1,1)`, `≡ 0` off `(-2,2)`), so `χ'` vanishes
strictly outside `[-2,2]` — at such a point `χ` is *eventually equal* to the constant `0`, so the
derivative is `0` (`Filter.EventuallyEq.deriv_eq`); likewise `χ''` vanishes there, since `χ'`
itself is eventually `0` near every point outside `[-2,2]`.  Note that there is no need for
Fermat's rule at the boundary points `±2`: the compactness argument below only needs vanishing
*strictly* outside.

*Compactness.* On the compact interval `[-2,2]` the continuous functions `χ'` and `χ''` are
bounded (`IsCompact.exists_bound_of_continuousOn`), and outside it they vanish, so a single
constant `C = max M₁ (max M₂ 1)` bounds both `χ'` and `χ''` on all of `ℝ` — and, being `≥ 1`,
also bounds `|χ| ≤ 1`.

The Lipschitz clauses are then the mean value theorem in dimension one
(`Convex.norm_image_sub_le_of_norm_deriv_le`, `s = univ`): a differentiable function whose
derivative is bounded by `C` is `C`-Lipschitz.  Applied to `χ` it gives the Lipschitz clause of
`χ` (bounded first derivative), applied to `χ'` it gives the Lipschitz clause of `χ'` (bounded
second derivative).
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped ContDiff Topology
open Set Filter

set_option autoImplicit false

namespace Work.FTS.Regularity

/-! ## The cut-off is flat off `[-2,2]` -/

/-- **`χ' = 0` strictly outside `[-2,2]`.**  For `2 < |t|` the cut-off vanishes on a whole
neighbourhood of `t` (`chi_eq_zero`), so its derivative there is the derivative of a constant. -/
theorem chi_deriv_eq_zero_of_two_lt_abs {t : ℝ} (ht : 2 < |t|) :
    deriv Work.Stability.chi t = 0 := by
  have hev : Work.Stability.chi =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    rcases lt_abs.mp ht with h | h
    · filter_upwards [Ioi_mem_nhds h] with y (hy : 2 < y)
      exact Work.Stability.chi_eq_zero (by
        rw [abs_of_pos (by linarith : (0 : ℝ) < y)]; linarith)
    · have ht2 : t < -2 := by linarith
      filter_upwards [Iio_mem_nhds ht2] with y (hy : y < -2)
      exact Work.Stability.chi_eq_zero (by
        rw [abs_of_neg (by linarith : y < 0)]; linarith)
  rw [hev.deriv_eq, deriv_const]

/-- **`χ'' = 0` strictly outside `[-2,2]`.**  For `2 < |t|` the derivative `χ'` vanishes on a whole
neighbourhood of `t` (the previous lemma), so the second derivative there is `0`. -/
theorem chi_deriv2_eq_zero_of_two_lt_abs {t : ℝ} (ht : 2 < |t|) :
    deriv (deriv Work.Stability.chi) t = 0 := by
  have hev : deriv Work.Stability.chi =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    rcases lt_abs.mp ht with h | h
    · filter_upwards [Ioi_mem_nhds h] with y (hy : 2 < y)
      exact chi_deriv_eq_zero_of_two_lt_abs (by
        rw [abs_of_pos (by linarith : (0 : ℝ) < y)]; linarith)
    · have ht2 : t < -2 := by linarith
      filter_upwards [Iio_mem_nhds ht2] with y (hy : y < -2)
      exact chi_deriv_eq_zero_of_two_lt_abs (by
        rw [abs_of_neg (by linarith : y < 0)]; linarith)
  rw [hev.deriv_eq, deriv_const]

/-- **A universal bound for `χ'` and `χ''`.**  Both are continuous and vanish off the compact
interval `[-2,2]`, so both are bounded there by compactness.  The constant produced is `≥ 1`, so it
also bounds `|χ|` (which lies in `[0,1]`). -/
theorem chi_deriv_bounds :
    ∃ C : ℝ, 0 < C ∧
      (∀ t : ℝ, |Work.Stability.chi t| ≤ C) ∧
      (∀ t : ℝ, |deriv Work.Stability.chi t| ≤ C) ∧
      (∀ t : ℝ, |deriv (deriv Work.Stability.chi) t| ≤ C) := by
  have hcd : ContDiff ℝ ∞ Work.Stability.chi := Work.Stability.chi_contDiff
  have hd1 : ContDiff ℝ ∞ (deriv Work.Stability.chi) := contDiff_infty_iff_deriv.mp hcd |>.2
  have hd2 : ContDiff ℝ ∞ (deriv (deriv Work.Stability.chi)) :=
    contDiff_infty_iff_deriv.mp hd1 |>.2
  have hc1 : Continuous (deriv Work.Stability.chi) := hd1.continuous
  have hc2 : Continuous (deriv (deriv Work.Stability.chi)) := hd2.continuous
  -- a point outside the closed interval `[-2,2]` is `> 2` in absolute value
  have hout : ∀ t : ℝ, t ∉ Set.Icc (-2) 2 → 2 < |t| := by
    intro t ht
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨M1, hM1⟩ :=
    (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨M2, hM2⟩ :=
    (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn hc2.continuousOn
  have hC1 : M1 ≤ max M1 (max M2 1) := le_max_left _ _
  have hC2 : M2 ≤ max M1 (max M2 1) := le_trans (le_max_left M2 1) (le_max_right M1 _)
  have hone : (1 : ℝ) ≤ max M1 (max M2 1) := le_trans (le_max_right M2 1) (le_max_right M1 _)
  refine ⟨max M1 (max M2 1), lt_of_lt_of_le zero_lt_one hone, ?_, ?_, ?_⟩
  · intro t
    rw [abs_of_nonneg (Work.Stability.chi_nonneg t)]
    exact (Work.Stability.chi_le_one t).trans hone
  · intro t
    by_cases ht : t ∈ Set.Icc (-2 : ℝ) 2
    · rw [← Real.norm_eq_abs]
      exact (hM1 t ht).trans hC1
    · rw [chi_deriv_eq_zero_of_two_lt_abs (hout t ht), abs_zero]
      exact zero_le_one.trans hone
  · intro t
    by_cases ht : t ∈ Set.Icc (-2 : ℝ) 2
    · rw [← Real.norm_eq_abs]
      exact (hM2 t ht).trans hC2
    · rw [chi_deriv2_eq_zero_of_two_lt_abs (hout t ht), abs_zero]
      exact zero_le_one.trans hone

/-! ## The moduli -/

theorem chiModuli :
    ∃ C : ℝ, 0 < C ∧
      (∀ x : ℝ, |Work.Stability.chi x| ≤ C) ∧
      (∀ x : ℝ, |deriv Work.Stability.chi x| ≤ C) ∧
      (∀ x : ℝ, |deriv (deriv Work.Stability.chi) x| ≤ C) ∧
      (∀ x y : ℝ, |Work.Stability.chi x - Work.Stability.chi y| ≤ C * |x - y|) ∧
      (∀ x y : ℝ, |deriv Work.Stability.chi x - deriv Work.Stability.chi y| ≤ C * |x - y|) := by
  obtain ⟨C, hCpos, hC0, hC1, hC2⟩ := chi_deriv_bounds
  have hdiff : Differentiable ℝ Work.Stability.chi :=
    (contDiff_infty_iff_deriv.mp (Work.Stability.chi_contDiff : ContDiff ℝ ∞ Work.Stability.chi)).1
  have hdiff1 : Differentiable ℝ (deriv Work.Stability.chi) :=
    (contDiff_infty_iff_deriv.mp
      (contDiff_infty_iff_deriv.mp
        (Work.Stability.chi_contDiff : ContDiff ℝ ∞ Work.Stability.chi)).2).1
  refine ⟨C, hCpos, hC0, hC1, hC2, ?_, ?_⟩
  · -- `χ` is `C`-Lipschitz: its derivative is bounded by `C`
    intro x y
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (s := Set.univ)
      (f := Work.Stability.chi) (C := C) (fun z _ => hdiff z)
      (fun z _ => by rw [Real.norm_eq_abs]; exact hC1 z) convex_univ
      (Set.mem_univ x) (Set.mem_univ y)
    simpa [Real.norm_eq_abs, abs_sub_comm] using h
  · -- `χ'` is `C`-Lipschitz: its derivative is bounded by `C`
    intro x y
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (s := Set.univ)
      (f := deriv Work.Stability.chi) (C := C) (fun z _ => hdiff1 z)
      (fun z _ => by rw [Real.norm_eq_abs]; exact hC2 z) convex_univ
      (Set.mem_univ x) (Set.mem_univ y)
    simpa [Real.norm_eq_abs, abs_sub_comm] using h

end Work.FTS.Regularity
