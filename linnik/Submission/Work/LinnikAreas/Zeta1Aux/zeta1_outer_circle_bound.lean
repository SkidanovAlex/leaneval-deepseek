import Mathlib
import Submission.Work.LinnikAreas.Zeta1Aux.CommonsImports
import Submission.Work.LinnikAreas.Zeta1Aux.zeta1_strip_region_bound
import Submission.Work.LinnikAreas.Zeta1Aux.zeta1_right_halfplane_bound

namespace Work.LinnikAreas.Zeta1Aux

/-!
# Growth of `ζ₁ = (s-1) ζ(s)` on the circle `‖w - (2 + i t)‖ = 4`

This is the "outer circle" bound consumed by the horizontal-vanishing machinery for `ζ₁`:
at height `|t| ≥ 5`, the entire function `riemannZeta₁` is dominated on the circle of
radius `4` about `2 + i t` by `C * (|t| + 9)^13`.

The argument is purely geometric plus two already-proved strip bounds for `ζ`:

* `w ∈ sphere (2 + i t) 4` gives `|Re w - 2| ≤ 4` and `|Im w - t| ≤ 4`, hence
  `-2 ≤ Re w` and `|Im w| ∓ ... `: since `|t| ≥ 5` one gets `1 ≤ |Im w|` (otherwise
  `|t| ≤ |Im w| + 4 < 5`), and `|Im w| + 3 ≤ |t| + 9`.  Also
  `‖w - 1‖ ≤ ‖w - (2 + i t)‖ + ‖1 + i t‖ ≤ 4 + 1 + |t| ≤ |t| + 9`.
* If `3 ≤ Re w`, use `zeta1_right_halfplane_bound`: `‖ζ₁ w‖ ≤ C ‖w - 1‖^13`.
* Otherwise `-2 ≤ Re w ≤ 3` with `|Im w| ≥ 1`, and `zeta1_strip_region_bound` gives
  `‖ζ₁ w‖ ≤ C (|Im w| + 3)^13`.
-/

theorem zeta1_outer_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 5 ≤ |t| →
      ∀ w : ℂ, w ∈ Metric.sphere ((2 : ℂ) + Complex.I * (t : ℂ)) 4 →
        ‖riemannZeta₁ w‖ ≤ C * (|t| + 9) ^ 13 := by
  obtain ⟨Cst, hCst0, hCst⟩ := zeta1_strip_region_bound
  obtain ⟨Cr, hCr0, hCr⟩ := zeta1_right_halfplane_bound
  refine ⟨max Cst Cr, lt_max_of_lt_left hCst0, ?_⟩
  intro t ht w hw
  set c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ) with hcdef
  rw [Metric.mem_sphere, dist_eq_norm] at hw
  -- `hw : ‖w - c‖ = 4`
  have hre_abs : |w.re - 2| ≤ 4 := by
    have h := Complex.abs_re_le_norm (w - c)
    rw [hw] at h
    simpa [hcdef] using h
  have him_abs : |w.im - t| ≤ 4 := by
    have h := Complex.abs_im_le_norm (w - c)
    rw [hw] at h
    simpa [hcdef] using h
  have hre_lo : -2 ≤ w.re := by have h := (abs_le.mp hre_abs).1; linarith
  -- `1 ≤ |Im w|`, because `|t| ≤ |Im w| + 4` and `5 ≤ |t|`.
  have him_lo : 1 ≤ |w.im| := by
    have hdec : w.im + (t - w.im) = t := by ring
    have h1 : |t| ≤ |w.im| + |t - w.im| := by
      calc |t| = |w.im + (t - w.im)| := by rw [hdec]
        _ ≤ |w.im| + |t - w.im| := abs_add_le _ _
    have h2 : |t - w.im| = |w.im - t| := abs_sub_comm t w.im
    rw [h2] at h1
    linarith
  have hw1le : ‖w - 1‖ ≤ |t| + 9 := by
    have hc1 : ‖c - 1‖ ≤ 1 + |t| := by
      have heq : c - 1 = (1 : ℂ) + Complex.I * (t : ℂ) := by rw [hcdef]; ring
      rw [heq]
      calc ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ :=
            norm_add_le _ _
        _ = 1 + |t| := by simp
    have hsum : (w - c) + (c - 1) = w - 1 := by ring
    calc ‖w - 1‖ = ‖(w - c) + (c - 1)‖ := by rw [hsum]
      _ ≤ ‖w - c‖ + ‖c - 1‖ := norm_add_le _ _
      _ ≤ 4 + (1 + |t|) := by rw [hw]; linarith
      _ ≤ |t| + 9 := by linarith
  have htri : |w.im| + 3 ≤ |t| + 9 := by
    have h : |w.im| ≤ |t| + 4 := by
      have hsplit : t + (w.im - t) = w.im := by ring
      calc |w.im| = |t + (w.im - t)| := by rw [hsplit]
        _ ≤ |t| + |w.im - t| := abs_add_le t (w.im - t)
        _ ≤ |t| + 4 := by linarith
    linarith
  by_cases hre : 3 ≤ w.re
  · have hb := hCr w hre
    have hpow : ‖w - 1‖ ^ 13 ≤ (|t| + 9) ^ 13 := pow_le_pow_left₀ (norm_nonneg _) hw1le 13
    calc ‖riemannZeta₁ w‖ ≤ Cr * ‖w - 1‖ ^ 13 := hb
      _ ≤ Cr * (|t| + 9) ^ 13 := mul_le_mul_of_nonneg_left hpow (le_of_lt hCr0)
      _ ≤ max Cst Cr * (|t| + 9) ^ 13 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · have hre3 : w.re ≤ 3 := by linarith
    have hb := hCst w hre_lo hre3 him_lo
    have hpow : (|w.im| + 3) ^ 13 ≤ (|t| + 9) ^ 13 := pow_le_pow_left₀ (by positivity) htri 13
    calc ‖riemannZeta₁ w‖ ≤ Cst * (|w.im| + 3) ^ 13 := hb
      _ ≤ Cst * (|t| + 9) ^ 13 := mul_le_mul_of_nonneg_left hpow (le_of_lt hCst0)
      _ ≤ max Cst Cr * (|t| + 9) ^ 13 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end Work.LinnikAreas.Zeta1Aux
