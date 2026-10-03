import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# Budget transfer for the coordinate `τ₀(w) = -1/w`

`MandelDim.tau0 w = -1/w` is an involution of `ℂ \ {0}`.  This file records the elementary
"budget" transfer: if `τ₀ y` is within `η/80` of a point `w` of size `≈ η` (precisely
`7η/10 ≤ ‖w‖ ≤ 13η/10`), and `x` is within `ε` of `y` with `ε` so small that `6η²ε ≤ η/560`,
then `τ₀ x` is within `η/70` of `w`, and `‖x‖ ≥ 1/(3η)`.

The whole content is the explicit Lipschitz estimate
`‖τ₀ x - τ₀ y‖ = ‖x - y‖ / (‖x‖·‖y‖)`
combined with the two-sided bounds on `‖y‖` forced by `hA`:

* `11η/16 ≤ ‖τ₀ y‖ ≤ 21η/16`, i.e. `16/(21η) ≤ ‖y‖ ≤ 16/(11η)`;
* hence `‖x‖ ≥ 16/(21η) - 1/(3360η) ≥ 1/(3η)`, so `1/‖x‖ ≤ 3η`, `1/‖y‖ ≤ 21η/16`;
* `‖τ₀ x - τ₀ y‖ < ε·3η·(21η/16) = 63η²ε/16 ≤ 3η/2560`
  (using `ε ≤ 1/(3360η)`, which is exactly `6η²ε ≤ η/560`);
* and finally `3η/2560 + η/80 ≤ η/70`, since `3/2560 + 1/80 = 35/2560 < 1/70`.

The constants are exactly the ones supplied; the auxiliary hypothesis `hε1 : 6ηε ≤ 1` is
not needed for the estimate (it is implied by `hε2` when `η ≤ 560`).
-/

namespace Work.Pert

set_option linter.unusedVariables false

theorem tau0_approx_transfer_budget {x y w : ℂ} {η ε : ℝ} (hη : 0 < η)
    (hwlo : 7 * η / 10 ≤ ‖w‖) (hwhi : ‖w‖ ≤ 13 * η / 10)
    (hA : ‖MandelDim.tau0 y - w‖ ≤ η / 80)
    (hε : ‖x - y‖ < ε) (hε1 : 6 * η * ε ≤ 1) (hε2 : 6 * η ^ 2 * ε ≤ η / 560) :
    ‖x‖ ≥ 1 / (3 * η) ∧ ‖MandelDim.tau0 x - w‖ ≤ η / 70 := by
  -- `τ₀` is inversion up to sign, hence `‖τ₀ z‖ = 1/‖z‖`.
  have hnorm_tau0 : ∀ z : ℂ, ‖MandelDim.tau0 z‖ = 1 / ‖z‖ := by
    intro z
    rw [MandelDim.tau0, norm_div, norm_neg, norm_one]
  -- `hA` forces `y ≠ 0` (otherwise `τ₀ y = 0` and `‖w‖ ≤ η/80 < 7η/10`).
  have hy_ne : y ≠ 0 := by
    intro hy
    subst hy
    have hw0 : ‖w‖ ≤ η / 80 := by simpa [MandelDim.tau0] using hA
    nlinarith [hwlo, hw0, hη]
  -- Upper bound for `‖τ₀ y‖`.
  have h1 : ‖MandelDim.tau0 y‖ ≤ 21 * η / 16 := by
    have h' : MandelDim.tau0 y - w + w = MandelDim.tau0 y := by ring
    have h := norm_add_le (MandelDim.tau0 y - w) w
    rw [h'] at h
    linarith [h, hA, hwhi]
  -- Lower bound for `‖τ₀ y‖` (in particular nonzero, so `‖y‖ < ∞` strictly).
  have h2 : 11 * η / 16 ≤ ‖MandelDim.tau0 y‖ := by
    have h' : w - MandelDim.tau0 y + MandelDim.tau0 y = w := by ring
    have h := norm_add_le (w - MandelDim.tau0 y) (MandelDim.tau0 y)
    rw [h'] at h
    rw [norm_sub_rev] at h
    linarith [h, hA, hwlo]
  have h3 : 1 / ‖y‖ ≤ 21 * η / 16 := by rw [← hnorm_tau0 y]; exact h1
  have h4 : 11 * η / 16 ≤ 1 / ‖y‖ := by rw [← hnorm_tau0 y]; exact h2
  have hyinv_pos : (0 : ℝ) < 1 / ‖y‖ := lt_of_lt_of_le (by positivity) h4
  -- `16/(21η) ≤ ‖y‖`.
  have h5 : 16 / (21 * η) ≤ ‖y‖ := by
    have h := one_div_le_one_div_of_le hyinv_pos h3
    have e1 : 1 / (21 * η / 16) = 16 / (21 * η) := by field_simp
    have e2 : 1 / (1 / ‖y‖) = ‖y‖ := by field_simp
    rwa [e1, e2] at h
  have hypos : (0 : ℝ) < ‖y‖ := by
    have : (0 : ℝ) < 16 / (21 * η) := by positivity
    linarith
  -- `hε2` is exactly `ε ≤ 1/(3360η)`.
  have hε' : ε ≤ 1 / (3360 * η) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 3360 * η)]
    nlinarith [hε2, hη]
  have h6 : ‖x - y‖ < 1 / (3360 * η) := lt_of_lt_of_le hε hε'
  -- Reverse triangle inequality: `‖x‖ > 16/(21η) - 1/(3360η)`.
  have hx_aux : 16 / (21 * η) - 1 / (3360 * η) < ‖x‖ := by
    have h' : y - x + x = y := by ring
    have h := norm_add_le (y - x) x
    rw [h'] at h
    rw [norm_sub_rev] at h
    linarith [h, h5, h6]
  have hnum : 1 / (3 * η) ≤ 16 / (21 * η) - 1 / (3360 * η) := by
    have hc : (1 : ℝ) / 3 ≤ 16 / 21 - 1 / 3360 := by norm_num
    have hpos : (0 : ℝ) < 1 / η := by positivity
    have h := mul_le_mul_of_nonneg_left hc (le_of_lt hpos)
    rw [show 1 / (3 * η) = (1 / η) * (1 / 3) from by field_simp,
        show 16 / (21 * η) - 1 / (3360 * η) = (1 / η) * (16 / 21 - 1 / 3360) from by field_simp]
    exact h
  have hx_lower : 1 / (3 * η) ≤ ‖x‖ := by linarith [hnum, hx_aux]
  have hx_ne : x ≠ 0 := by
    intro hx0
    rw [hx0, norm_zero] at hx_lower
    have : (0 : ℝ) < 1 / (3 * η) := by positivity
    linarith
  have hxpos : (0 : ℝ) < ‖x‖ := by
    have : (0 : ℝ) < 1 / (3 * η) := by positivity
    linarith
  -- The explicit Lipschitz identity for the inversion.
  have hdist : ‖MandelDim.tau0 x - MandelDim.tau0 y‖ = ‖x - y‖ / (‖x‖ * ‖y‖) := by
    rw [show MandelDim.tau0 x = -(x⁻¹) from by rw [MandelDim.tau0, div_eq_mul_inv, neg_one_mul],
        show MandelDim.tau0 y = -(y⁻¹) from by rw [MandelDim.tau0, div_eq_mul_inv, neg_one_mul]]
    rw [← dist_eq_norm, dist_neg_neg, dist_inv_inv₀ hx_ne hy_ne, dist_eq_norm]
  have hxinv : 1 / ‖x‖ ≤ 3 * η := by
    have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1 / (3 * η)) hx_lower
    have e : 1 / (1 / (3 * η)) = 3 * η := by field_simp
    rwa [e] at h
  -- The core estimate, cleared of denominators: `2560‖x-y‖ < 3η‖x‖‖y‖`.
  have hbig : 2560 * ‖x - y‖ < 3 * η * (‖x‖ * ‖y‖) := by
    have hA1 : 2560 * ‖x - y‖ < 2560 * (1 / (3360 * η)) := by
      have h := mul_lt_mul_of_pos_left h6 (by norm_num : (0 : ℝ) < 2560)
      linarith [h]
    have hA2 : (2560 : ℝ) * (1 / (3360 * η)) = 16 / (21 * η) := by field_simp; ring
    have hB1 : 3 * η * (‖x‖ * ‖y‖) ≥ 3 * η * ((1 / (3 * η)) * (16 / (21 * η))) := by
      have h := mul_le_mul hx_lower h5 (by positivity : (0 : ℝ) ≤ 16 / (21 * η)) (le_of_lt hxpos)
      have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 3 * η)
      linarith [h2]
    have hB2 : 3 * η * ((1 / (3 * η)) * (16 / (21 * η))) = 16 / (21 * η) := by field_simp
    linarith [hA1, hB1, hA2, hB2]
  have ht : ‖MandelDim.tau0 x - MandelDim.tau0 y‖ < 3 * η / 2560 := by
    rw [hdist, div_lt_iff₀ (mul_pos hxpos hypos)]
    linarith [hbig]
  -- Budget: `3η/2560 + η/80 ≤ η/70`.
  have hbudget : 3 * η / 2560 + η / 80 ≤ η / 70 := by
    have hc : (3 : ℝ) / 2560 + 1 / 80 ≤ 1 / 70 := by norm_num
    have h := mul_le_mul_of_nonneg_left hc (le_of_lt hη)
    linarith [h]
  have h' : MandelDim.tau0 x - MandelDim.tau0 y + (MandelDim.tau0 y - w) = MandelDim.tau0 x - w :=
    by ring
  have h := norm_add_le (MandelDim.tau0 x - MandelDim.tau0 y) (MandelDim.tau0 y - w)
  rw [h'] at h
  exact ⟨hx_lower, by linarith [h, hA, ht, hbudget]⟩

end Work.Pert
