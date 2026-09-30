import Mathlib
import Submission.Work.BMF.parseval.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Norm bounds for the truncated Perron kernel `Φ(t,u)`

We prove the two elementary size estimates for
`Phi t u = ((1+u)^{1+it} - 1)/(1+it)` that are used to control the single-window
Perron integral:

* `‖Phi t u‖ ≤ u` for `u ≥ 0`: the kernel is the average `u⁻¹ ∫₀^u (1+s)^{it} ds`
  of unimodular numbers, i.e. `Phi t u = u · Theta u t` with `‖Theta u t‖ ≤ 1`
  (lemma `theta_norm_le_one` of `delta_bounds`);
* `‖Phi t u‖ ≤ 8/(1+|t|)` for `0 ≤ u ≤ 3`: the triangle inequality gives
  `‖Phi t u‖ ≤ (2+u)/√(1+t²) ≤ 5/√(1+t²)`, and `8√(1+t²) ≥ 5(1+|t|)`.

The file builds only on `Submission.Work.BMF.parseval.Defs` (which supplies the
definition of `Phi`, the identity `Phi_eq_mul_Theta`, `Phi_zero` and the bound
`theta_norm_le_one`).
-/

namespace Work.BMF

/-- The elementary real inequality `5(1+|t|) ≤ 8√(1+t²)`.

Squaring, this is `25(1+|t|)² ≤ 64(1+t²)`, which follows from `2|t| ≤ 1+t²`
(the arithmetic–geometric mean inequality) since
`25(1+|t|)² ≤ 50(1+t²) ≤ 64(1+t²)`. -/
lemma five_mul_one_add_abs_le_eight_sqrt (t : ℝ) :
    5 * (1 + |t|) ≤ 8 * Real.sqrt (1 + t ^ 2) := by
  have h64 : (8:ℝ) * Real.sqrt (1 + t^2) = Real.sqrt (64 * (1 + t^2)) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 64)]
    norm_num
  rw [h64, Real.le_sqrt (by positivity) (by positivity)]
  nlinarith [sq_abs t, sq_nonneg (|t| - 1), abs_nonneg t]

/-- Decay bound for `Phi`: for `0 ≤ u ≤ 3` and every real `t`,
`‖Phi t u‖ ≤ 8/(1+|t|)`. -/
lemma Phi_norm_le_abs (t u : ℝ) (hu : 0 ≤ u) (hu3 : u ≤ 3) :
    ‖Phi t u‖ ≤ 8 / (1 + |t|) := by
  have h1u : (0:ℝ) < 1 + u := by linarith
  -- the numerator `(1+u)^{1+it}` has modulus `1+u`
  have hA : ‖((1+u:ℝ):ℂ)^(1 + Complex.I*(t:ℂ))‖ = 1 + u := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos h1u]
    have hre : (1 + Complex.I*(t:ℂ)).re = 1 := by simp [Complex.mul_re]
    rw [hre, Real.rpow_one]
  -- the denominator `1+it` has modulus `√(1+t²)`
  have hden : ‖(1:ℂ) + Complex.I*(t:ℂ)‖ = Real.sqrt (1 + t^2) := by
    simpa [mul_comm] using Complex.norm_add_mul_I 1 t
  have hnum : ‖((1+u:ℝ):ℂ)^(1+Complex.I*(t:ℂ)) - 1‖ ≤ 5 := by
    calc ‖((1+u:ℝ):ℂ)^(1+Complex.I*(t:ℂ)) - 1‖
        ≤ ‖((1+u:ℝ):ℂ)^(1+Complex.I*(t:ℂ))‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = (1+u) + 1 := by rw [hA]; simp
      _ ≤ 5 := by linarith
  rw [Phi, norm_div, hden]
  have hs : 0 < Real.sqrt (1 + t^2) := Real.sqrt_pos_of_pos (by positivity)
  have hd : 0 < 1 + |t| := by positivity
  calc ‖((1+u:ℝ):ℂ)^(1+Complex.I*(t:ℂ)) - 1‖ / Real.sqrt (1 + t^2)
      ≤ 5 / Real.sqrt (1 + t^2) := div_le_div_of_nonneg_right hnum hs.le
    _ ≤ 8 / (1 + |t|) := by
        rw [div_le_div_iff₀ hs hd]
        exact five_mul_one_add_abs_le_eight_sqrt t

theorem Phi_norm_bounds :
    (∀ t u : ℝ, 0 ≤ u → ‖Phi t u‖ ≤ u) ∧
    (∀ t u : ℝ, 0 ≤ u → u ≤ 3 → ‖Phi t u‖ ≤ 8 / (1 + |t|)) := by
  refine ⟨?_, Phi_norm_le_abs⟩
  intro t u hu
  rcases lt_or_eq_of_le hu with h | h
  · -- `Phi t u = u · Theta u t` and `‖Theta u t‖ ≤ 1`
    rw [Phi_eq_mul_Theta, norm_mul]
    have hu' : ‖(u:ℂ)‖ = u := by simp [abs_of_nonneg hu]
    rw [hu']
    calc u * ‖Theta u t‖ ≤ u * 1 := mul_le_mul_of_nonneg_left (theta_norm_le_one u t h) hu
      _ = u := by ring
  · rw [← h, Phi_zero]; simp

end Work.BMF
