import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.sigma_le_norm_alpha
import Submission.Work.Pert.tauC_denom_lower_global
import Submission.Work.Pert.tauC_exp_one_of_iInf_eq_zero

/-!
# PERT · `Work.Pert.tauC_norm_le_sharp`

The *sharp* pointwise bound for the universal cover `τ_f = tauC σ α` of (A.1.5), valid on all of
`ℂ` (no gate hypothesis):

  `∀ z, ‖τ_f z‖ ≤ 2^8 ‖α‖ / min 1 (2 ‖α‖ · d)`,  `d = dist (z, ℤ/α)`.

The right-hand side is `2^8 ‖α‖` when `2 ‖α‖ d ≥ 1` and `128/d` when `2‖α‖ d ≤ 1`; in both
regimes it is a bound of the expected size, because the normalisation
`1 - σ u₀ = exp (2πi α)` forces `‖σ‖ ≤ 32 ‖α‖` (`Work.Pert.sigma_le_norm_alpha`), so numerator and
denominator of `τ_f` are both of size `‖α‖` near the lattice.

Three inputs:

* **normalisation bound** `‖σ‖ ≤ 32 ‖α‖`, from `σ u₀ = 1 - exp (2πi α)`, `‖u₀‖ ≥ 1/2`,
  `‖α‖ ≤ 1/64`;
* **lattice lower bound for the denominator** (`Work.Pert.tauC_denom_lower_global`, a corollary of
  `norm_one_sub_exp_two_pi_I_mul_ge`): `(3/4) min 1 (‖α‖ d) ≤ ‖1 - exp (-2πi α z)‖` when `d > 0`;
* **degenerate case** (`Work.Pert.tauC_exp_one_of_iInf_eq_zero`): if `α ≠ 0` and `d = 0` then
  `z ∈ ℤ/α` is a pole of `τ_f`, hence `exp (-2πi α z) = 1`, the denominator vanishes and `τ_f z = 0`.

The remaining steps are the elementary arithmetic comparison
`32 ‖α‖ / ((3/4) min 1 u) ≤ 2^8 ‖α‖ / min 1 (2u)` and the case `α = 0` (where `τ_f ≡ 0`).
-/

namespace Work.Pert

open MandelDim Complex

noncomputable section

set_option linter.unusedVariables false

/-- Elementary real comparison.  For `A ≥ 0` and `u ≥ 0`,

`32 A / ((3/4) min 1 u) ≤ 2^8 A / min 1 (2u)`.

For `u ≤ 1/2` both minima are the linear term and the claim is `128/3 ≤ 128`; for `u ≥ 1/2` the
right minimum is `1` while the left one is `≥ 1/2`, and `32/((3/4)(1/2)) = 256/3 ≤ 256`. -/
private lemma arith_sharp {A u : ℝ} (hA : 0 ≤ A) (hu : 0 ≤ u) :
    32 * A / ((3 / 4) * min 1 u) ≤ 2 ^ 8 * A / min 1 (2 * u) := by
  rcases eq_or_lt_of_le hu with h0 | hu0
  · subst h0; norm_num
  · have hmpos : 0 < min 1 u := lt_min one_pos hu0
    by_cases hu2 : u ≤ 1/2
    · have hu1 : u ≤ 1 := by linarith
      rw [min_eq_right hu1, min_eq_right (by linarith : 2 * u ≤ 1)]
      have e1 : 32 * A / ((3 / 4) * u) = 128 * A / (3 * u) := by field_simp; ring
      have e2 : 2 ^ 8 * A / (2 * u) = 128 * A / u := by norm_num; field_simp; ring
      rw [e1, e2]
      exact div_le_div_of_nonneg_left (by linarith) hu0 (by linarith)
    · have h1 : (1 : ℝ) ≤ 2 * u := by linarith
      rw [min_eq_left h1, div_one]
      have hm : (1/2 : ℝ) ≤ min 1 u := le_min (by norm_num) (by linarith)
      have hval : 32 * A / ((3 / 4) * (1/2)) = 256 * A / 3 := by norm_num; field_simp; ring
      calc 32 * A / ((3 / 4) * min 1 u) ≤ 32 * A / ((3 / 4) * (1/2)) :=
            div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
        _ = 256 * A / 3 := hval
        _ ≤ 2 ^ 8 * A := by norm_num; linarith

theorem tauC_norm_le_sharp {rr : ℝ} {α σ : ℂ} {u : ℂ → ℂ}
    (hrr : 0 < rr) (hα64 : ‖α‖ ≤ 1 / 64) (hσ : σ ≠ 0)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) :
    ∀ z : ℂ,
      ‖Work.Pert.tauC σ α z‖
        ≤ 2 ^ 8 * ‖α‖
            / min 1 (2 * ‖α‖ * (⨅ k : ℤ, dist z ((k : ℂ) / α))) := by
  have hσb : ‖σ‖ ≤ 32 * ‖α‖ :=
    sigma_le_norm_alpha hα64 (hu2 0 (Metric.mem_ball_self hrr)).1 hnorm
  intro z
  rcases eq_or_ne α 0 with hα0 | hα0
  · -- `α = 0`: `τ_f ≡ 0` (the denominator `1 - exp 0` vanishes), and so does the right-hand side
    subst hα0
    simp [Work.Pert.tauC]
  · have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα0
    set d : ℝ := ⨅ k : ℤ, dist z ((k : ℂ) / α) with hd
    have hdnn : 0 ≤ d := by rw [hd]; exact le_ciInf (fun k => dist_nonneg)
    rcases lt_or_ge (0:ℝ) (‖α‖ * d) with hz | hz
    · -- non-degenerate case: the denominator is bounded below by `(3/4) min 1 (‖α‖ d)`
      have hDge : (3 / 4) * min 1 (‖α‖ * d)
          ≤ ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * z))‖ := by
        have h := tauC_denom_lower_global hα0 (by rw [← hd]; exact hz)
        rwa [← hd] at h
      have hdenpos : 0 < (3 / 4) * min 1 (‖α‖ * d) := by
        have : 0 < min 1 (‖α‖ * d) := lt_min one_pos hz
        linarith
      calc ‖Work.Pert.tauC σ α z‖
          = ‖σ‖ / ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * z))‖ := by
            rw [Work.Pert.tauC, norm_div]
        _ ≤ ‖σ‖ / ((3 / 4) * min 1 (‖α‖ * d)) :=
            div_le_div_of_nonneg_left (norm_nonneg σ) hdenpos hDge
        _ ≤ 32 * ‖α‖ / ((3 / 4) * min 1 (‖α‖ * d)) :=
            div_le_div_of_nonneg_right hσb (by linarith)
        _ ≤ 2 ^ 8 * ‖α‖ / min 1 (2 * (‖α‖ * d)) :=
            arith_sharp (norm_nonneg α) (mul_nonneg (norm_nonneg α) hdnn)
        _ = 2 ^ 8 * ‖α‖ / min 1 (2 * ‖α‖ * d) := by
            rw [show 2 * (‖α‖ * d) = 2 * ‖α‖ * d by ring]
    · -- degenerate case `‖α‖ d = 0`, i.e. `d = 0` (`α ≠ 0`): `z` is a pole of `τ_f`
      have hz0 : ‖α‖ * d = 0 := le_antisymm hz (mul_nonneg (norm_nonneg α) hdnn)
      have hdeq : d = 0 := by
        rcases mul_eq_zero.mp hz0 with h | h
        · exact absurd h hαpos.ne'
        · exact h
      have he : Complex.exp (-(2 * Real.pi * Complex.I * α * z)) = 1 :=
        tauC_exp_one_of_iInf_eq_zero hα0 (by rw [← hd]; exact hdeq)
      have htau : Work.Pert.tauC σ α z = 0 := by
        rw [Work.Pert.tauC, he, sub_self, div_zero]
      rw [htau, norm_zero, hdeq]
      norm_num

end

end Work.Pert
