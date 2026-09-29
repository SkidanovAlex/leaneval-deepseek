import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.uhCoeff_bound

/-!
# A14D — the power series of `uhCoeff` sums to `uh (1 - z)` on `‖z‖ < 8/9`

`uh (1 - z) = Σₙ aₙ zⁿ` (`a = uhCoeff`), so the announced statement is that the power series
`Σ aₙ zⁿ` has sum `uh (1 - z)`.  Since `uh` is *defined* as a `tsum`, the content is that the
series is summable on the disc `‖z‖ < 8/9`; this is exactly the radius of convergence that the
geometric bound `a_{n+1} ≤ 9/8 · a_n` of `Submission.Work.A14D.uhCoeff_bound` provides.
-/

open Complex Metric Filter
open scoped Topology BigOperators

namespace Work.A14D

/-- Geometric upper bound for the coefficients, in `ℚ`. -/
private lemma uhCoeff_geom_Q (n : ℕ) : uhCoeff n ≤ (9 / 8 : ℚ) ^ n := by
  induction n with
  | zero => norm_num [uhCoeff]
  | succ n ih =>
    calc uhCoeff (n + 1) ≤ 9 / 8 * uhCoeff n := (uhCoeff_bound.2.1) n
      _ ≤ 9 / 8 * (9 / 8 : ℚ) ^ n := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (9 / 8 : ℚ) ^ (n + 1) := by ring

/-- Geometric upper bound for the coefficients, in `ℝ`. -/
private lemma uhCoeff_geom (n : ℕ) : (uhCoeff n : ℝ) ≤ (9 / 8 : ℝ) ^ n := by
  have := uhCoeff_geom_Q n
  have h : ((uhCoeff n : ℚ) : ℝ) ≤ (((9 / 8 : ℚ) ^ n : ℚ) : ℝ) := by exact_mod_cast this
  rw [Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofNat] at h
  norm_num at h
  exact h

/-- The norm of the (positive) coefficient, viewed in `ℂ`. -/
private lemma norm_uhCoeff (n : ℕ) : ‖(uhCoeff n : ℂ)‖ = (uhCoeff n : ℝ) := by
  rw [← Complex.ofReal_ratCast]
  have h2 : ‖(((uhCoeff n : ℝ)) : ℂ)‖ ^ 2 = |(uhCoeff n : ℝ)| ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq_abs]; ring
  have hpos : (0 : ℝ) ≤ (uhCoeff n : ℝ) := by
    have := (uhCoeff_bound.1 n); exact_mod_cast le_of_lt this
  rw [abs_of_nonneg hpos] at h2
  nlinarith [norm_nonneg (((uhCoeff n : ℝ)) : ℂ)]

/-- The coefficient series `Σ aₙ zⁿ` is summable on the disc `‖z‖ < 8/9`. -/
private lemma summable_uh (z : ℂ) (hz : ‖z‖ < 8 / 9) :
    Summable (fun n : ℕ => (uhCoeff n : ℂ) * z ^ n) := by
  have hz9 : (9 / 8 : ℝ) * ‖z‖ < 1 := by
    have h : (9 / 8 : ℝ) * (8 / 9) = 1 := by norm_num
    calc (9 / 8 : ℝ) * ‖z‖ < 9 / 8 * (8 / 9) := mul_lt_mul_of_pos_left hz (by norm_num)
      _ = 1 := h
  have hgeo : Summable (fun n : ℕ => ((9 / 8 : ℝ) * ‖z‖) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hz9
  refine Summable.of_norm_bounded hgeo (fun n => ?_)
  rw [norm_mul, norm_pow, norm_uhCoeff]
  calc (uhCoeff n : ℝ) * ‖z‖ ^ n ≤ (9 / 8 : ℝ) ^ n * ‖z‖ ^ n :=
        mul_le_mul_of_nonneg_right (uhCoeff_geom n) (by positivity)
    _ = ((9 / 8 : ℝ) * ‖z‖) ^ n := by rw [mul_pow]

theorem uh_hasSum (z : ℂ) (hz : ‖z‖ < 8 / 9) :
    HasSum (fun n : ℕ => (uhCoeff n : ℂ) * z ^ n) (uh (1 - z)) := by
  have h := (summable_uh z hz).hasSum
  have heq : uh (1 - z) = ∑' n : ℕ, (uhCoeff n : ℂ) * z ^ n := by
    unfold uh
    simp only [sub_sub_cancel]
  rw [heq]
  exact h

end Work.A14D
